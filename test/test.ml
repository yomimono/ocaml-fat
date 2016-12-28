(*
 * Copyright (C) 2013 Citrix Systems Inc
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open OUnit
open Lwt.Infix
open Block
open Result
open Mirage_fs

module MemFS = Fat.FS(Mirage_block_lwt.Mem)

let fail fmt = Fmt.kstrf Lwt.fail_with fmt

let (>>*=) m f = m >>= function
  | Error e -> fail "%a" MemFS.pp_write_error (e :> MemFS.write_error)
  | Ok x    -> f x

let alloc bytes =
  let pages = Io_page.(to_cstruct (get ((bytes + 4095) / 4096))) in
  Cstruct.sub pages 0 bytes

let read_sector filename =
  Lwt_unix.openfile filename [ Lwt_unix.O_RDONLY ] 0o0 >>= fun fd ->
  let buf = alloc 512 in
  really_read fd buf >>= fun () ->
  Lwt_unix.close fd >|= fun () ->
  buf

let read_whole_file filename =
  Lwt_unix.openfile filename [ Lwt_unix.O_RDONLY ] 0o0 >>= fun fd ->
  let size = (Unix.stat filename).Unix.st_size in
  let buf = alloc size in
  really_read fd buf >>= fun () ->
  Lwt_unix.close fd >|= fun () ->
  buf

let checksum_test () =
  let open Fat_name in
  let checksum_tests = [
    make "MAKEFILE", 193;
    make "FAT.ML", 223;
  ] in
  List.iter (fun (d, expected) ->
      let d = snd d.dos in
      let checksum = compute_checksum d in
      assert_equal ~printer:string_of_int expected checksum
    ) checksum_tests

let print_int_list xs = "[" ^ ( String.concat "; " (List.map string_of_int xs) ) ^ "]"

let test_root_list () =
  let open Fat_name in
  let t =
    read_whole_file "test/root.dat" >>= fun bytes ->
    let all = list bytes in
    assert_equal ~printer:string_of_int 5 (List.length all);
    let x = List.nth all 1 in
    let utf_filename =
      "l\000o\000w\000e\000r\000.\000t\000x\000t\000\000\000\255\255\255\255\255\255"
    in
    assert_equal ~printer:(fun x -> x) utf_filename x.utf_filename;
    let a, b = x.dos in
    assert_equal ~printer:string_of_int 192 a;
    assert_equal ~printer:(fun x -> x) "LOWER" b.filename;
    assert_equal ~printer:(fun x -> x) "TXT" b.ext;
    assert_equal ~printer:string_of_bool false b.deleted;
    assert_equal ~printer:string_of_bool false b.read_only;
    assert_equal ~printer:string_of_bool false b.hidden;
    assert_equal ~printer:string_of_bool false b.system;
    assert_equal ~printer:string_of_bool false b.volume;
    assert_equal ~printer:string_of_bool false b.subdir;
    assert_equal ~printer:string_of_bool true b.archive;
    assert_equal ~printer:string_of_int 0 b.start_cluster;
    assert_equal ~printer:Int32.to_string 0l b.file_size;
    assert_equal ~printer:string_of_int 2013 b.create.year;
    assert_equal ~printer:string_of_int 11 b.create.month;
    assert_equal ~printer:string_of_int 2 b.create.day;
    assert_equal ~printer:string_of_int 16 b.create.hours;
    assert_equal ~printer:string_of_int 58 b.create.mins;
    assert_equal ~printer:string_of_int 52 b.create.secs;
    assert_equal ~printer:string_of_int 100 b.create.ms;
    let lfns = x.lfns in
    assert_equal ~printer:string_of_int 1 (List.length lfns);
    let a, b = List.hd lfns in
    assert_equal ~printer:string_of_int 160 a;
    assert_equal ~printer:string_of_bool false b.lfn_deleted;
    assert_equal ~printer:string_of_bool true b.lfn_last;
    assert_equal ~printer:string_of_int 1 b.lfn_seq;
    assert_equal ~printer:string_of_int 252 b.lfn_checksum;
    assert_equal ~printer:(fun x -> x) utf_filename b.lfn_utf16_name;
    Lwt.return ()
  in
  Lwt_main.run t

let test_chains () =
  let t =
    let open Fat_boot_sector in
    read_sector "test/bootsector.dat" >>= fun bytes ->
    let boot = match unmarshal bytes with
      | Error x -> failwith x
      | Ok x -> x in
    let printer = function
      | Error e -> e
      | Ok x -> Fat_format.to_string x in
    assert_equal ~printer
      (Ok Fat_format.FAT16) (Fat_boot_sector.detect_format boot);
    read_whole_file "test/root.dat" >>= fun bytes ->
    let open Fat_name in
    let all = list bytes in
    read_whole_file "test/fat.dat" >>= fun fat ->

    let expected = [0; 0; 0; 2235; 3] in
    let actual = List.map (fun x -> (snd (x.dos)).start_cluster) all in
    assert_equal ~printer:print_int_list expected actual;
    assert_equal ~printer:print_int_list []
      (Fat_entry.Chain.follow Fat_format.FAT16 fat 0);

    assert_equal ~printer:print_int_list [2235]
      (Fat_entry.Chain.follow Fat_format.FAT16 fat 2235);
    let rec ints last x = if x = last then [x] else x :: (ints last (x + 1)) in
    let expected = ints 2234 3 in
    assert_equal ~printer:print_int_list expected
      (Fat_entry.Chain.follow Fat_format.FAT16 fat 3);
    Lwt.return ()
  in
  Lwt_main.run t

let test_parse_boot_sector () =
  let t =
    let open Fat_boot_sector in
    read_sector "test/bootsector.dat" >>= fun bytes ->
    let x = match unmarshal bytes with
      | Error x -> failwith x
      | Ok x -> x in
    let check x =
      assert_equal ~printer:(fun x -> x) "mkdosfs\000" x.oem_name;
      assert_equal ~printer:string_of_int 512 x.bytes_per_sector;
      assert_equal ~printer:string_of_int 4 x.sectors_per_cluster;
      assert_equal ~printer:string_of_int 4 x.reserved_sectors;
      assert_equal ~printer:string_of_int 2 x.number_of_fats;
      assert_equal ~printer:string_of_int 512 x.number_of_root_dir_entries;
      assert_equal ~printer:Int32.to_string 30720l x.total_sectors;
      assert_equal ~printer:string_of_int 32 x.sectors_per_fat;
      assert_equal ~printer:Int32.to_string 0l x.hidden_preceeding_sectors;
      let sectors_of_fat =
        [4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21;
         22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35]
      in
      let sectors_of_root_dir =
        [68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84;
         85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99]
      in
      assert_equal ~printer:print_int_list sectors_of_fat
        (Fat_boot_sector.sectors_of_fat x);
      assert_equal ~printer:print_int_list sectors_of_root_dir
        (Fat_boot_sector.sectors_of_root_dir x) in
    check x;
    let buf = alloc sizeof in
    marshal buf x;
    let x = match unmarshal buf with
      | Error x -> failwith x
      | Ok x -> x in
    check x;
    Lwt.return ()
  in
  Lwt_main.run t

let kib = 1024L
let mib = Int64.mul kib 1024L

module FsError = struct
  let (>>=) x f = x >>= function
    | `Ok x -> f x
    | `Error error ->
      let b = Buffer.create 20 in
      let ppf = Format.formatter_of_buffer b in
      let k ppf = Format.pp_print_flush ppf (); fail "%s" (Buffer.contents b) in
      Fmt.kpf k ppf "%a" Mirage_pp.pp_fs_write_error error
end

let test_create () =
  let t =
    MemFS.format "" (Int64.mul 16L mib) >>*= fun fs ->
    let filename = "HELLO.TXT" in
    MemFS.create fs filename >>*= fun () ->
    MemFS.stat fs "/" >>*= function
    | { MemFS.directory = true; _ } ->
      let file = "/" in
      MemFS.listdir fs file >>*= fun names ->
      assert_equal ~printer:(String.concat "; ") [ filename ] names;
      Lwt.return ()
    | { MemFS.directory = false; _ } ->
      fail "Not a directory"
  in
  Lwt_main.run t

exception Cstruct_differ

let cstruct_equal a b =
  let check_contents a b =
    try
      for i = 0 to Cstruct.len a - 1 do
        let a' = Cstruct.get_char a i in
        let b' = Cstruct.get_char b i in
        if a' <> b' then raise Cstruct_differ
      done;
      true
    with _ -> false in
  (Cstruct.len a = (Cstruct.len b)) && (check_contents a b)

let make_pattern tag length =
  (* if the tag is smaller than length then truncate it *)
  let tag = if String.length tag > length then String.sub tag 0 length else tag in
  assert (String.length tag <= length);
  let buffer = alloc length in
  Cstruct.blit_from_string tag 0 buffer 0 (String.length tag);
  for i = String.length tag to Cstruct.len buffer - 1 do
    Cstruct.set_char buffer i tag.[i mod (String.length tag)]
  done;
  buffer

let sector_aligned_writes = [
  0, 512;
  512, 512;
  4096, 512;
]

let sector_misaligned_writes = [
  1, 1;
  512, 1;
  256, 512;
]

let interesting_writes = sector_aligned_writes @ sector_misaligned_writes

let interesting_filenames = [
  "HELLO.TXT";
  "/FOO/BAR.TXT";
]

let test_listdir () =
  let t =
    MemFS.format "" (Int64.mul 16L mib) >>*= fun fs ->
    let filename = "hello" in
    MemFS.create fs filename >>*= fun () ->
    MemFS.listdir fs "/" >>*= fun all ->
    if List.mem filename all
    then Lwt.return ()
    else fail "Looking for '%s' in directory, contents [ %s ]" filename
        (String.concat ", " (List.map (fun x ->
             Printf.sprintf "'%s'(%d)" x (String.length x)) all))
  in
  Lwt_main.run t

let test_listdir_subdir () =
  let t =
    MemFS.format "" (Int64.mul 16L mib) >>*= fun fs ->
    let dirname = "hello" in
    MemFS.mkdir fs dirname >>*= fun () ->
    MemFS.listdir fs "/" >>*= fun all ->
    ( if List.mem dirname all
      then Lwt.return ()
      else fail "Looking for '%s' in / directory, contents [ %s ]" dirname
          (String.concat ", " (List.map (fun x ->
               Printf.sprintf "'%s'(%d)" x (String.length x)) all)))
    >>= fun () ->
    let filename = "there" in
    let path = Filename.concat dirname filename in
    MemFS.create fs path >>*= fun () ->
    MemFS.listdir fs dirname >>*= fun all ->
    ( if List.mem filename all
      then Lwt.return ()
      else fail "Looking for '%s' in %s directory, contents [ %s ]"
          filename dirname
          (String.concat ", " (List.map (fun x ->
               Printf.sprintf "'%s'(%d)" x (String.length x)) all)))
  in
  Lwt_main.run t

let test_read () =
  let t =
    MemFS.format "" (Int64.mul 16L mib) >>*= fun fs ->
    let filename = "hello" in
    let length = 512 in
    MemFS.create fs filename >>*= fun () ->
    let buffer = make_pattern "basic writing test " length in
    MemFS.write fs filename 0 buffer >>*= fun () ->
    MemFS.read fs filename 0 length >>*= fun buffers ->
    let count buffers = List.fold_left (+) 0 (List.map Cstruct.len buffers) in
    assert_equal ~printer:string_of_int length (count buffers);
    MemFS.read fs filename 0 (length * 2) >>*= fun buffers ->
    assert_equal ~printer:string_of_int length (count buffers);
    MemFS.read fs filename 1 (length * 2) >>*= fun buffers ->
    assert_equal ~printer:string_of_int (length - 1) (count buffers);
    MemFS.read fs filename 1 (length - 2) >>*= fun buffers ->
    assert_equal ~printer:string_of_int (length - 2) (count buffers);
    MemFS.read fs filename length length >>*= fun buffers ->
    assert_equal ~printer:string_of_int 0 (count buffers);
    Lwt.return ()
  in
  Lwt_main.run t

(* Very simple, easy sector-aligned writes. Tests that
   read(write(data)) = data; and that files are extended properly *)
let test_write ((filename: string), (_offset, length)) () =
  let t =
    MemFS.format "" (Int64.mul 16L mib) >>*= fun fs ->
    let open Lwt in
    ( match List.rev (Fat_path.to_string_list (Fat_path.of_string filename)) with
      | [] -> assert false
      | [ _ ] -> return ()
      | _ :: dir ->
        List.fold_left (fun current dir ->
            current >>= fun current ->
            MemFS.mkdir fs (Fat_path.(to_string (of_string_list (current @ [dir]))))
            >>*= fun () ->
            return (current @ [dir])
          ) (return []) (List.rev dir) >>= fun _ ->
        return () )
    >>= fun () ->
    MemFS.create fs filename >>*= fun () ->
    let buffer = make_pattern "basic writing test " length in
    MemFS.write fs filename 0 buffer >>*= fun () ->
    MemFS.read fs filename 0 512 >>*= fun buffers ->
    let to_string x =
      Printf.sprintf "\"%s\"(%d)" (Cstruct.to_string x) (Cstruct.len x)
    in
    assert_equal ~printer:to_string ~cmp:cstruct_equal buffer (List.hd buffers);
    return ()
  in
  Lwt_main.run t

let test_destroy () =
  let t =
    MemFS.format "" 0x100000L >>*= fun fs ->
    MemFS.create fs "/data" >>*= fun () ->
    MemFS.destroy fs "/data" >>*= fun () ->
    MemFS.listdir fs "/" >>*= function
    | []    -> Lwt.return ()
    | items ->
      List.iter (Printf.printf "Item: %s\n") items;
      assert_failure "Items present after destroy!"
  in
  Lwt_main.run t

let rec allpairs xs ys = match xs with
  | []      -> []
  | x :: xs -> List.map (fun y -> x, y) ys @ (allpairs xs ys)

let _ =
  let write_tests =
    List.map (fun ((filename, (off, len)) as x) ->
        Printf.sprintf "write to %s at %d length %d" filename off len >::
        (test_write x)
      ) (allpairs interesting_filenames interesting_writes) in

  let suite = "fat" >::: [
      "test_parse_boot_sector" >:: test_parse_boot_sector;
      "checksum" >:: checksum_test;
      "test_root_list" >:: test_root_list;
      "test_chains" >:: test_chains;
      "test_create" >:: test_create;
      "test_listdir" >:: test_listdir;
      "test_listdir_subdir" >:: test_listdir_subdir;
      "test_read" >:: test_read;
      "test_destroy" >:: test_destroy;
    ] @ write_tests
  in
  run_test_tt_main suite
