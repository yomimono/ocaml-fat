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
open Lwt
open Fat
open Fat_lwt

let read_sector filename =
  Lwt_unix.openfile filename [ Lwt_unix.O_RDONLY ] 0o0 >>= fun fd ->
  let buf = Cstruct.create 512 in
  really_read fd buf >>= fun () ->
  Lwt_unix.close fd >>= fun () ->
  return buf

let checksum_test () =
  let open Name in
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
  let bytes = Bitstring.bitstring_of_file "lib_test/root.dat" in
  let all = Name.list bytes in
  assert_equal ~printer:string_of_int 5 (List.length all);
  let x = List.nth all 1 in
  let utf_filename = "l\000o\000w\000e\000r\000.\000t\000x\000t\000\000\000\255\255\255\255\255\255" in
  assert_equal ~printer:(fun x -> x) utf_filename x.Name.utf_filename;
  let a, b = x.Name.dos in
  assert_equal ~printer:string_of_int 192 a;
  assert_equal ~printer:(fun x -> x) "LOWER" b.Name.filename;
  assert_equal ~printer:(fun x -> x) "TXT" b.Name.ext;
  assert_equal ~printer:string_of_bool false b.Name.deleted;
  assert_equal ~printer:string_of_bool false b.Name.read_only;
  assert_equal ~printer:string_of_bool false b.Name.hidden;
  assert_equal ~printer:string_of_bool false b.Name.system;
  assert_equal ~printer:string_of_bool false b.Name.volume;
  assert_equal ~printer:string_of_bool false b.Name.subdir;
  assert_equal ~printer:string_of_bool true b.Name.archive;
  assert_equal ~printer:string_of_int 0 b.Name.start_cluster;
  assert_equal ~printer:Int32.to_string 0l b.Name.file_size;
  assert_equal ~printer:string_of_int 2013 b.Name.create.Name.year;
  assert_equal ~printer:string_of_int 11 b.Name.create.Name.month;
  assert_equal ~printer:string_of_int 2 b.Name.create.Name.day;
  assert_equal ~printer:string_of_int 16 b.Name.create.Name.hours;
  assert_equal ~printer:string_of_int 58 b.Name.create.Name.mins;
  assert_equal ~printer:string_of_int 52 b.Name.create.Name.secs;
  assert_equal ~printer:string_of_int 100 b.Name.create.Name.ms;
  let lfns = x.Name.lfns in
  assert_equal ~printer:string_of_int 1 (List.length lfns);
  let a, b = List.hd lfns in
  assert_equal ~printer:string_of_int 160 a;
  assert_equal ~printer:string_of_bool false b.Name.lfn_deleted;
  assert_equal ~printer:string_of_bool true b.Name.lfn_last;
  assert_equal ~printer:string_of_int 1 b.Name.lfn_seq;
  assert_equal ~printer:string_of_int 252 b.Name.lfn_checksum;
  assert_equal ~printer:(fun x -> x) utf_filename b.Name.lfn_utf16_name

let test_chains () =
  let t =
    let open Boot_sector in
    read_sector "lib_test/bootsector.dat" >>= fun bytes ->
    let boot = match unmarshal bytes with
    | Result.Error x -> failwith x
    | Result.Ok x -> x in
    let printer = function
    | None -> "None"
    | Some x -> "Some " ^ (Fat_format.to_string x) in
    assert_equal ~printer (Some Fat_format.FAT16) (Boot_sector.detect_format boot);
    let bytes = Bitstring.bitstring_of_file "lib_test/root.dat" in
    let all = Name.list bytes in
    let fat = Bitstring.bitstring_of_file "lib_test/fat.dat" in

    let expected = [0; 0; 0; 2235; 3] in
    let actual = List.map (fun x -> (snd (x.Name.dos)).Name.start_cluster) all in
    assert_equal ~printer:print_int_list expected actual; 
    assert_equal ~printer:print_int_list [] (Entry.follow_chain Fat_format.FAT16 fat 0);

    assert_equal ~printer:print_int_list [2235] (Entry.follow_chain Fat_format.FAT16 fat 2235);
    let rec ints last x = if x = last then [x] else x :: (ints last (x + 1)) in
    let expected = ints 2234 3 in
    assert_equal ~printer:print_int_list expected (Entry.follow_chain Fat_format.FAT16 fat 3);
    return () in
  Lwt_main.run t

let test_parse_boot_sector () =
  let t =
    let open Boot_sector in
    read_sector "lib_test/bootsector.dat" >>= fun bytes ->
    let x = match unmarshal bytes with
    | Result.Error x -> failwith x
    | Result.Ok x -> x in
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
      let sectors_of_fat = [4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35] in
      let sectors_of_root_dir = [68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99] in
      assert_equal ~printer:print_int_list sectors_of_fat (Boot_sector.sectors_of_fat x);
      assert_equal ~printer:print_int_list sectors_of_root_dir (Boot_sector.sectors_of_root_dir x) in
    check x;
    let buf = Cstruct.create sizeof in
    marshal buf x;
    let x = match unmarshal buf with
    | Result.Error x -> failwith x
    | Result.Ok x -> x in
    check x;
    return () in
  Lwt_main.run t

let _ =
  let verbose = ref false in
  Arg.parse [
    "-verbose", Arg.Unit (fun _ -> verbose := true), "Run in verbose mode";
  ] (fun x -> Printf.fprintf stderr "Ignoring argument: %s" x)
    "Test FAT filesystem";

  let suite = "fat" >::: [
    "test_parse_boot_sector" >:: test_parse_boot_sector;
    "checksum" >:: checksum_test;
    "test_root_list" >:: test_root_list;
    "test_chains" >:: test_chains;
  ] in
  run_test_tt ~verbose:!verbose suite
