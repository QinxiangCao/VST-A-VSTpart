open String
open Comment
open ClightC

let get_binder_list (s : string) : string list * string =
  (* print_endline s; *)
  let l = length s in
  let i = ref 0 in
  let is_whitespace c =
    c = '\n' || c = '\r' || c = ' ' || c = '\t'
  in
  let has_next_char () =
    !i < l
  in
  let next_char () =
    if !i < l then
      let c = s.[!i] in
      i := !i+1; c
    else failwith "Unexpected end of assertion"
  in
  let rec loop acc cnt =
    let c = next_char () in
    (* print_char c; *)
    if is_whitespace c then
      loop acc cnt
    else if c = '(' then
      loop acc (cnt+1)
    else if c = 'E' then
      if has_next_char() && next_char () = 'X' then
        let start = !i in
        let rec loop2 cnt =
          match next_char () with
          | '(' -> loop2 (cnt+1)
          | ')' -> loop2 (cnt-1)
          | ',' when cnt = 0 -> sub s start (!i - start)
          | _ -> loop2 cnt
        in
        (* print_int !i; *)
        let res = loop2 0 in
        (* print_endline res;
        print_int !i;
        print_newline (); *)
        loop (trim (res) :: acc) cnt
      else
        (List.rev acc, make cnt '(' ^ sub s (!i-2) (l-(!i-2)))
    else
      (List.rev acc, make cnt '(' ^ sub s (!i-1) (l-(!i-1)))
  in
  loop [] 0

let parse_comment s =
  let open String in
  let open Cabs in
  let s = trim s in
  let startwith s t =
    let l = length t in
    try let ss = sub s 0 l in
      if ss = t then Some (sub s l (length s - l)) else None
    with _ -> None
  in
  let step acc (name, ct) =
    match acc with
    | Some _ -> acc
    | None ->
      begin match startwith s name with
      | Some s -> Some (ct, s)
      | None -> None
      end
  in
  let comment_types = [
    ("Assert", Assert);
    ("Given", Given);
    ("Inv", Inv);
    ("With", With);
    ("Require", Require);
    ("Ensure", Ensure);
    ("Local", Local);
    ("Unlocal", Unlocal);
  ] in
  List.fold_left step None comment_types
