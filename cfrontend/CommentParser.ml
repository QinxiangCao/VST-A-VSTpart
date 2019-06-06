open String

let get_binder_list (s : string) : string list =
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
  let rec loop acc =
    let c = next_char () in
    (* print_char c; *)
    if is_whitespace c || c = '(' then
      loop acc
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
        loop (trim (res) :: acc)
      else
        acc
    else
      acc
  in
  List.rev (loop [])
