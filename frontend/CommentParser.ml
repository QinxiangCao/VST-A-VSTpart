open String
open Comment
open ClightC

(* let get_binder_list (s : string) : string list * string =
  print_endline s;
  let res =
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
  in
  List.iter print_endline (fst res);
  print_endline (snd res);
  res *)


let get_binder_list (s : string) : (string * string) list =
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
        let rec peak_binder_end j =
          (* Check whether all the binders are read off,
              and also return the position of the next binder
            e.g. if the tokens are 
                EX a b c,....
                      |<--- i is here
              then we should return false, so that the 
              remainder of the assert will be EX c, ...

              if the tokens are 
                EX a b c,....
                        |<--- i is here
              then we should return true, so that the remainder 
              will directly be the content of the assert
          *)
          if j < l then
            let c = s.[j] in
                (if (is_whitespace c) 
                  then peak_binder_end (j+1)
              else if c = ',' then (j, true)
                else (j, false))
          else failwith "Unexpected end of assertion"
        in
        let start, _ = peak_binder_end (!i) in
        i := start;
        let rec loop2 start acc' cnt' : (string * string) list  =
          (* print_char (s.[!i]);
          print_char ';';
          print_string " cnt':";
          print_int cnt';
          print_string " start:";
          print_int start;
          print_char ';';
          print_string " nexti:";
          print_int (!i+1);          
          print_char ';'; 
          print_newline (); *)
          match next_char () with
          | '(' -> loop2 start acc' (cnt'+1)
          | ')' -> loop2 start acc' (cnt'-1)
          | _ as c when cnt' = 0 -> 
              if (is_whitespace c) || c = ',' then
                let next_start, next_is_end = peak_binder_end (!i-1) in
                (* print_string @@ (string_of_bool next_is_end) ^ ";" ;
                print_char (s.[next_start]);
                print_newline (); *)
                if next_is_end then
                  (sub s start (!i - start - 1), 
                  make cnt '(' ^ trim @@ sub s (next_start+1) (l-((next_start+1)))) :: acc'
                    (* +1 to remove the ',' *)
                else
                  let acc_new = (sub s start (!i - start - 1), 
                  make cnt '(' ^ "EX " ^ trim @@ sub s (next_start) (l-next_start)) :: acc' in
                  i := next_start;
                  loop2 (next_start) acc_new cnt'
              else 
                (* acc' *)
                loop2 start acc' cnt'
          | _ -> 
            (* acc' *)
            loop2 start acc' cnt'
        in
        (* print_int !i; *)
        let res = loop2 (start) [] 0 in
        (* print_endline res;
        print_int !i;
        print_newline (); *)
        loop (res @ acc) cnt
      else
        acc
        (* (List.rev acc, make cnt '(' ^ sub s (!i-2) (l-(!i-2))) *)
    else
      acc
      (* (List.rev acc, make cnt '(' ^ sub s (!i-1) (l-(!i-1))) *)
  in
  let res = loop [] 0 in
  List.map (fun (binder, ass) -> (trim binder, trim ass)) res
  


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
