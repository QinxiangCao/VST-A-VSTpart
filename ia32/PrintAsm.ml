(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Printing IA32 assembly code in asm syntax *)

open Printf
open Datatypes
open Camlcoq
open AST
open Asm

(* Recognition of target ABI and asm syntax *)

type target = ELF | MacOS | Cygwin

let target = 
  match Configuration.system with
  | "macosx" -> MacOS
  | "linux"  -> ELF
  | "bsd"    -> ELF
  | "cygwin" -> Cygwin
  | _        -> invalid_arg ("System " ^ Configuration.system ^ " not supported")

(* On-the-fly label renaming *)

let next_label = ref 100

let new_label() =
  let lbl = !next_label in incr next_label; lbl

let current_function_labels = (Hashtbl.create 39 : (label, int) Hashtbl.t)

let transl_label lbl =
  try
    Hashtbl.find current_function_labels lbl
  with Not_found ->
    let lbl' = new_label() in
    Hashtbl.add current_function_labels lbl lbl';
    lbl'

(* Basic printing functions *)

let coqint oc n =
  fprintf oc "%ld" (camlint_of_coqint n)

let raw_symbol oc s =
  match target with
  | ELF -> fprintf oc "%s" s
  | MacOS | Cygwin -> fprintf oc "_%s" s

let re_variadic_stub = Str.regexp "\\(.*\\)\\$[if]*$"

let symbol oc symb =
  let s = extern_atom symb in
  if Str.string_match re_variadic_stub s 0
  then raw_symbol oc (Str.matched_group 1 s)
  else raw_symbol oc s

let symbol_offset oc (symb, ofs) =
  symbol oc symb;
  if ofs <> 0l then fprintf oc " + %ld" ofs

let label oc lbl =
  match target with
  | ELF -> fprintf oc ".L%d" lbl
  | MacOS | Cygwin -> fprintf oc "L%d" lbl

let comment = "#"

let int_reg_name = function
  | EAX -> "%eax"  | EBX -> "%ebx"  | ECX -> "%ecx"  | EDX -> "%edx"
  | ESI -> "%esi"  | EDI -> "%edi"  | EBP -> "%ebp"  | ESP -> "%esp"

let int8_reg_name = function
  | EAX -> "%al"  | EBX -> "%bl"  | ECX -> "%cl"  | EDX -> "%dl"
  | _ -> assert false

let int16_reg_name = function
  | EAX -> "%ax"  | EBX -> "%bx"  | ECX -> "%cx"  | EDX -> "%dx"
  | ESI -> "%si"  | EDI -> "%di"  | EBP -> "%bp"  | ESP -> "%sp"

let float_reg_name = function
  | XMM0 -> "%xmm0"  | XMM1 -> "%xmm1"  | XMM2 -> "%xmm2"  | XMM3 -> "%xmm3"
  | XMM4 -> "%xmm4"  | XMM5 -> "%xmm5"  | XMM6 -> "%xmm6"  | XMM7 -> "%xmm7"

let ireg oc r = output_string oc (int_reg_name r)
let ireg8 oc r = output_string oc (int8_reg_name r)
let ireg16 oc r = output_string oc (int16_reg_name r)
let freg oc r = output_string oc (float_reg_name r)

let preg oc = function
  | IR r -> ireg oc r
  | FR r -> freg oc r
  | _    -> assert false

let addressing oc (Addrmode(base, shift, cst)) =
  begin match cst with
  | Coq_inl n ->
      let n = camlint_of_coqint n in
      fprintf oc "%ld" n
  | Coq_inr(Coq_pair(id, ofs)) -> 
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then symbol oc id
      else fprintf oc "(%a + %ld)" symbol id ofs
  end;
  begin match base, shift with
  | None, None -> ()
  | Some r1, None -> fprintf oc "(%a)" ireg r1
  | None, Some(Coq_pair(r2,sc)) -> fprintf oc "(,%a,%a)" ireg r2 coqint sc
  | Some r1, Some(Coq_pair(r2,sc)) -> fprintf oc "(%a,%a,%a)" ireg r1 ireg r2 coqint sc
  end

let name_of_condition = function
  | Cond_e -> "e" | Cond_ne -> "ne"
  | Cond_b -> "b" | Cond_be -> "be" | Cond_ae -> "ae" | Cond_a -> "a"
  | Cond_l -> "l" | Cond_le -> "le" | Cond_ge -> "ge" | Cond_g -> "g"
  | Cond_p -> "p" | Cond_np -> "np" 
  | Cond_nep | Cond_enp -> assert false (* treated specially *)

let section oc name =
  fprintf oc "	%s\n" name

(* Names of sections *)

let (text, data, const_data, float_literal, jumptable_literal) =
  match target with
  | ELF ->
      (".text",
       ".data",
       ".section	.rodata",
       ".section	.rodata.cst8,\"a\",@progbits",
       ".text")
  | MacOS ->
      (".text",
       ".data",
       ".const",
       ".const_data",
       ".text")
  | Cygwin ->
      (".text",
       ".data",
       ".section	.rdata,\"dr\"",
       ".section	.rdata,\"dr\"",
       ".text")

(* SP adjustment to allocate or free a stack frame *)

let stack_alignment =
  match target with
  | ELF | Cygwin -> 8               (* minimum is 4, 8 is better for perfs *)
  | MacOS -> 16                     (* mandatory *)

let int32_align n a =
  if n >= 0l
  then Int32.logand (Int32.add n (Int32.of_int (a-1))) (Int32.of_int (-a))
  else Int32.logand n (Int32.of_int (-a))

let sp_adjustment lo hi =
  let lo = camlint_of_coqint lo and hi = camlint_of_coqint hi in
  let sz = Int32.sub hi lo in
(* Enforce stack alignment, noting that 4 bytes are already allocated
   by the call *)
  let sz = Int32.sub (int32_align (Int32.add sz 4l) stack_alignment) 4l in
  assert (sz >= 0l);
  sz

(* Base-2 log of a Caml integer *)

let rec log2 n =
  assert (n > 0);
  if n = 1 then 0 else 1 + log2 (n lsr 1)

(* Emit a align directive *)

let print_align oc n =
  match target with
  | ELF | Cygwin -> fprintf oc "	.align	%d\n" n
  | MacOS        -> fprintf oc "	.align	%d\n" (log2 n)

let need_masks = ref false

(* Built-in functions *)

(* Built-ins.  They come in two flavors: 
   - inlined by the compiler: take their arguments in arbitrary
     registers; preserve all registers except ECX, EDX, XMM6 and XMM7
   - inlined while printing asm code; take their arguments in
     locations dictated by the calling conventions; preserve
     callee-save regs only. *)

let print_builtin_inlined oc name args res =
  fprintf oc "%s begin builtin %s\n" comment name;
  begin match name, args, res with
  (* Volatile reads *)
  | "__builtin_volatile_read_int8unsigned", [IR addr], IR res ->
      fprintf oc "	movzbl	0(%a), %a\n" ireg addr ireg res
  | "__builtin_volatile_read_int8signed", [IR addr], IR res ->
      fprintf oc "	movsbl	0(%a), %a\n" ireg addr ireg res
  | "__builtin_volatile_read_int16unsigned", [IR addr], IR res ->
      fprintf oc "	movzwl	0(%a), %a\n" ireg addr ireg res
  | "__builtin_volatile_read_int16signed", [IR addr], IR res ->
      fprintf oc "	movswl	0(%a), %a\n" ireg addr ireg res
  | ("__builtin_volatile_read_int32"|"__builtin_volatile_read_pointer"), [IR addr], IR res ->
      fprintf oc "	movl	0(%a), %a\n" ireg addr ireg res
  | "__builtin_volatile_read_float32", [IR addr], FR res ->
      fprintf oc "	cvtss2sd 0(%a), %a\n" ireg addr freg res
  | "__builtin_volatile_read_float64", [IR addr], FR res ->
      fprintf oc "	movsd	0(%a), %a\n" ireg addr freg res
  (* Volatile writes *)
  | ("__builtin_volatile_write_int8unsigned"|"__builtin_volatile_write_int8signed"), [IR addr; IR src], _ ->
      if Asmgen.low_ireg src then
        fprintf oc "	movb	%a, 0(%a)\n" ireg8 src ireg addr
      else begin
        fprintf oc "	movl	%a, %%ecx\n" ireg src;
        fprintf oc "	movb	%%cl, 0(%a)\n" ireg addr
      end
  | ("__builtin_volatile_write_int16unsigned"|"__builtin_volatile_write_int16signed"), [IR addr; IR src], _ ->
      if Asmgen.low_ireg src then
        fprintf oc "	movw	%a, 0(%a)\n" ireg16 src ireg addr
      else begin
        fprintf oc "	movl	%a, %%ecx\n" ireg src;
        fprintf oc "	movw	%%cx, 0(%a)\n" ireg addr
      end
  | ("__builtin_volatile_write_int32"|"__builtin_volatile_write_pointer"), [IR addr; IR src], _ ->
      fprintf oc "	movl	%a, 0(%a)\n" ireg src ireg addr
  | "__builtin_volatile_write_float32", [IR addr; FR src], _ ->
      fprintf oc "	cvtsd2ss %a, %%xmm7\n" freg src;
      fprintf oc "	movss	%%xmm7, 0(%a)\n" ireg addr
  | "__builtin_volatile_write_float64", [IR addr; FR src], _ ->
      fprintf oc "	movsd	%a, 0(%a)\n" freg src ireg addr
  (* Float arithmetic *)
  | "__builtin_fabs", [FR a1], FR res ->
      need_masks := true;
      if a1 <> res then
        fprintf oc "	movsd	%a, %a\n" freg a1 freg res;
      fprintf oc "	andpd	%a, %a\n" raw_symbol "__absd_mask" freg res
  | "__builtin_fsqrt", [FR a1], FR res ->
      fprintf oc "	sqrtsd	%a, %a\n" freg a1 freg res
  | "__builtin_fmax", [FR a1; FR a2], FR res ->
      if res = a1 then
        fprintf oc "	maxsd	%a, %a\n" freg a2 freg res
      else if res = a2 then
        fprintf oc "	maxsd	%a, %a\n" freg a1 freg res
      else begin
        fprintf oc "	movsd	%a, %a\n" freg a1 freg res;
        fprintf oc "	maxsd	%a, %a\n" freg a2 freg res
      end
  | "__builtin_fmin", [FR a1; FR a2], FR res ->
      if res = a1 then
        fprintf oc "	minsd	%a, %a\n" freg a2 freg res
      else if res = a2 then
        fprintf oc "	minsd	%a, %a\n" freg a1 freg res
      else begin
        fprintf oc "	movsd	%a, %a\n" freg a1 freg res;
        fprintf oc "	minsd	%a, %a\n" freg a2 freg res
      end
  | _ ->
      invalid_arg ("unrecognized builtin " ^ name)
  end;
  fprintf oc "%s end builtin %s\n" comment name

let re_builtin_function = Str.regexp "__builtin_"

let is_builtin_function s =
  Str.string_match re_builtin_function (extern_atom s) 0

let print_builtin_function oc s =
  fprintf oc "%s begin builtin function %s\n" comment (extern_atom s);
  (* arguments: on stack, starting at offset 0 *)
  (* result: EAX or ST0 *)
  begin match extern_atom s with
  (* Block copy *)
  | "__builtin_memcpy" ->
      fprintf oc "	movl	%%esi, %%eax\n";
      fprintf oc "	movl	%%edi, %%edx\n";
      fprintf oc "	movl	0(%%esp), %%edi\n";
      fprintf oc "	movl	4(%%esp), %%esi\n";
      fprintf oc "	movl	8(%%esp), %%ecx\n";
      fprintf oc "	rep movsb\n";
      fprintf oc "	movl	%%eax, %%esi\n";
      fprintf oc "	movl	%%edx, %%edi\n"
  | "__builtin_memcpy_words" ->
      fprintf oc "	movl	%%esi, %%eax\n";
      fprintf oc "	movl	%%edi, %%edx\n";
      fprintf oc "	movl	0(%%esp), %%edi\n";
      fprintf oc "	movl	4(%%esp), %%esi\n";
      fprintf oc "	movl	8(%%esp), %%ecx\n";
      fprintf oc "	shr	$2, %%ecx\n";
      fprintf oc "	rep movsl\n";
      fprintf oc "	movl	%%eax, %%esi\n";
      fprintf oc "	movl	%%edx, %%edi\n"
  (* Catch-all *)
  | s ->
      invalid_arg ("unrecognized builtin function " ^ s)
  end;
  fprintf oc "%s end builtin function %s\n" comment (extern_atom s)

let re_builtin_annotation = Str.regexp "__builtin_annotation_\"\\(.*\\)\"$"

let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"

let print_annotation oc txt args res =
  fprintf oc "%s annotation: " comment;
  let print_fragment = function
  | Str.Text s ->
      output_string oc s
  | Str.Delim "%%" ->
      output_char oc '%'
  | Str.Delim s ->
      let n = int_of_string (String.sub s 1 (String.length s - 1)) in
      try
        preg oc (List.nth args (n-1))
      with Failure _ ->
        fprintf oc "<bad parameter %s>" s in
  List.iter print_fragment (Str.full_split re_annot_param txt);
  fprintf oc "\n";
  match args, res with
  | [], _ -> ()
  | IR src :: _, IR dst ->
      if dst <> src then fprintf oc "	movl	%a, %a\n" ireg src ireg dst
  | FR src :: _, FR dst ->
      if dst <> src then fprintf oc "	movsd	%a, %a\n" freg src freg dst
  | _, _ -> assert false

(* Printing of instructions *)

module Labelset = Set.Make(struct type t = label let compare = compare end)

let float_literals : (int * int64) list ref = ref []
let jumptables : (int * label list) list ref = ref []

(* Reminder on AT&T syntax: op source, dest *)

let print_instruction oc labels = function
  (* Moves *)
  | Pmov_rr(rd, r1) ->
      fprintf oc "	movl	%a, %a\n" ireg r1 ireg rd
  | Pmov_ri(rd, n) ->
      let n = camlint_of_coqint n in
      if n = 0l then
        fprintf oc "	xorl	%a, %a\n" ireg rd ireg rd
      else
        fprintf oc "	movl	$%ld, %a\n" n ireg rd
  | Pmov_rm(rd, a) ->
      fprintf oc "	movl	%a, %a\n" addressing a ireg rd
  | Pmov_mr(a, r1) ->
      fprintf oc "	movl	%a, %a\n" ireg r1 addressing a
  | Pmovd_fr(rd, r1) ->
      fprintf oc "	movd	%a, %a\n" ireg r1 freg rd
  | Pmovd_rf(rd, r1) ->
      fprintf oc "	movd	%a, %a\n" freg r1 ireg rd
  | Pmovsd_ff(rd, r1) ->
      fprintf oc "	movapd	%a, %a\n" freg r1 freg rd
  | Pmovsd_fi(rd, n) ->
      let b = Int64.bits_of_float n in
      if b = 0L then (* +0.0 *)
        fprintf oc "	xorpd	%a, %a %s +0.0\n" freg rd freg rd comment
      else begin
        let lbl = new_label() in
        fprintf oc "	movsd	%a, %a %s %.18g\n" label lbl freg rd comment n;
        float_literals := (lbl, b) :: !float_literals
      end
  | Pmovsd_fm(rd, a) ->
      fprintf oc "	movsd	%a, %a\n" addressing a freg rd
  | Pmovsd_mf(a, r1) ->
      fprintf oc "	movsd	%a, %a\n" freg r1 addressing a
  | Pfld_f(r1) ->
      fprintf oc "	subl	$8, %%esp\n";
      fprintf oc "	movsd	%a, 0(%%esp)\n" freg r1;
      fprintf oc "	fldl	0(%%esp)\n";
      fprintf oc "	addl	$8, %%esp\n"
  | Pfld_m(a) ->
      fprintf oc "	fldl	%a\n" addressing a
  | Pfstp_f(rd) ->
      fprintf oc "	subl	$8, %%esp\n";
      fprintf oc "	fstpl	0(%%esp)\n";
      fprintf oc "	movsd	0(%%esp), %a\n" freg rd;
      fprintf oc "	addl	$8, %%esp\n"
  | Pfstp_m(a) ->
      fprintf oc "	fstpl	%a\n" addressing a
  (** Moves with conversion *)
  | Pmovb_mr(a, r1) ->
      fprintf oc "	movb	%a, %a\n" ireg8 r1 addressing a
  | Pmovw_mr(a, r1) ->
      fprintf oc "	movw	%a, %a\n" ireg16 r1 addressing a
  | Pmovzb_rr(rd, r1) ->
      fprintf oc "	movzbl	%a, %a\n" ireg8 r1 ireg rd
  | Pmovzb_rm(rd, a) ->
      fprintf oc "	movzbl	%a, %a\n" addressing a ireg rd
  | Pmovsb_rr(rd, r1) ->
      fprintf oc "	movsbl	%a, %a\n" ireg8 r1 ireg rd
  | Pmovsb_rm(rd, a) ->
      fprintf oc "	movsbl	%a, %a\n" addressing a ireg rd
  | Pmovzw_rr(rd, r1) ->
      fprintf oc "	movzwl	%a, %a\n" ireg16 r1 ireg rd
  | Pmovzw_rm(rd, a) ->
      fprintf oc "	movzwl	%a, %a\n" addressing a ireg rd
  | Pmovsw_rr(rd, r1) ->
      fprintf oc "	movswl	%a, %a\n" ireg16 r1 ireg rd
  | Pmovsw_rm(rd, a) ->
      fprintf oc "	movswl	%a, %a\n" addressing a ireg rd
  | Pcvtss2sd_fm(rd, a) ->
      fprintf oc "	cvtss2sd %a, %a\n" addressing a freg rd
  | Pcvtsd2ss_ff(rd, r1) ->
      fprintf oc "	cvtsd2ss %a, %a\n" freg r1 freg rd;
      fprintf oc "	cvtss2sd %a, %a\n" freg rd freg rd
  | Pcvtsd2ss_mf(a, r1) ->
      fprintf oc "	cvtsd2ss %a, %%xmm7\n" freg r1;
      fprintf oc "	movss	%%xmm7, %a\n" addressing a
  | Pcvttsd2si_rf(rd, r1) ->
      fprintf oc "	cvttsd2si %a, %a\n" freg r1 ireg rd
  | Pcvtsi2sd_fr(rd, r1) ->
      fprintf oc "	cvtsi2sd %a, %a\n" ireg r1 freg rd
  (** Arithmetic and logical operations over integers *)
  | Plea(rd, a) ->
      fprintf oc "	leal	%a, %a\n" addressing a ireg rd
  | Pneg(rd) ->
      fprintf oc "	negl	%a\n" ireg rd
  | Psub_rr(rd, r1) ->
      fprintf oc "	subl	%a, %a\n" ireg r1 ireg rd
  | Pimul_rr(rd, r1) ->
      fprintf oc "	imull	%a, %a\n" ireg r1 ireg rd
  | Pimul_ri(rd, n) ->
      fprintf oc "	imull	$%a, %a\n" coqint n ireg rd
  | Pdiv(r1) ->
      fprintf oc "	xorl	%%edx, %%edx\n";
      fprintf oc "	divl	%a\n" ireg r1
  | Pidiv(r1) ->
      fprintf oc "	cltd\n";
      fprintf oc "	idivl	%a\n" ireg r1
  | Pand_rr(rd, r1) ->
      fprintf oc "	andl	%a, %a\n" ireg r1 ireg rd
  | Pand_ri(rd, n) ->
      fprintf oc "	andl	$%a, %a\n" coqint n ireg rd
  | Por_rr(rd, r1) ->
      fprintf oc "	orl	%a, %a\n" ireg r1 ireg rd
  | Por_ri(rd, n) ->
      fprintf oc "	orl	$%a, %a\n" coqint n ireg rd
  | Pxor_rr(rd, r1) ->
      fprintf oc "	xorl	%a, %a\n" ireg r1 ireg rd
  | Pxor_ri(rd, n) ->
      fprintf oc "	xorl	$%a, %a\n" coqint n ireg rd
  | Psal_rcl(rd) ->
      fprintf oc "	sall	%%cl, %a\n" ireg rd
  | Psal_ri(rd, n) ->
      fprintf oc "	sall	$%a, %a\n" coqint n ireg rd
  | Pshr_rcl(rd) ->
      fprintf oc "	shrl	%%cl, %a\n" ireg rd
  | Pshr_ri(rd, n) ->
      fprintf oc "	shrl	$%a, %a\n" coqint n ireg rd
  | Psar_rcl(rd) ->
      fprintf oc "	sarl	%%cl, %a\n" ireg rd
  | Psar_ri(rd, n) ->
      fprintf oc "	sarl	$%a, %a\n" coqint n ireg rd
  | Pror_ri(rd, n) ->
      fprintf oc "	rorl	$%a, %a\n" coqint n ireg rd
  | Pcmp_rr(r1, r2) ->
      fprintf oc "	cmpl	%a, %a\n" ireg r2 ireg r1
  | Pcmp_ri(r1, n) ->
      fprintf oc "	cmpl	$%a, %a\n" coqint n ireg r1
  | Ptest_rr(r1, r2) ->
      fprintf oc "	testl	%a, %a\n" ireg r2 ireg r1
  | Ptest_ri(r1, n) ->
      fprintf oc "	testl	$%a, %a\n" coqint n ireg r1
  | Pcmov(c, rd, r1) ->
      assert (c <> Cond_nep && c <> Cond_enp);
      fprintf oc "	cmov%s	%a, %a\n" (name_of_condition c) ireg r1 ireg rd
  | Psetcc(c, rd) ->
      begin match c with
      | Cond_nep ->
          fprintf oc "	setne	%%cl\n";
          fprintf oc "	setp	%%dl\n";
          fprintf oc "	orb	%%dl, %%cl\n"
      | Cond_enp ->
          fprintf oc "	sete	%%cl\n";
          fprintf oc "	setnp	%%dl\n";
          fprintf oc "	andb	%%dl, %%cl\n"
      | _ ->
          fprintf oc "	set%s	%%cl\n" (name_of_condition c)
      end;
      fprintf oc "	movzbl	%%cl, %a\n" ireg rd
  (** Arithmetic operations over floats *)
  | Paddd_ff(rd, r1) ->
      fprintf oc "	addsd	%a, %a\n" freg r1 freg rd
  | Psubd_ff(rd, r1) ->
      fprintf oc "	subsd	%a, %a\n" freg r1 freg rd
  | Pmuld_ff(rd, r1) ->
      fprintf oc "	mulsd	%a, %a\n" freg r1 freg rd
  | Pdivd_ff(rd, r1) ->
      fprintf oc "	divsd	%a, %a\n" freg r1 freg rd
  | Pnegd (rd) ->
      need_masks := true;
      fprintf oc "	xorpd	%a, %a\n" raw_symbol "__negd_mask" freg rd
  | Pabsd (rd) ->
      need_masks := true;
      fprintf oc "	andpd	%a, %a\n" raw_symbol "__absd_mask" freg rd
  | Pcomisd_ff(r1, r2) ->
      fprintf oc "	comisd	%a, %a\n" freg r2 freg r1
  (** Branches and calls *)
  | Pjmp_l(l) ->
      fprintf oc "	jmp	%a\n" label (transl_label l)
  | Pjmp_s(f) ->
      if not (is_builtin_function f) then
        fprintf oc "	jmp	%a\n" symbol f
      else begin
        print_builtin_function oc f;
        fprintf oc "	ret\n"
      end
  | Pjmp_r(r) ->
      fprintf oc "	jmp	*%a\n" ireg r
  | Pjcc(c, l) ->
      let l = transl_label l in
      begin match c with
      | Cond_nep ->
          fprintf oc "	jp	%a\n" label l;
          fprintf oc "	jne	%a\n" label l
      | Cond_enp ->
          let l' = new_label() in
          fprintf oc "	jp	%a\n" label l';
          fprintf oc "	je	%a\n" label l;
          fprintf oc "%a:\n" label l'
      | _ ->
          fprintf oc "	j%s	%a\n" (name_of_condition c) label l
      end
  | Pjmptbl(r, tbl) ->
      let l = new_label() in
      fprintf oc "	jmp	*%a(, %a, 4)\n" label l ireg r;
      jumptables := (l, tbl) :: !jumptables
  | Pcall_s(f) ->
      if not (is_builtin_function f) then
        fprintf oc "	call	%a\n" symbol f
      else
        print_builtin_function oc f
  | Pcall_r(r) ->
      fprintf oc "	call	*%a\n" ireg r
  | Pret ->
      fprintf oc "	ret\n"
  (** Pseudo-instructions *)
  | Plabel(l) ->
      if Labelset.mem l labels then
        fprintf oc "%a:\n" label (transl_label l)
  | Pallocframe(lo, hi, ofs_ra, ofs_link) ->
      let sz = sp_adjustment lo hi in
      let ofs_link = camlint_of_coqint ofs_link in
      fprintf oc "	subl	$%ld, %%esp\n" sz;
      fprintf oc "	leal	%ld(%%esp), %%edx\n" (Int32.add sz 4l);
      fprintf oc "	movl	%%edx, %ld(%%esp)\n" ofs_link
  | Pfreeframe(lo, hi, ofs_ra, ofs_link) ->
      let sz = sp_adjustment lo hi in
      fprintf oc "	addl	$%ld, %%esp\n" sz
  | Pbuiltin(ef, args, res) ->
      let name = extern_atom ef.ef_id in
      if Str.string_match re_builtin_annotation name 0
      then print_annotation oc (Str.matched_group 1 name) args res
      else print_builtin_inlined oc name args res

let print_literal oc (lbl, n) =
  fprintf oc "%a:	.quad	0x%Lx\n" label lbl n

let print_jumptable oc (lbl, tbl) =
  fprintf oc "%a:" label lbl;
  List.iter
    (fun l -> fprintf oc "	.long	%a\n" label (transl_label l))
    tbl

let rec labels_of_code accu = function
  | [] ->
      accu
  | (Pjmp_l lbl | Pjcc(_, lbl)) :: c ->
      labels_of_code (Labelset.add lbl accu) c
  | Pjmptbl(_, tbl) :: c ->
      labels_of_code (List.fold_right Labelset.add tbl accu) c
  | _ :: c ->
      labels_of_code accu c

let print_function oc name code =
  Hashtbl.clear current_function_labels;
  float_literals := [];
  jumptables := [];
  section oc text;
  print_align oc 16;
  if not (C2C.atom_is_static name) then
    fprintf oc "	.globl %a\n" symbol name;
  fprintf oc "%a:\n" symbol name;
  List.iter (print_instruction oc (labels_of_code Labelset.empty code)) code;
  if target = ELF then begin
    fprintf oc "	.type	%a, @function\n" symbol name;
    fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
  end;
  if !float_literals <> [] then begin
    section oc float_literal;
    print_align oc 8;
    List.iter (print_literal oc) !float_literals;
    float_literals := []
  end;
  if !jumptables <> [] then begin
    section oc jumptable_literal;
    print_align oc 4;
    List.iter (print_jumptable oc) !jumptables;
    jumptables := []
  end

let print_fundef oc (Coq_pair(name, defn)) =
  match defn with
  | Internal code -> print_function oc name code
  | External ef -> ()

let print_init oc = function
  | Init_int8 n ->
      fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
  | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
  | Init_int32 n ->
      fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
  | Init_float32 n ->
      fprintf oc "	.long	%ld %s %.18g\n" (Int32.bits_of_float n) comment n
  | Init_float64 n ->
      fprintf oc "	.quad	%Ld %s %.18g\n" (Int64.bits_of_float n) comment n
  | Init_space n ->
      let n = camlint_of_z n in
      if n > 0l then fprintf oc "	.space	%ld\n" n
  | Init_addrof(symb, ofs) ->
      fprintf oc "	.long	%a\n" 
                 symbol_offset (symb, camlint_of_coqint ofs)

let print_init_data oc name id =
  if Str.string_match PrintCsyntax.re_string_literal (extern_atom name) 0
  && List.for_all (function Init_int8 _ -> true | _ -> false) id
  then
    fprintf oc "	.ascii	\"%s\"\n" (PrintCsyntax.string_of_init id)
  else
    List.iter (print_init oc) id

let print_var oc (Coq_pair(name, v)) =
  match v.gvar_init with
  | [] -> ()
  | _  ->
      let sec =
        if v.gvar_readonly then const_data else data
      and align =
        match C2C.atom_alignof name with
        | Some a -> a
        | None -> 8 (* 8-alignment is a safe default *)
      in
      section oc sec;
      print_align oc align;
      if not (C2C.atom_is_static name) then
        fprintf oc "	.globl	%a\n" symbol name;
      fprintf oc "%a:\n" symbol name;
      print_init_data oc name v.gvar_init;
      if target = ELF then begin
        fprintf oc "	.type	%a, @object\n" symbol name;
        fprintf oc "	.size	%a, . - %a\n" symbol name symbol name
      end

let print_program oc p =
  need_masks := false;
  List.iter (print_var oc) p.prog_vars;
  List.iter (print_fundef oc) p.prog_funct;
  if !need_masks then begin
    section oc float_literal;
    print_align oc 16;
    fprintf oc "%a:	.quad   0x8000000000000000, 0\n"
               raw_symbol "__negd_mask";
    fprintf oc "%a:	.quad   0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF\n"
               raw_symbol "__absd_mask"
  end
