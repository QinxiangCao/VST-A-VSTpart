Require BuildAnnotation.
Require ClassifyComment.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* Coqlib *)
(* Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)". *)

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

Extract Inlined Constant Comment.string => "string".

Extract Constant BuildAnnotation.get_binder_list => "CommentParser.get_binder_list".
Extract Constant ClassifyComment.parse_comment => "CommentParser.parse_comment".

Load extractionMachdep.

Extraction Blacklist List String Int.

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
Set Extraction AccessOpaque.

(* Go! *)

Cd "frontend".
Cd "extraction".

Separate Extraction
   BuildAnnotation.annotate_program
   ClassifyComment.classify_program.
