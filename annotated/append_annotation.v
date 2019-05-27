Require Import append.
Require Import append_def.
From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

                                                  Module Info.
                                                    Definition version := "3.5"%string.
                                                    Definition build_number := ""%string.
                                                    Definition build_tag := ""%string.
                                                    Definition arch := "x86"%string.
                                                    Definition model := "32sse2"%string.
                                                    Definition abi := "standard"%string.
                                                    Definition bitsize := 32.
                                                    Definition big_endian := false.
                                                    Definition source_file := "append.c"%string.
                                                    Definition normalized := true.
                                                  End Info.
                                                  
                                                  Require Import annotated_Clight.

Definition f_append_hint :=  GIVEN sh: share, GIVEN s1: list val, GIVEN s2: list val, GIVEN x: val, GIVEN y: val, 
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _x (tptr (Tstruct _list noattr)))
                                                                 (Ecast
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   (tptr tvoid))
                                                                 tint)
                                                    (Sreturn (Some (Etempvar _y (tptr (Tstruct _list noattr)))))
                                                    (Ssequence
                                                      (Sset _t
                                                        (Etempvar _x (tptr (Tstruct _list noattr))))
                                                      
    (Ssequence
      (Sassert (EX a: val, EX s1b: list val,
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y))))
    (GIVEN a: val, GIVEN s1b: list val,
    (Ssequence
      (Sassert (EX u: val,
        (PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert)
    (GIVEN u: val,
    
                                                      (Ssequence
                                                        (Sset _u
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _t (tptr (Tstruct _list noattr)))
                                                              (Tstruct _list noattr))
                                                            _tail
                                                            (tptr (Tstruct _list noattr))))
                                                        (Ssequence
                                                          (Swhile
                                                            
      (EX a: val, EX s1b: list val, EX t: val, EX u: val,
            PROP ()
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                   data_at sh t_struct_list (a,u) t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert
      
                                                            (Ebinop One
                                                              (Etempvar _u (tptr (Tstruct _list noattr)))
                                                              (Ecast
                                                                (Econst_int (Int.repr 0) tint)
                                                                (tptr tvoid))
                                                              tint)
                                                            
        (GIVEN a: val, GIVEN s1b: list val, GIVEN t: val, GIVEN u: val,
        (Ssequence
            (Sassert (EX b: val, EX s1c: list val, EX z: val,
              (PROP (s1b = b :: s1c)
               LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
               SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                    data_at sh t_struct_list (a, u) t;
                    data_at sh t_struct_list (b, z) u;
                    listrep sh s1c z; listrep sh s2 y)))%assert)
          (GIVEN b: val, GIVEN s1c: list val, GIVEN z: val,
        
                                                            (Ssequence
                                                              (Sset _t
                                                                (Etempvar _u (tptr (Tstruct _list noattr))))
                                                              (Sset _u
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _t (tptr (Tstruct _list noattr)))
                                                                    (Tstruct _list noattr))
                                                                  _tail
                                                                  (tptr (Tstruct _list noattr))))
                                                              )))))
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _t (tptr (Tstruct _list noattr)))
                                                                  (Tstruct _list noattr))
                                                                _tail
                                                                (tptr (Tstruct _list noattr)))
                                                              (Etempvar _y (tptr (Tstruct _list noattr))))
                                                            (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr)))))
                                                            ))))))))).
                                                  
