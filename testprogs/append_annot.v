Definition f_append_spec_annotation :=
  ANNOTATION_WITH  sh x y s1 s2, ((
       PROP(writable_share sh)
       LOCAL (temp _x x; temp _y y)
       SEP (listrep sh s1 x; listrep sh s2 y)),
  (
      EX r: val,
       PROP()
       LOCAL(temp ret_temp r)
       SEP (listrep sh (s1++s2) r))).

Definition f_append_spec_complex :=
  ltac:(uncurry_funcspec f_append_spec_annotation).

Definition f_append_funsig: funsig :=
  (((_x, (tptr (Tstruct _list noattr))) ::
    (_y, (tptr (Tstruct _list noattr))) :: nil),
   (tptr (Tstruct _list noattr))).

Definition append_spec :=
  ltac:(make_funcspec _append f_append_funsig f_append_spec_complex).

Definition f_append_hint :=
(GIVEN  sh x y s1 s2,
  (Ssequence
    (Sdummyassert (
       PROP(writable_share sh)
       LOCAL (temp _x x; temp _y y)
       SEP (listrep sh s1 x; listrep sh s2 y)))
    (Ssequence
      (Sdummyassert (
      EX r: val,
       PROP()
       LOCAL(temp ret_temp r)
       SEP (listrep sh (s1++s2) r)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _x (tptr (Tstruct _list noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sreturn (Some (Etempvar _y (tptr (Tstruct _list noattr)))))
            Sskip)
          (Ssequence
            (Sset _t (Etempvar _x (tptr (Tstruct _list noattr))))
            (Ssequence
              (Sassert ( (EX a s1b, (
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y))))))
              (EXGIVEN s1b
                [[(((
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y)))))]] 
                (EXGIVEN a
                  [[((EX s1b, (
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y)))))]] 
                  (Ssequence
                    (Sassert ( (EX u,
        (PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert))
                    (EXGIVEN u
                      [[(((PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert)]] 
                      (Ssequence
                        (Sset _u
                          (Efield
                            (Ederef
                              (Etempvar _t (tptr (Tstruct _list noattr)))
                              (Tstruct _list noattr)) _tail
                            (tptr (Tstruct _list noattr))))
                        (Ssequence
                          (Sloop
                            (LISingle (
    (EX a s1b t u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert))
                            (EXGIVEN u
                              [[((PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert)]] 
                              (EXGIVEN t
                                [[((EX u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert)]] 
                                (EXGIVEN s1b
                                  [[((EX t u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert)]] 
                                  (EXGIVEN a
                                    [[((EX s1b t u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert)]] 
                                    (Ssequence
                                      (Sifthenelse (Ebinop One
                                                     (Etempvar _u (tptr (Tstruct _list noattr)))
                                                     (Ecast
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr tvoid)) tint)
                                        Sskip
                                        (Ssequence Sbreak Sskip))
                                      (Ssequence
                                        (Sassert ( (EX b s1c z,
            (PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert))
                                        (EXGIVEN z
                                          [[(((PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert)]] 
                                          (EXGIVEN s1c
                                            [[((EX z,
            (PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert)]] 
                                            (EXGIVEN b
                                              [[((EX s1c z,
            (PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert)]] 
                                              (Ssequence
                                                (Sset _t
                                                  (Etempvar _u (tptr (Tstruct _list noattr))))
                                                (Ssequence
                                                  (Sset _u
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t (tptr (Tstruct _list noattr)))
                                                        (Tstruct _list noattr))
                                                      _tail
                                                      (tptr (Tstruct _list noattr))))
                                                  Sskip)))))))))))
                            Sskip)
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _t (tptr (Tstruct _list noattr)))
                                  (Tstruct _list noattr)) _tail
                                (tptr (Tstruct _list noattr)))
                              (Etempvar _y (tptr (Tstruct _list noattr))))
                            (Ssequence
                              (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr)))))
                              Sskip)))))))))))
        Sskip)))).


