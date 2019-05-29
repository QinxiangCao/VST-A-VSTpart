#define NULL 0

struct list {int head; struct list *tail;};

struct list *append (struct list *x, struct list *y) {
  /* GIVEN (sh: share) (s1: list val) (s2: list val) (x: val) (y: val), */
  struct list *t, *u;
  if (x==NULL)
    return y;
  else {
    t = x;
    /*
    (Ssequence
      (Sassert (EX a: val, EX s1b: list val,
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y))))
    (GIVEN (a: val) (s1b: list val),
    (Ssequence
      (Sassert (EX u: val,
        (PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert)
    (GIVEN u: val,
    */
    u = t->tail;
    {
      /*
      (EX a: val, EX s1b: list val, EX t: val, EX u: val,
            PROP ()
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                   data_at sh t_struct_list (a,u) t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert
      */
      while (u!=NULL) {
        /*
        (GIVEN (a: val) (s1b: list val) (t: val) (u: val),
        (Ssequence
            (Sassert (EX b: val, EX s1c: list val, EX z: val,
              (PROP (s1b = b :: s1c)
               LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
               SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                    data_at sh t_struct_list (a, u) t;
                    data_at sh t_struct_list (b, z) u;
                    listrep sh s1c z; listrep sh s2 y)))%assert)
          (GIVEN (b: val) (s1c: list val) (z: val),
        */
        t = u;
        u = t->tail;
        /*)))*/
      }
    }
    t->tail = y;
    return x;
    /*))))*/
  }
}
