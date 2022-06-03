#include <stddef.h>

struct list {int head; struct list *tail;};

struct list *append (struct list *x, struct list *y) {
  /*@ With sh x y s1 s2, */
  /*@ Require
       PROP(writable_share sh)
       LOCAL (temp _x x; temp _y y)
       SEP (listrep sh s1 x; listrep sh s2 y)
  */
  /*@ Ensure
      EX r: val,
       PROP()
       LOCAL(temp ret_temp r)
       SEP (listrep sh (s1++s2) r)
  */
  struct list *t, *u;
  if (x==NULL)
    return y;
  else {
    t = x;
    /*@ Assert (EX a s1b, (
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y))))
    */
    /*@ Assert (EX u,
        (PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert
    */
    u = t->tail;
    /*@ Inv
    (EX a s1b t u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert
    */
    while (u!=NULL) {
      /*@ Assert (EX b s1c z,
            (PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert
      */
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}
