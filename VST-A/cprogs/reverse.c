#include <stddef.h>

struct list {unsigned head; struct list *tail;};

struct list *reverse (struct list *p) {
  /* With sh p l, */
  /* Require
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p)
  */
  /* Ensure
          EX q: val,
	    PROP  ()
	    LOCAL (temp ret_temp q)
	    SEP   (listrep sh (rev l) q)
  */
  struct list *w, *t, *v;
  w = NULL;
  v = p;
  /* Inv
       (EX w v l1 l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert
  */
  while (v) {
    /* Assert
         (EX t x l2',
	    PROP  (l2 = x :: l2')
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert
    */
    t = v->tail;
    v->tail = w;
    w = v;
    v = t;
  }
  return w;
}
