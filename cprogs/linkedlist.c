#include <stddef.h>
struct list {
  unsigned int head;
  struct list * tail;
};

unsigned sumlist (struct list *p) {
	//@ With (sigma : list Z) (p: val),
	/*@ Require
     PROP  ()
     LOCAL (temp _p p)
     SEP   (listrep sigma p)
    */
	/*@ Ensure
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr(sum_Z sigma))))
     SEP   (listrep sigma p)
	*/
  unsigned h;
  unsigned s=0 ;

  struct list *t=p;

  
	/*@ Inv
	 (EX (s1: list Z)(s2: list Z)(t:val),
     PROP (sigma=s1++s2)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(sum_Z s1)));temp _p p)
     SEP (lseg s1 p t;listrep s2 t))
	 */
  while (t) {
	 /*@ Assert
	 (EX (z:Z)(s3:list Z)(y:val),
	 PROP (sigma=s1++z::s3 )
	 LOCAL (temp _t t; temp _s (Vint (Int.repr (sum_Z s1))); temp _p p)
     SEP (lseg s1 p t; data_at Tsh t_struct_list (Vint (Int.repr z), y) t ; listrep s3 y))%assert
	 */
     h = t->head;
     t = t->tail;
     s = s + h;
  }
  return s;
}

struct list *append (struct list *x, struct list *y) {
	//@ With (x: val)(y: val)(s1: list Z)(s2: list Z),
    /*@ Require
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (listrep s1 x; listrep s2 y)
	*/
    /*@ Ensure
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep (s1++s2) r)
	*/
  struct list *t, *u; 
  if (x==NULL)
    return y;
  else {
    t = x;
	/*@ Assert
	(EX (z:Z)(s1':list Z)(w:val),
	PROP (s1=z::s1')  
	LOCAL (temp _t x; temp _x x; temp _y y)  
	SEP (listrep s1' w;data_at Tsh t_struct_list (Vint (Int.repr z), w) x; listrep s2 y))%assert
	*/
    u = t->tail;
	/*@ Inv
	(EX p:val,EX q:val,EX s3: list Z,EX s4:list Z,EX j:Z,
     PROP (s3++[j]++s4=z::s1';s1=z::s1')
     LOCAL (temp _u p; temp _t q;temp _x x;temp _y y)
     SEP (lseg s3 x q;listrep s4 p ;data_at Tsh t_struct_list (Vint (Int.repr j), p) q; listrep s2 y))%assert
	*/
    while (u!=NULL) {
      t = u;
	  /*@ Assert
	(EX (z0:Z)(s4:list Z)(y0:val),
     PROP (s3++[j]++z0::s4=z::s1';s1=z::s1')
     LOCAL (temp _u p; temp _t p;temp _x x;temp _y y)
     SEP (lseg s3 x q;listrep s4 y0; data_at Tsh t_struct_list (Vint (Int.repr z0), y0) p  ;data_at Tsh t_struct_list (Vint (Int.repr j), p) q; listrep s2 y))%assert
	*/
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}	

void append2(struct list * * x, struct list * y) {
	//@ With (x: val)(y: val)(s1: list Z)(s2: list Z)(p :val),
	/*@ Require
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (listrep s1 p ;(data_at Tsh (tptr t_struct_list) p x); listrep s2 y)
	*/
	/*@ Ensure
     EX q:val,
     PROP()
     LOCAL()
     SEP (data_at Tsh (tptr t_struct_list) q x;listrep (s1++s2) q)
	*/
  struct list * h;
  h = * x;
  /*@ Inv
  (EX t:val,EX s3: list Z,EX s4:list Z,EX s:val,
     PROP (s3++s4=s1)
     LOCAL (temp _x s;temp _y y;temp _h t)
     SEP ( data_at Tsh (tptr t_struct_list) t s;
     lbseg s3 x s ;listrep s4 t; listrep s2 y ))%assert
  */
  while (h != NULL) {
	/*@ Assert(
	EX (z:Z)(s4':list Z)(u:val),
	PROP (s3++z::s4'=s1;offset_val 4 t=field_address t_struct_list [StructField _tail] t )
	LOCAL (temp _x s; temp _y y; temp _h t)
	SEP (data_at Tsh (tptr t_struct_list) t s; lbseg s3 x s;data_at Tsh t_struct_list (Vint (Int.repr z), u) t;listrep s4' u; listrep s2 y))%assert
	*/
    x = & (h -> tail);
    h = * x;
  }
  * x = y;
}

struct list* append3 (struct list *x, struct list *y) {
	//@ With (x: val)(y: val)(s1: list Z)(s2: list Z),
    /*@ Require
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (listrep s1 x; listrep s2 y)
	*/
	/*@ Ensure
     EX q:val,
     PROP()
     LOCAL(temp ret_temp q)
     SEP (listrep (s1++s2) q)
	 */
  struct list** begin;
  struct list ** h;
  struct list *fake;
  h=&fake;
  begin=h;
  *h=x;
  /*@Inv (EX t:val,EX s3: list Z,EX s4:list Z,EX s:val,EX v_fake:val,
     PROP (s3++s4=s1)
     LOCAL (temp _x t;temp _y y;temp _h s;temp _begin v_fake;lvar _fake (tptr (Tstruct _list noattr)) v_fake)
     SEP ( data_at Tsh (tptr t_struct_list) t s; 
     lbseg s3 v_fake s ;listrep s4 t; listrep s2 y ))%assert */
  while (x != NULL) {
  /*@Assert (EX s4':list Z,EX k:val,EX z:Z,
     PROP (s3++z::s4'=s1)
     LOCAL (temp _x t;temp _y y;temp _h s;temp _begin v_fake;lvar _fake (tptr (Tstruct _list noattr)) v_fake)
     SEP ( data_at Tsh (tptr t_struct_list) t s; 
     lbseg s3 v_fake s ;listrep s4' k;data_at Tsh t_struct_list (Vint (Int.repr z), k) t; listrep s2 y ))%assert */
    h = & (x -> tail);
	/*@ Assert 
	(EX (u:val),
	PROP ( )
   LOCAL (temp _h (field_address t_struct_list [StructField _tail] t);
   temp _x t; temp _y y; temp _begin v_fake;
   lvar _fake (tptr (Tstruct _list noattr)) v_fake)
   SEP (data_at Tsh (tptr t_struct_list) t u; lbseg s3 v_fake u;
   field_at Tsh t_struct_list [StructField _head] (Vint (Int.repr z)) t;
   field_at Tsh t_struct_list [StructField _tail] k t; 
   listrep s4' k; listrep s2 y))%assert */
    x = * h;
  }
  /*@ Assert
  (EX (s:val)(t:val)(v_fake:val)(s3:list Z)(s4:list Z),
   PROP (s3++s4=s1;t=nullval)
   LOCAL (temp _x t; temp _y y; temp _h s; temp _begin v_fake;
   lvar _fake (tptr (Tstruct _list noattr)) v_fake)
   SEP (data_at Tsh (tptr t_struct_list) t s; lbseg s3 v_fake s; 
   listrep s4 t; listrep s2 y))%assert
   */
  * h = y;
  /*@ Assert
  (EX (u:val),PROP ( s3++s4=s1;t=nullval)
   LOCAL (temp _x nullval; temp _y y; temp _h s; temp _begin v_fake;
   lvar _fake (tptr (Tstruct _list noattr)) v_fake)
   SEP (listrep (s3 ++ s2) u; data_at Tsh (tptr t_struct_list) u v_fake;
   listrep s4 nullval))%assert
   */
  return *begin;
}


struct list *reverse (struct list *p) {
	//@ With (sigma : list Z) (p: val),
  /*@ Require
     PROP ()
     LOCAL (temp _p p)
     SEP (listrep sigma p)
	 */
	/*@ Ensure
	 EX q:val,
     PROP () 
	 LOCAL (temp ret_temp q)
     SEP (listrep(rev sigma) q)
	*/
  struct list *w, *t, *v;
  w = NULL;
  v = p;
  /*@ Inv (EX s1: list Z, EX s2 : list Z, 
    EX w: val, EX v: val,
     PROP (sigma = rev s1 ++ s2)
     LOCAL (temp _w w; temp _v v)
     SEP (listrep s1 w; listrep s2 v))%assert */
  while (v) {
  /*@ Assert (EX (t:Z)(s2:list Z)(y:val),
     PROP (sigma = rev s1 ++ t::s2)
     LOCAL (temp _w w; temp _v v)
     SEP (listrep s1 w; listrep s2 y;data_at Tsh t_struct_list (Vint (Int.repr t), y) v))%assert */
    t = v->tail;
    v->tail = w;
    w = v;
    v = t;
  }
  return w;
}


unsigned minlist(struct list *p) {
	//@ With (sigma : list Z) (p: val),
  /*@ Require
     PROP  (forall a:Z,In a sigma->0<=a<=Int.max_unsigned)
     LOCAL (temp _p p)
     SEP   (listrep sigma p)
	 */
	/*@ Ensure
     PROP  ()
     LOCAL (temp ret_temp (Vint(Int.repr  (min_Z sigma))))
     SEP   (listrep sigma p)
	 */
  unsigned s = ~0;
  struct list *t = p;
  unsigned h;
  /*@ Inv (EX s1: list Z, EX s2: list Z,
    EX t:val,
     PROP (sigma=s1++s2;0<=min_Z s1<=Int.max_unsigned)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(min_Z s1)));temp _p p)
     SEP (lseg s1 p t;listrep s2 t))%assert */
  while (t) {
	  /*@ Assert (EX s2': list Z, EX z:Z, EX y:val,
     PROP (sigma=s1++z::s2';0<=min_Z s1<=Int.max_unsigned)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(min_Z s1)));temp _p p)
     SEP (data_at Tsh t_struct_list (Vint (Int.repr z), y) t;lseg s1 p t;listrep s2' y))%assert */
     h = t->head;
     t = t->tail;
     if(h<s)
     s=h;
  }
  return s;
}

unsigned maxlist(struct list *p) {
  //@ With (sigma : list Z) (p: val),
  /*@ Require
     PROP  (forall a:Z,In a sigma->0<=a<=Int.max_unsigned )
     LOCAL (temp _p p)
     SEP   (listrep sigma p)
  */
  /*@ Ensure
     PROP  ()
     LOCAL (temp ret_temp (Vint(Int.repr  (max_Z sigma))))
     SEP   (listrep sigma p)
  */
  unsigned s = 0;
  struct list *t = p;
  unsigned h;
  /*@ Inv (EX s1: list Z, EX s2: list Z,
    EX t:val,
     PROP (sigma=s1++s2;0<=max_Z s1<=Int.max_unsigned)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(max_Z s1)));temp _p p)
     SEP (lseg s1 p t;listrep s2 t))%assert */
  while (t) {
	  /*@ Assert (EX s2': list Z, EX z:Z, EX y:val,
     PROP (sigma=s1++z::s2';0<=max_Z s1<=Int.max_unsigned)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(max_Z s1)));temp _p p)
     SEP (data_at Tsh t_struct_list (Vint (Int.repr z), y) t;lseg s1 p t;listrep s2' y))%assert */
     h = t->head;
     t = t->tail;
     if(h>s)
     s=h;
  }
  return s;
} 
