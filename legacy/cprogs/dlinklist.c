#include <stddef.h>
#include <limits.h>
struct list {
  unsigned int data;
  struct list * next;
  struct list * prev;
};

unsigned sumlist (struct list *p) {
  //@ With (sigma : list Z)(p: val),
  /*@ Require 
     PROP  ()
     LOCAL (temp _p p)
     SEP   (listrep sigma p) */
  /*@ Ensure
	 PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (sum_Z sigma))))
     SEP   (listrep sigma p) */
  unsigned s = 0;
  struct list *t = p;
  unsigned h;
  /*@ Inv
	 (EX (s1: list Z)(s2: list Z)(t:val)(s:val),
     PROP (sigma=s1++s2)
     LOCAL (temp _t t; temp _s (Vint( Int.repr(sum_Z s1)));temp _p p)
     SEP (lseg_pre s1 p t nullval s;listrep_pre s2 t s))
	*/
  while (t) {
	  /*@ Assert
	 ( EX (s2: list Z)(z:Z)(y:val),
     PROP (sigma=s1++z::s2)
     LOCAL (temp _t t; temp _s (Vint( Int.repr(sum_Z s1)));temp _p p)
     SEP (lseg_pre s1 p t nullval s;data_at Tsh t_struct_list (Vint (Int.repr z), (y, s)) t;listrep_pre s2 y t))%assert
	 */
     h = t->data;
     t = t->next;
     s = s + h;
  }
  return s;
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
  /*@ Inv (EX (s1: list Z)(s2: list Z)(t:val)(s:val),
     PROP (sigma=s1++s2;0<=min_Z s1<=Int.max_unsigned)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(min_Z s1)));temp _p p)
     SEP (lseg_pre s1 p t nullval s;listrep_pre s2 t s))%assert */
  while (t) {
	  /*@ Assert (EX (s2': list Z)(z:Z)(y:val),
     PROP (sigma=s1++z::s2';0<=min_Z s1<=Int.max_unsigned;0<=z<=Int.max_unsigned)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(min_Z s1)));temp _p p)
     SEP (lseg_pre s1 p t nullval s;data_at Tsh t_struct_list (Vint (Int.repr z), (y, s)) t;listrep_pre s2' y t))%assert */
     h = t->data;
     t = t->next;
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
  /*@ Inv (EX (s1: list Z)(s2: list Z)(t:val)(s:val),
     PROP (sigma=s1++s2;0<=max_Z s1<=Int.max_unsigned)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(max_Z s1)));temp _p p)
     SEP (lseg_pre s1 p t nullval s;listrep_pre s2 t s))%assert */
  while (t) {
	  /*@ Assert (EX (s2': list Z)(z:Z)(y:val),
     PROP (sigma=s1++z::s2';0<=max_Z s1<=Int.max_unsigned;0<=z<=Int.max_unsigned)
     LOCAL (temp _t t; temp _s (Vint(Int.repr(max_Z s1)));temp _p p)
     SEP (lseg_pre s1 p t nullval s;data_at Tsh t_struct_list (Vint (Int.repr z), (y, s)) t;listrep_pre s2' y t))%assert */
     h = t->data;
     t = t->next;
     if(h>s)
     s=h;
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
  /*@ Assert
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (listrep_pre s1 x nullval; listrep s2 y)
	*/
  if (x==NULL)
    return y;
  else {
    t = x;
	/*@ Assert
	(EX (z:Z)(s1':list Z)(w:val),
	PROP (s1=z::s1' )  
	LOCAL (temp _t x; temp _x x; temp _y y)  
	SEP (listrep_pre s1' w x;data_at Tsh t_struct_list (Vint (Int.repr z), (w,nullval)) x; listrep_pre s2 y nullval))%assert
	*/
    u = t->next;
	/*@ Inv
	(EX p:val,EX q:val,EX s3: list Z,EX s4:list Z,EX j:Z,EX t:val,
     PROP (s3++[j]++s4=z::s1';s1=z::s1')
     LOCAL (temp _u p; temp _t q;temp _x x;temp _y y)
     SEP (lseg_pre s3 x q nullval t;listrep_pre s4 p q;data_at Tsh t_struct_list (Vint (Int.repr j), (p,t)) q; listrep_pre s2 y nullval))%assert */
    while (u!=NULL) {
      t = u;
	  /*@ Assert
	(EX (z0:Z)(s4':list Z)(y':val)(k:val),
     PROP (s3++[j]++z0::s4'=z::s1')
     LOCAL (temp _u p; temp _t p;temp _x x;temp _y y)
     SEP (lseg_pre s3 x q nullval k;listrep_pre s4' y' p; data_at Tsh t_struct_list (Vint (Int.repr z0), (y',q)) p  ;
	 data_at Tsh t_struct_list (Vint (Int.repr j), (p,k)) q; listrep_pre s2 y nullval))%assert
	*/
      u = t->next;
    }
    t->next = y;
	if(y!= NULL){
		/*@ Assert
	(EX p:val,EX q:val,EX s3: list Z,EX s4:list Z,EX j:Z,EX t:val,EX r:Z,EX s2':list Z,EX i:val,
     PROP (s3++[j]++s4=z::s1';s1=z::s1';s2=r::s2')
     LOCAL (temp _u nullval; temp _t q;temp _x x;temp _y y)
     SEP (lseg_pre s3 x q nullval t;listrep_pre s4 nullval q;data_at Tsh t_struct_list (Vint (Int.repr j), (y,t)) q; 
	 data_at Tsh t_struct_list (Vint (Int.repr r), (i,nullval)) y ;listrep_pre s2' i y))%assert */
	y->prev = t;
	}
    return x;
  }
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
  /*@ Inv
  (EX s1: list Z, EX s2 : list Z, 
    EX w: val, EX v: val,
     PROP (sigma = rev s1 ++ s2)
     LOCAL (temp _w w; temp _v v)
     SEP (listrep_pre s1 w v; listrep_pre s2 v w))*/
  while (v) {
	 /*@ Assert
  (EX (k:val)(z:Z)(s2':list Z),
     PROP (sigma = rev s1 ++ z::s2')
     LOCAL (temp _w w; temp _v v)
     SEP (listrep_pre s1 w v;data_at Tsh t_struct_list (Vint (Int.repr z), (k,w)) v  ; listrep_pre s2' k v))%assert*/ 
    t = v->next;
    v->next = w;
	v->prev = t;
    w = v;
    v = t;
  }
  return w;
}

struct list *find(struct list* p,unsigned n){
	//@ With (sigma:list Z)(p:val)(t:Z),
	/*@ Require
	PROP (In t sigma)
     LOCAL (temp _p p;temp _n (Vint (Int.repr t)))
     SEP (listrep sigma p ) */
	 /*@ Ensure
	 EX s1:list Z,EX s2:list Z,EX q:val,EX s:val,EX r:val,EX w:Z,
     PROP (Int.repr w=Int.repr t;sigma=s1++[w]++s2;forall a,In a s1->Int.repr a<>Int.repr t) 
     LOCAL (temp ret_temp q) 
     SEP (lseg_pre s1 p q nullval s;lseg_pre [w] q r s q;listrep_pre s2 r q) */
	/*@ Assert (EX (s1 s2 : list Z) (u q r : val) (w : Z),
	PROP ( )
	LOCAL (temp _t p; temp _p p; temp _n (Vint (Int.repr t)))
	SEP (!! (forall a : Z, In a s1 -> Int.repr a <> Int.repr t) &&
        !! (Int.repr w = Int.repr t /\ sigma = s1 ++ [w] ++ s2) && lseg_pre s1 p u nullval q *
        lseg_pre [w] u r q u * listrep_pre s2 r u)) */
	struct list *t=p;
	/*@ Inv
	(
     EX a:val,EX s3:list Z,EX s4:list Z,EX b:val,
     PROP (s1++[w]=s3 ++ s4;forall a:Z,In a s1->Int.repr a<>Int.repr t;s4<>nil)
     LOCAL (temp _t a; temp _p p; temp _n (Vint (Int.repr t)))
     SEP (lseg_pre s3 p a nullval b;lseg_pre s4 a r b u;
   listrep_pre s2 r u))%assert */
	while(t){
		/*@ Assert
	(
     EX (i:Z)(k:val)(s4':list Z),
     PROP (s1++[w]=s3 ++ i::s4';forall a:Z,In a s1->Int.repr a<>Int.repr t;i::s4<>nil)
     LOCAL (temp _t a; temp _p p; temp _n (Vint (Int.repr t)))
     SEP (lseg_pre s3 p a nullval b;data_at Tsh t_struct_list (Vint (Int.repr i), (k,b)) a  ;lseg_pre s4' k r a u;
   listrep_pre s2 r u))%assert */
		if(t->data==n)
			return t;
		else
		t=t->next;
	}
	return NULL;
}


#if 0
struct list* Delete(struct list* p,struct list* del){
	if(p){
		if(del==p){
			p->next->prev=NULL;
			return p->next;
		}
		else{
			if(del){
				del->prev->next=del->next;
				if(del->next)
				del->next->prev=del->prev;
			}
		}
	}
	return p;
}
#endif
struct list* findprev(struct list*q,struct list* p){
	//@With (s1 : list Z)(s2:list Z)(p: val)(q:val)(t:val)(z:Z)(r:val),
  /*@ Require
     PROP ()
     LOCAL (temp _p p;temp _q q)
     SEP (lseg_pre s1 q p nullval t;lseg_pre [z] p r t p;listrep_pre s2 r p)*/
  /*@ Ensure
     PROP () 
     LOCAL (temp ret_temp t)
     SEP (lseg_pre s1 q p nullval t;lseg_pre [z] p r t p;listrep_pre s2 r p)
	*/
	/*@ Assert
     PROP ()
     LOCAL (temp _p p;temp _q q)
     SEP (lseg_pre s1 q p nullval t;data_at Tsh t_struct_list (Vint (Int.repr z), (r,t)) p ;listrep_pre s2 r p)*/
	return p->prev;
}
struct list* findnext(struct list* q,struct list* p){
	 //@With (s1 : list Z)(s2:list Z)(p: val)(q:val)(t:val)(z:Z)(r:val),
  /*@ Require
     PROP ()
     LOCAL (temp _p p;temp _q q)
     SEP (lseg_pre s1 q p nullval t;lseg_pre [z] p r t p;listrep_pre s2 r p)*/
  /*@ Ensure
     PROP () 
     LOCAL (temp ret_temp r)
     SEP (lseg_pre s1 q p nullval t;lseg_pre [z] p r t p;listrep_pre s2 r p)
	*/
	/*@ Assert
     PROP ()
     LOCAL (temp _p p;temp _q q)
     SEP (lseg_pre s1 q p nullval t;data_at Tsh t_struct_list (Vint (Int.repr z), (r,t)) p ;listrep_pre s2 r p)*/
	return p->next;
}