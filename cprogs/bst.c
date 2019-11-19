#include <stddef.h>

extern void *mallocN (int n);
extern void freeN(void *p, int n);

struct tree {int key; void *value; struct tree *left, *right;};

typedef struct tree **treebox;

void insert (treebox p, int x, void *value){
  //@ With (p0: val) (x: nat) (v: val) (m0: total_map val),
  /*@ Require
        PROP( Int.min_signed <= Z.of_nat x <= Int.max_signed; is_pointer_or_null v)
        LOCAL(temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))); temp _value v)
        SEP (Mapbox_rep m0 p0)
  */
  /*@ Ensure
        PROP()
        LOCAL()
        SEP (Mapbox_rep (t_update m0 x v) p0)
  */
  /*@ Assert EX t0 : tree val,
        PROP ( )
        LOCAL (temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))); temp _value v)
        SEP (treebox_rep t0 p0)
  */
  struct tree *q;
  /*@ Inv EX p: val, EX t: tree val, EX P: tree val -> tree val,
        PROP(P (insert x v t) = (insert x v t0))
        LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
        SEP(treebox_rep t p;  partial_treebox_rep P p0 p)
  */
  for(;;) {
    /*@ Assert EX q : val,
          PROP ( )
          LOCAL (temp _p p; temp _x (Vint (Int.repr (Z.of_nat x))); temp _value v)
          SEP (data_at Tsh (tptr t_struct_tree) q p * tree_rep t q; partial_treebox_rep P p0 p)
    */
    q = * p;
    if (q == NULL) {
      q = (struct tree *) mallocN (sizeof * q);
      q -> key = x; q -> value = value; q -> left = NULL; q -> right = NULL;
      * p = q;
      return;
    } else {
      int y = q -> key;
      if (x < y)
	p = & q -> left;
      else if (y<x)
	p = & q -> right;
      else {
	q -> value = value;
	return;
      }
    }
  }
}

void *lookup (struct tree * p, int x) {
  void * v;
  while (p != NULL) {
    int y = p -> key;
    if (x < y)
      p = p -> left;
    else if (y<x)
      p = p -> right;
    else {
      v = p -> value;
      return v;
    }
  }
  return NULL;
}

void turn_left(treebox _l, struct tree * l, struct tree * r) {
  struct tree * mid;
  mid = r->left;
  l->right = mid;
  r->left = l;
  *_l = r;
}

void pushdown_left (treebox t) {
  struct tree *p, *q;
  for(;;) {
    p = *t;
    q = p->right;
    if (q==NULL) {
      q = p->left;
      *t = q;
      freeN(p, sizeof (*p));
      return;
    } else {
      turn_left(t, p, q);
      t = &q->left;
    }
  }
}

void delete (treebox t, int x) {
  struct tree *p;
  for(;;) {
    p = *t;
    if (p==NULL) {
      return;
    } else {
      int y = p->key;
      if (x<y)
	t= &p->left;
      else if (y<x)
	t= &p->right;
      else {
	pushdown_left(t);
	return;
      }
    }
  }
}
