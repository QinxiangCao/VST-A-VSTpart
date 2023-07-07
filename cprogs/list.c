struct list {
  int head;
  struct list *tail;
};

struct queue {
  struct list * l1;
  struct list * l2;
};

struct list * malloc_list_cell(void)
  /*@ Require emp
      Ensure store_list_cell_(__return)
   */
  ;

void free_list_cell(struct list * p)
  /*@ Require store_list_cell_(p)
      Ensure emp
   */
  ;

struct list * * malloc_list_2p(void)
  /*@ Require emp
      Ensure exists p, store_list_ptr(__return, p)
   */
  ;

void free_list_2p(struct list * * p2)
  /*@ Require store_list_ptr_(p2)
      Ensure emp
   */
  ;

struct list *reverse(struct list *p) {
  /*@ With l
      Require listrep(l, p)
      Ensure listrep(rev(l), __return)
   */
  struct list *w, *t, *v;
  w = (void *)0;
  v = p;
  /*@ Inv
        exists l1 l2,
          l == rev(l1) ++ l2 &&
          listrep(l1, w) * listrep(l2, v)
   */
  while (v) {
    t = v->tail;
    v->tail = w;
    w = v;
    v = t;
  }
  return w;
}

struct list *append(struct list *x, struct list *y) {
  /*@ With s1 s2
      Require listrep(s1, x) * listrep(s2, y)
      Ensure listrep(s1 ++ s2, __return)
  */
  struct list *t, *u;
  if (x == (void *)0) {
    return y;
  } else {
    u = x->tail;
    if (u == (void *)0) {
      x->tail = y;
      return x;
    }
    t = x;
    u = t->tail;
    /*@ Inv
          exists s1a b s1c,
            s1a ++ b :: s1c == s1 &&
            lseg(s1a, x, t) *
            store_list_cell(t, b, u) *
            listrep(s1c, u) * listrep(s2, y)
    */
    while (u != (void *)0) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}

struct list *append_2p(struct list *x, struct list *y) {
  /*@ With s1 s2
      Require listrep(s1, x) * listrep(s2, y)
      Ensure listrep(s1 ++ s2, __return)
  */
  struct list * * t, * * px;
  px = malloc_list_2p();
  t = px;
  * t = x;
  /*@ Inv
        exists s1a s1b u,
          s1a ++ s1b == s1 &&
          lbseg(s1a, px, t) *
          store_list_ptr(t, u) *
          listrep(s1b, u) * listrep(s2, y)
  */
  while (* t != (void *) 0) {
    t = &((*t) -> tail);
  }
  * t = y;
  x = * px;
  free_list_2p(px);
  return x;
}

struct list *append2(struct list *x, struct list *y) {
  /*@ With s1 s2
      Require listrep(s1, x) * listrep(s2, y)
      Ensure listrep(s1 ++ s2, __return)
  */
  struct list *t, *u;
  if (x == (void *)0) {
    return y;
  } else {
    u = x->tail;
    if (u == (void *)0) {
      x->tail = y;
      return x;
    }
    t = x;
    u = t->tail;
    /*@ Inv
          exists a s1b,
            listrep(a :: s1b ++ s2, t) -* listrep(s1 ++ s2, x) *
            store_list_cell(t, a, u) *
            listrep(s1b, u) * listrep(s2, y)
    */
    while (u != (void *)0) {
      t = u;
      u = t->tail;
    }
    t->tail = y;
    return x;
  }
}

struct list *rev_append(struct list *p, struct list *q) {
  /*@ With l1 l2
      Require listrep(l1, p) * listrep(l2, q)
      Ensure listrep(rev(l1) ++ l2, __return)
  */
  struct list *w, *t, *v;
  if (! p) {
    return q;
  }
  w = p;
  v = p->tail;
  p->tail = (void *)0;
  /*@ Inv
        exists a l1b l1c,
          l1 == a :: rev(l1b) ++ l1c &&
          store_list_cell(p, a, NULL) *
          lseg(l1b, w, p) *
          listrep(l1c, v) * listrep(l2, q)
  */
  while (v) {
    t = v->tail;
    v->tail = w;
    w = v;
    v = t;
  }
  p->tail = q;
  return w;
}

int max(struct list *p) {
  /*@ With l p0
      Require all_nonneg(l) && p == p0 && listrep(l, p0)
      Ensure __return == Vint(IntRepr(max(l))) && listrep(l, p0)
  */
  int r;
  r = 0;
  /*@ Inv
        exists l1 l2 r0,
          all_nonneg(l2) &&
          l == l1 ++ l2 &&
          max(l) == max_aux(l2, r0) &&
          0 <= r0 && r0 <= INT_MAX &&
          r == Vint(IntRepr(r0)) &&
          lseg(l1, p0, p) * listrep(l2, p)
  */
  while (p) {
    if (p -> head > r) {
      r = p -> head;
    }
    p = p -> tail;
  }
  return r;
}

void push(struct list * * p, int x) {
  /*@ With l x0 p0 q
      Require p == p0 && x == Vint (IntRepr(x0)) && store_list_ptr(p0, q) * listrep(l, q)
      Ensure exists q0, store_list_ptr(p0, q0) * listrep(x0 :: l, q0)
  */
  struct list * px;
  px = malloc_list_cell();
  px -> head = x;
  px -> tail = * p;
  * p = px;
}

int pop(struct list * * p) {
  /*@ With l x0 p0 q
      Require p == p0 && store_list_ptr(p0, q) * listrep(x0 :: l, q)
      Ensure exists q0, __return == Vint(IntRepr(x0)) && store_list_ptr(p0, q0) * listrep(l, q0)
  */
  struct list * px;
  int x;
  px = * p;
  x = px -> head;
  * p = px -> tail;
  free_list_cell(px);
  return x;
}

void enqueue(struct queue * l, int x) {
  /*@ With s l0 x0
      Require l == l0 && x == Vint (IntRepr (x0)) && qrep(s, l0)
      Ensure qrep(s ++ singleton(x0), l0)
   */
  push(&(l -> l2), x);
}

int dequeue(struct queue * l) {
  /*@ With s l0 x0
      Require l == l0 && qrep(x0 :: s, l0)
      Ensure __return == Vint (IntRepr(x0)) && qrep(s, l0)
   */
  if (l -> l1 == (void *) 0) {
    l -> l1 = reverse(l -> l2);
    l -> l2 = (void *) 0;
  }
  return pop(&(l -> l1));
}

struct list * merge(struct list * x, struct list * y) {
  /*@ With s1 s2
      Require all_nonneg(s1) && all_nonneg(s2) &&
              listrep(s1, x) * listrep(s2, y)
      Ensure exists s3,
              merge_rel(s1, s2, s3) &&
              listrep(s3, __return)
  */
  struct list * * pret, * * t, * ret;
  pret = malloc_list_2p();
  t = pret;
  /*@ Inv
        exists l1 l2 l3 u,
          all_nonneg(l1) && all_nonneg(l2) &&
          merge_steps(s1, s2, nil, l1, l2, l3) &&
          lbseg(l3, pret, t) * listrep(l1, x) * listrep(l2, y) *
          store_list_ptr(t, u)
  */
  while (1) {
    if (x == (void *)0) {
      * t = y;
      break;
    }
    if (y == (void *)0) {
      * t = x;
      break;
    }
    if (x -> head < y -> head) {
      * t = x;
      t = &(x -> tail);
      x = x -> tail;
    }
    else {
      * t = y;
      t = &(y -> tail);
      y = y -> tail;
    }
  }
  ret = * pret;
  free_list_2p(pret);
  return ret;
}

void split_rec(struct list * x, struct list * * p, struct list * * q) {
  /*@ With l l1 l2 x0 ptr_p ptr_q p0 q0
      Require x == x0 && p == ptr_p && q == ptr_q &&
              all_nonneg(l) && all_nonneg(l1) && all_nonneg(l2) &&
              store_list_ptr(ptr_p, p0) * store_list_ptr(ptr_q, q0) *
              listrep(l, x0) * listrep(l1, p0) * listrep(l2, q0)
      Ensure exists s1 s2 p0 q0,
              split_rec(l, l1, l2, s1, s2) &&
              store_list_ptr(ptr_p, p0) * store_list_ptr(ptr_q, q0) *
              listrep(s1, p0) * listrep(s2, q0)
  */
  if (x == (void *)0) {
    return;
  }
  else {
    struct list * t;
    t = x -> tail;
    x -> tail = * p;
    * p = x;
    split_rec(t, q, p);
  }
}

struct list * merge_sort_rec(struct list * x, struct list * * p, struct list * * q) {
  /*@ With l x0 ptr_p ptr_q
      Require x == x0 && p == ptr_p && q == ptr_q &&
              all_nonneg(l) &&
              store_list_ptr_(ptr_p) * store_list_ptr_(ptr_q) *
              listrep(l, x0)
      Ensure exists l0,
              merge_sort(l, l0) &&
              store_list_ptr_(ptr_p) * store_list_ptr_(ptr_q) *
              listrep(l0, __return)
  */
  struct list * p1, * q1;
  * p = (void *)0;
  * q = (void *)0;
  split_rec(x, p, q);
  p1 = * p;
  q1 = * q;
  if (q1 == (void *)0) {
    return p1;
  }
  p1 = merge_sort_rec(p1, p, q);
  q1 = merge_sort_rec(q1, p, q);
  return merge(p1, q1);
}

struct list * merge_sort(struct list * x) {
  /*@ With l x0
      Require x == x0 && all_nonneg(l) &&
              listrep(l, x0)
      Ensure exists l0,
              Permutation(l, l0) && increasing(l0) &&
              listrep(l0, __return)
  */
  struct list * * p, * * q;
  p = malloc_list_2p();
  q = malloc_list_2p();
  x = merge_sort_rec(x, p, q);
  free_list_2p(p);
  free_list_2p(q);
  return x;
}

struct list *reverse1(struct list *p) {
  /*@ With l
      Require listrep(l, p)
      Ensure listrep(rev(l), __return)
  */
  struct list *w, *t, *v;
  w = (void *)0;
  v = p;
  /*@ Inv
        exists l1 l2,
          l == rev(l1) ++ l2 &&
          listrep(l1, w) * listrep(l2, v)
  */
  while (v) {
    /*@ Assert
          exists u l1 x l2,
            l == rev(l1) ++ x :: l2 &&
            store_list_cell(v, x, u) * listrep(l1, w) * listrep(l2, u)
    */
    t = v->tail;
    v->tail = w;
    w = v;
    v = t;
  }
  return w;
}

struct list *reverse2(struct list *p) {
  /*@ With l
      Require listrep(l, p)
      Ensure listrep(rev(l), __return)
  */
  struct list *w, *t, *v;
  w = (void *)0;
  v = p;
  while (v) {
    /*@ Assert
          exists l1 x l2 u,
            l == rev(l1) ++ x :: l2 &&
            store_list_cell(v, x, u) * listrep(l1, w) * listrep(l2, u)
     */
    t = v->tail;
    v->tail = w;
    w = v;
    v = t;
  }
  return w;
}

struct list * merge_alter_proof(struct list * x, struct list * y) {
  /*@ With s1 s2
      Require increasing(s1) && all_nonneg(s1) &&
              increasing(s2) && all_nonneg(s2) &&
              listrep(s1, x) * listrep(s2, y)
      Ensure exists s3,
        increasing(s3) && Permutation(s1 ++ s2, s3) &&
        listrep(s3, __return)
  */
  struct list * * pret, * * t, * ret;
  pret = malloc_list_2p();
  t = pret;
  /*@ Inv
        exists l1 l2 l3 u,
          increasing(l3 ++ l1) && all_nonneg(l1) &&
          increasing(l3 ++ l2) && all_nonneg(l2) &&
          Permutation(s1 ++ s2, l3 ++ l1 ++ l2) &&
          lbseg(l3, pret, t) * listrep(l1, x) * listrep(l2, y) *
          store_list_ptr(t, u)
  */
  while (1) {
    if (x == (void *)0) {
      * t = y;
      break;
    }
    if (y == (void *)0) {
      * t = x;
      break;
    }
    if (x -> head < y -> head) {
      * t = x;
      t = &(x -> tail);
      x = x -> tail;
    }
    else {
      * t = y;
      t = &(y -> tail);
      y = y -> tail;
    }
  }
  ret = * pret;
  free_list_2p(pret);
  return ret;
}

struct list * merge_alter_spec(struct list * x, struct list * y) {
  /*@ With s1 s2
      Require increasing(s1) && all_nonneg(s1) &&
              increasing(s2) && all_nonneg(s2) &&
              listrep(s1, x) * listrep(s2, y)
      Ensure exists s3,
        increasing(s3) && Permutation(s1 ++ s2, s3) &&
        listrep(s3, __return)
  */
  struct list * * pret, * * t, * ret;
  pret = malloc_list_2p();
  t = pret;
  /*@ Inv
        exists l1 l2 l3 u,
          increasing(s1) && all_nonneg(l1) &&
          increasing(s2) && all_nonneg(l2) &&
          merge_steps(s1, s2, nil, l1, l2, l3) &&
          lbseg(l3, pret, t) * listrep(l1, x) * listrep(l2, y) *
          store_list_ptr(t, u)
  */
  while (1) {
    if (x == (void *)0) {
      * t = y;
      break;
    }
    if (y == (void *)0) {
      * t = x;
      break;
    }
    if (x -> head < y -> head) {
      * t = x;
      t = &(x -> tail);
      x = x -> tail;
    }
    else {
      * t = y;
      t = &(y -> tail);
      y = y -> tail;
    }
  }
  ret = * pret;
  free_list_2p(pret);
  return ret;
}
