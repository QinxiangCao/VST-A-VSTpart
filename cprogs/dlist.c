struct list {
  unsigned int data;
  struct list *next;
  struct list *prev;
};

struct listbox {
  struct list * head;
  struct list * tail;
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
          listrep_pre(l1, w, v) * listrep_pre(l2, v, w)
   */
  while (v) {
    t = v->next;
    v->next = w;
    v->prev = t;
    w = v;
    v = t;
  }
  return w;
}

struct list *append(struct list *x, struct list *y) {
  /*@ With l1 l2
      Require listrep(l1, x) * listrep(l2, y)
      Ensure listrep(l1 ++ l2, __return)
   */
  struct list *t, *u;
  if (x == (void *)0) {
    return y;
  } else {
    t = x;
    /*@ Assert
          exists z l3 w,
            l1 == z :: l3 && t == x &&
            listrep_pre(l3, w, x) *
            store_list_cell(x, z, w, NULL) *
            listrep_pre(l2, y, NULL)
        Given z l3
     */
    u = t->next;
    /*@ Inv
          exists l4 l5 a b,
            l4 ++ a :: l5 == z :: l3 &&
            l1 == z :: l3 &&
            lseg_pre(l4, x, t, NULL, b) *
            listrep_pre(l5, u, t) *
            store_list_cell(t, a, u, b) *
            listrep_pre(l2, y, NULL)
     */
    while (u != (void *)0) {
      t = u;
      u = t->next;
    }
    t->next = y;
    if (y != (void *)0) {
      y->prev = t;
    }
    return x;
  }
}

void enqueue(struct listbox * l, unsigned int x) {
  /*@ With s l0 x0
      Require l == l0 && x == Vint (IntRepr (x0)) && lbrep(s, l0)
      Ensure lbrep(s ++ singleton(x0), l0)
   */
  struct list * p;
  p = malloc_list_cell();
  p -> data = x;
  if (l -> head == (void *)0) {
    l -> head = p;
    l -> tail = p;
    p -> next = (void *)0;
    p -> prev = (void *)0;
  }
  else {
    l -> tail -> next = p;
    p -> prev = l -> tail;
    l -> tail = p;
    p -> next = (void *)0;
  }
}

unsigned int dequeue(struct listbox * l) {
  /*@ With s l0 x0
      Require l == l0 && lbrep(x0 :: s, l0)
      Ensure __return == Vint (IntRepr(x0)) && lbrep(s, l0)
   */
  unsigned int x;
  struct list * p;
  p = l -> head;
  x = p -> data;
  l -> head = p -> next;
  free_list_cell(p);
  if (l -> head == (void *)0) {
    l -> tail = (void *)0;
  }
  else {
    l -> head -> prev = (void *)0;
  }
  return x;
}
