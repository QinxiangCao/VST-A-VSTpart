struct tree {
  int key;
  void *value;
  struct tree *left;
  struct tree *right;
};

struct tree * malloc_tree_node(void)
  /*@ Require emp
      Ensure store_tree_cell_(__return)
   */;

void free_tree_node(struct tree * ptr)
  /*@ Require store_tree_cell_(ptr)
      Ensure emp
   */;

void *lookup(int x, struct tree *p) {
  /*@ With n t p_old
      Require
        x == Vint(IntRepr(n)) &&
        INT_MIN <= n && n <= INT_MAX &&
        p == p_old &&
        tree_rep(t, p)
      Ensure
        __return == lookup(n, t) &&
        tree_rep(t, p_old)
   */
  int y;
  void *v;

  /*@ Inv
        exists t1,
          x == Vint(IntRepr(n)) &&
          INT_MIN <= n && n <= INT_MAX &&
          lookup(n, t1) == lookup(n, t) &&
          tree_rep(t1, p) -* tree_rep(t, p_old) *
          tree_rep(t1, p)
   */
  while (p != (void *)0) {
    y = p->key;
    if (x < y) {
      p = p->left;
    } else if (y < x) {
      p = p->right;
    } else {
      v = p->value;
      return v;
    }
  }

  return (void *)0;
}

void insert(struct tree **b, int x, void *value) {
  /*@ With t n b_old v
      Require
        x == Vint(IntRepr(n)) &&
        INT_MIN <= n && n <= INT_MAX &&
        value == v &&
        is_pointer_or_null(v) &&
        b == b_old &&
        treebox_rep(t, b)
      Ensure
        treebox_rep(insert(n, v, t), b_old)
   */
  struct tree *p;
  int y;

  /*@ Inv
        exists t1,
          x == Vint(IntRepr(n)) &&
          INT_MIN <= n && n <= INT_MAX &&
          value == v &&
          is_pointer_or_null(v) &&
          treebox_rep(insert(n, v, t1), b) -* treebox_rep(insert(n, v, t), b_old) *
          treebox_rep(t1, b)
   */
  while (1) {
    p = *b;
    if (p == (void *)0) {
      p = malloc_tree_node();
      p->key = x;
      p->value = value;
      p->left = (void *)0;
      p->right = (void *)0;
      *b = p;
      return;
    } else {
      y = p->key;
      if (x < y) {
        b = &p->left;
      } else if (y < x) {
        b = &p->right;
      } else {
        p->value = value;
        return;
      }
    }
  }
}

void pushdown_left(struct tree **b) {
  /*@ With ta tb n v t b_old
      Require
        INT_MIN <= n && n <= INT_MAX &&
        tc_val_ptr(v) &&
        b == b_old &&
        is_pointer_or_null(t) &&
        store_tree_ptr(b_old, t) *
        store_int(field_addr(t, key), n) *
        store_void_ptr(field_addr(t, value), v) *
        treebox_rep(ta, field_addr(t, left)) *
        treebox_rep(tb, field_addr(t, right))
      Ensure
        treebox_rep(pushdown_left(ta, tb), b_old)
   */
  struct tree *p, *q;
  struct tree *mid;

  /*@ Inv
      exists ta1 tb1 n1 v1,
        INT_MIN <= n && n <= INT_MAX &&
        tc_val_ptr(v) &&
        treebox_rep(T(ta1, n1, v1, tb1), b) *
        treebox_rep(pushdown_left(ta1, tb1), b) -* treebox_rep(pushdown_left(ta, tb), b_old)
   */
  while (1) {
    p = *b;
    q = p->right;
    if (q == (void*)0) {
      q = p->left;
      *b = q;
      free_tree_node(p);
      return;
    } else {
      mid = q->left;
      p->right = mid;
      q->left = p;
      *b = q;
      b = &q->left;
    }
  }
}

void delete(struct tree **b, int x) {
  /*@ With n t b_old
      Require
        x == Vint(IntRepr(n)) &&
        INT_MIN <= n && n <= INT_MAX &&
        b == b_old &&
        treebox_rep(t, b_old)
      Ensure
        treebox_rep(delete(n, t), b_old)
   */
  struct tree *p;
  int y;

  /*@ Inv
      exists t1,
        x == Vint(IntRepr(n)) &&
        INT_MIN <= n && n <= INT_MAX &&
        treebox_rep(t1, b) *
        treebox_rep(delete(n, t1), b) -* treebox_rep(delete(n, t), b_old)
   */
  while (1) {
    p = *b;
    if (p == (void *)0) {
      return;
    } else {
      y = p->key;
      if (x < y) {
        b = &p->left;
      } else if (y < x) {
        b = &p->right;
      } else {
        pushdown_left(b);
        return;
      }
    }
  }
}
