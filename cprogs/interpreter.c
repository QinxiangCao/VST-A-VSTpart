enum BinOpType {
  T_PLUS, T_MINUS, T_MUL, T_DIV, T_MOD,
  T_LT, T_EQ,
  T_AND, T_OR
};

enum ExprType {
  T_CONST, T_VAR, T_BINOP,
  T_DEREF, T_MALLOC
};

enum CmdType {
  T_DECL, T_ASGN, T_SEQ,
  T_IF, T_WHILE
};

struct expr {
  enum ExprType t;
  unsigned value; // CONST
  char *name; // VAR
  enum BinOpType bop; // BINOP
  struct expr *arg1; // BINOP, DEREF
  struct expr *arg2; // BINOP
};

struct cmd {
  enum CmdType t;
  char *name; // DECL
  struct expr *arg1; // ASGN, IF, WHILE
  struct expr *arg2; // ASGN
  struct cmd *sub1; // SEQ, IF, WHILE
  struct cmd *sub2; // SEQ, IF
};

struct cont_list {
  struct cmd *c;
  struct cont_list *link;
};

struct res_prog {
  struct cmd *foc;
  struct cont_list *ectx;
};

struct hash_table;

struct memory;

void *malloc_cont_list(void)
  /*@ Require emp
      Ensure store_cont_list_(__return)
   */;

void free_cont_list(struct cont_list *p)
  /*@ Require store_cont_list_(p)
      Ensure emp
   */;

void free_cmd(struct cmd *p)
  /*@ Require store_cmd_(p)
      Ensure emp
   */;

void free_expr(struct expr *p)
  /*@ Require store_expr_(p)
      Ensure emp
   */;

void exit(int code)
  /*@ Require code == Vint(IntRepr(1)) && emp
      Ensure False && emp
   */;

unsigned hash_table_get(struct hash_table *tbl , char *k)
  /*@ With t
      Require tbl == t && hash_table_rep(t)
      Ensure tc_val_uint(__return) && hash_table_rep(t)
   */;

void hash_table_set(struct hash_table *tbl, char *k, unsigned v)
  /*@ With t
      Require tbl == t && hash_table_rep(t)
      Ensure hash_table_rep(t)
   */;

unsigned mem_alloc(struct memory *mem)
  /*@ With m
      Require mem == m && memory_rep(m)
      Ensure tc_val_uint(__return) && memory_rep(m)
   */;

unsigned mem_get(struct memory *mem, unsigned loc)
  /*@ With m
      Require mem == m && memory_rep(m)
      Ensure tc_val_uint(__return) && memory_rep(m)
   */;

void mem_set(struct memory *mem, unsigned loc, unsigned val)
  /*@ With m
      Require mem == m && memory_rep(m)
      Ensure memory_rep(m)
   */;

struct cmd *copy_cmd(struct cmd *c)
  /*@ With cmd
      Require c == cmd && cmd_rep(cmd)
      Ensure cmd_rep(cmd) * cmd_rep(__return)
   */;

void free_expr_rec(struct expr *e) {
  /*@ Require expr_rep(e)
      Ensure emp
   */
  enum ExprType t;
  struct expr *arg1, *arg2;
  t = e->t;

  if (t == T_CONST) {
    free_expr(e);
  } else if (t == T_VAR) {
    free_expr(e);
  } else if (t == T_BINOP) {
    arg1 = e->arg1;
    arg2 = e->arg2;
    free_expr(e);
    free_expr_rec(arg1);
    free_expr_rec(arg2);
  } else if (t == T_DEREF) {
    arg1 = e->arg1;
    free_expr(e);
    free_expr_rec(arg1);
  } else if (t == T_MALLOC) {
    free_expr(e);
  }

  return;
}

void free_cmd_rec(struct cmd *c) {
  /*@ Require cmd_rep(c)
      Ensure emp
   */
  enum CmdType t;
  t = c->t;
  struct expr *arg1, *arg2;
  struct cmd *sub1, *sub2;

  if (t == T_DECL) {
    free_cmd(c);
  } else if (t == T_ASGN) {
    arg1 = c->arg1;
    arg2 = c->arg2;
    free_cmd(c);
    free_expr_rec(arg1);
    free_expr_rec(arg2);
  } else if (t == T_SEQ) {
    sub1 = c->sub1;
    sub2 = c->sub2;
    free_cmd(c);
    free_cmd_rec(sub1);
    free_cmd_rec(sub2);
  } else if (t == T_IF) {
    arg1 = c->arg1;
    sub1 = c->sub1;
    sub2 = c->sub2;
    free_cmd(c);
    free_expr_rec(arg1);
    free_cmd_rec(sub1);
    free_cmd_rec(sub2);
  } else if (t == T_WHILE) {
    arg1 = c->arg1;
    sub1 = c->sub1;
    free_cmd(c);
    free_expr_rec(arg1);
    free_cmd_rec(sub1);
  }
  return;
}

struct cont_list *CL_Cons(struct cmd *c, struct cont_list *cont) {
  /*@ Require cmd_rep(c) * cont_list_rep(cont)
      Ensure cont_list_rep(__return)
   */

  struct cont_list *res;
  res = malloc_cont_list();
  res->c = c;
  res->link = cont;
  return res;
}

unsigned
eval(struct hash_table *state,
     struct memory *mem,
     struct expr *e) {
  /*@ With st m expr
      Require
        state == st && mem == m && e == expr &&
        hash_table_rep(st) * memory_rep(m) * expr_rep(expr)
      Ensure
        tc_val_uint(__return) &&
        hash_table_rep(st) * memory_rep(m) * expr_rep(expr)
   */

  enum ExprType et;
  et = e->t;
  unsigned val1, val2;
  struct expr *arg1, *arg2;
  unsigned res;

  if (et == T_CONST) {
    res = e->value;
    return res;
  } else if (et == T_VAR) {
    char *v_name;
    v_name = e->name;
    return hash_table_get(state, v_name);
  } else if (et == T_BINOP) {
    enum BinOpType bop;
    bop = e->bop;
    arg1 = e->arg1;
    arg2 = e->arg2;
    val1 = eval(state, mem, arg1);
    if (bop == T_AND) {
      if (val1) {
        return eval(state, mem, arg2);
      } else {
        return 0;
      }
    } else if (bop == T_OR) {
      if (val1) {
        return 1;
      } else {
        return eval(state, mem, arg2);
      }
    } else if (bop == T_PLUS) {
      return val1 + eval(state, mem, arg2);
    } else if (bop == T_MINUS) {
      return val1 - eval(state, mem, arg2);
    } else if (bop == T_MUL) {
      return val1 * eval(state, mem, arg2);
    } else if (bop == T_DIV) {
      val2 = eval(state, mem, arg2);
      if (! val2) {
        return 0;
      } else {
        return val1 / val2;
      }
    } else if (bop == T_MOD) {
      val2 = eval(state, mem, arg2);
      if (! val2) {
        return 0;
      } else {
        return val1 % val2;
      }
    } else if (bop == T_LT) {
      val2 = eval(state, mem, arg2);
      if (val1 < val2) {
        return 1;
      } else {
        return 0;
      }
    } else if (bop == T_EQ) {
      val2 = eval(state, mem, arg2);
      if (val1 < val2) {
        return 1;
      } else {
        return 0;
      }
    }
  } else if (et == T_DEREF) {
    arg1 = e->arg1;
    val1 = eval(state, mem, arg1);
    return mem_get(mem, val1);
  } else if (et == T_MALLOC) {
    return mem_alloc(mem);
  }

  return 0;
}

void
step(struct hash_table *state,
     struct memory *mem,
     struct res_prog *r) {
  /*@ With st m prog
      Require
        state == st && mem == m && r == prog &&
        hash_table_rep(st) * memory_rep(m) * prog_rep(prog)
      Ensure
        hash_table_rep(st) * memory_rep(m) * prog_rep_or_end(prog)
   */

  struct cmd *foc;
  foc = r->foc;

  if (foc == (void *)0) {
    struct cont_list * cl;
    struct cmd *cl_c;
    struct cont_list *cl_link;
    cl = r->ectx;
    cl_c = cl->c;
    cl_link = cl->link;
    r->foc = cl_c;
    r->ectx = cl_link;
    free_cont_list(cl);
  } else {
    struct cmd *c;
    enum CmdType ct;
    c = foc;
    ct = c->t;
    unsigned val1;
    struct expr *arg1, *arg2;
    struct cmd *sub1, *sub2;
    struct cont_list *r_ectx;

    if (ct == T_DECL) {
      r->foc = (void *)0;
    } else if (ct == T_ASGN) {
      unsigned lhs, rhs;
      enum ExprType arg1_t;
      arg1 = c->arg1;
      arg2 = c->arg2;
      arg1_t = arg1->t;
      if (arg1_t == T_VAR) {
        char *v_name;
        v_name = arg1->name;
        rhs = eval(state, mem, arg2);
        hash_table_set(state, v_name, rhs);
      } else if (arg1_t == T_DEREF) {
        struct expr *_arg;
        _arg = arg1->arg1;
        lhs = eval(state, mem, _arg);
        rhs = eval(state, mem, arg2);
        mem_set(mem, lhs, rhs);
        free_expr_rec(_arg);
      } else {
        exit(1);
      }
      free_expr(arg1);
      free_expr_rec(arg2);
      r->foc = (void *)0;
    } else if (ct == T_SEQ) {
      sub1 = c->sub1;
      sub2 = c->sub2;
      r_ectx = r->ectx;
      r->foc = sub1;
      r->ectx = CL_Cons(sub2, r_ectx);
    } else if (ct == T_IF) {
      arg1 = c->arg1;
      val1 = eval(state, mem, arg1);
      sub1 = c->sub1;
      sub2 = c->sub2;
      if (val1) {
        r->foc = sub1;
        free_cmd_rec(sub2);
      } else {
        r->foc = sub2;
        free_cmd_rec(sub1);
      }
      free_expr_rec(arg1);
    } else if (ct == T_WHILE) {
      arg1 = c->arg1;
      val1 = eval(state, mem, arg1);
      if (val1) {
        struct cont_list *new_ectx;
        sub1 = c->sub1;
        sub1 = copy_cmd(sub1);
        r->foc = sub1;
        r_ectx = r->ectx;
        new_ectx = CL_Cons(c, r_ectx);
        r->ectx = new_ectx;
        return;
      } else {
        sub1 = c->sub1;
        r->foc = (void *)0;
        free_expr_rec(arg1);
        free_cmd_rec(sub1);
      }
    }
    free_cmd(c);
  }
  return;
}
