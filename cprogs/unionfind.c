extern void * mallocN (int n);

struct Node {
    unsigned int rank;
    struct Node * parent;
};

struct Node* makeSet() {
    struct Node * x;
    x = (struct Node *) mallocN (sizeof (struct Node));
    x -> parent = x;
    x -> rank = 0;
    return x;
}

struct Node* find(struct Node* x) {
    /*@ With sh (g : Graph) x, */
    /*@ Require
          PROP  (vvalid g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP   (whole_graph sh g)
    */
    /*@ Ensure
        EX g': Graph, EX rt : pointer_val,
        PROP (findS g x g' /\ uf_root g' x rt)
        LOCAL (temp ret_temp (pointer_val_val rt))
        SEP (whole_graph sh g')
    */
    struct Node *p, *p0;
    /*@ Local
          PROP ()
          LOCAL (temp _x (pointer_val_val x))
          SEP (data_at sh node_type (vgamma2cdata (vgamma g x)) (pointer_val_val x))
    */
    /*@ Assert EX r pa,
          PROP ((r, pa) = vgamma g x)
          LOCAL (temp _x (pointer_val_val x))
          SEP (data_at sh node_type (vgamma2cdata (r, pa)) (pointer_val_val x))
    */
    p = x -> parent;
    /*@ Unlocal EX r pa,
          PROP ((r, pa) = vgamma g x)
          LOCAL (temp _x (pointer_val_val x); temp _p (pointer_val_val pa))
          SEP (whole_graph sh g)
    */
    if (p != x) {
        p0 = find(p);
        p = p0;
        x -> parent = p;
    }
    /*@ Assert EX g'': Graph, EX rt : pointer_val,
     PROP (findS g x g'' /\ uf_root g'' x rt)
     LOCAL (temp _p (pointer_val_val rt))
     SEP (whole_graph sh g'') */
    return p;
};

void unionS(struct Node* x, struct Node* y) {
    struct Node *xRoot, *yRoot;
    unsigned int xRank, yRank;
    xRoot = find(x);
    yRoot = find(y);
    if (xRoot == yRoot) {
        return;
    }
    xRank = xRoot -> rank;
    yRank = yRoot -> rank;
    if (xRank < yRank) {
        xRoot -> parent = yRoot;
    } else if (xRank > yRank) {
        yRoot -> parent = xRoot;
    } else {
        yRoot -> parent = xRoot;
        xRoot -> rank = xRank + 1;
    }
};
