/*
 * Function schorr_waite implements the Schorr-Waite graph marking algorithm.
 * The code is identical with the one in the previous example. The difference
 * lays in the specification: while the previous examples considers the case
 * when the algorithm is applied on a tree, this example consider the case of a
 * general graph.
 *
 * The specification of the function states that the heap contains the graph of
 * the structure nodes reachable starting from root pointer and stopping at the
 * 0 (NULL) pointer. All the nodes that are not reachable from the root are part
 * of the heap frame. Each node of the mathematical Schorr-Waite graph is
 * labeled with the pair (pointer_to_structure, mark), while each edge is
 * labeled with name of the field that generated the respective edge. In this
 * context, pointers(T) refers to the graph holding only the pointer label
 * (dropping the mark label from each node), while marks(T) refers to the graph
 * holding only the mark component. The specification also states that the mark
 * labels of the initial graph are 0, and that the pointer labels of the initial
 * and final graph are identical.
 * 
 * The loop invariant states that the heap contains the graph of the structure
 * nodes reachable starting from p and q and stopping at 0. The isRestorable
 * predicates encodes the existence of a path from p to root in the initial
 * graph and the nodes on that path are marked accordingly. The invariant also
 * states that pointer structure of the initial graph can be obtain by restoring
 * the edges in the current graph, and that the root program variable remains
 * unchanged.
 * 
 * A few words about notation: {Elements}s stands for the set with the Elements
 * content, while swgraph(Roots, Frontier)(Graph) stands for the graph of
 * structure nodes reachable starting from an address in Roots and stopping at
 * an address in Frontier. For the definitions and axioms required by this proof
 * see [1].
 *
 * [1] http://code.google.com/p/matching-logic/source/browse/trunk/matchC/lib/theories/schorr-waite-theory.maude
 */


#include<stdlib.h>


struct graphNode {
  int mark;
  struct graphNode *left;
  struct graphNode *right;
};


void schorr_waite_graph(struct graphNode *root)
/*@ rule <k> $ => return; ...</k>
         <heap>...
           swgraph({root}s, {0}s)(G) => swgraph({root}s, {0}s)(?G)
         ...</heap>
    if isConst(0, marks(G)) /\ pointers(G) = pointers(?G) */
{
  struct graphNode *p;
  struct graphNode *q;

  if (root == NULL)
    return;

  p = root; q = NULL;
  /*@ inv <heap>... swgraph({p, q}s, {0}s)(?GPQ) ...</heap>
          /\ root = r /\ isRestorable(p, q, root, ?GPQ)
          /\ pointers(G) = pointers(restore(p, q, ?GPQ)) */
  while (p != NULL) {
    struct graphNode *t;

    p->mark = p->mark + 1;
    if (p->mark == 3 || p->left != NULL && p->left->mark == 0) {
      // parallel assignment p->left, p->right, q, p = p->right, q, p, p->left
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = p;
      p = t;
    }
    else {
      // parallel assignment p->left, p->right, q = p->right, q, p->left
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = t;
    }
  }

}


//@ var r : Int
//@ var G, GPQ : Graph

