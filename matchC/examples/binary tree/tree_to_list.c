#include <stdlib.h>
#include <stdio.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct listNode {
  int val;
  struct listNode *next;
};

struct stackNode {
  struct treeNode *val;
  struct stackNode *next;
};


struct listNode* tree_to_list_recursive(struct treeNode *t, struct listNode *l)
/*@ rule <k> $ => return ?l; </k>
         <heap_> tree(t)(T), list(l)(A) => list(?l)(tree2list(T) @ A) <_/heap>
         <out_> epsilon => rev(tree2list(T)) </out> */
{
  struct listNode *ln;

  if (t == NULL)
    return l;

  ln = (struct listNode *) malloc(sizeof(struct listNode));
  ln->val = t->val;
  ln->next = tree_to_list_recursive(t->right, l);
  printf("%d ", t->val);
  l = tree_to_list_recursive(t->left, ln);
  free(t);

  return l;
}

struct listNode* tree_to_list_iterative(struct treeNode *t)
/*@ rule <k> $ => return ?l; </k>
         <heap_> tree(t)(T) => list(?l)(tree2list(T)) <_/heap>
         <out_> epsilon => rev(tree2list(T)) </out> */
{
  struct listNode *l;
  struct stackNode *s;

  if (t == NULL)
    return NULL;

  l = NULL;
  s = (struct stackNode *) malloc(sizeof(struct stackNode));
  s->val = t;
  s->next = NULL;
  /*@ inv <heap_> treeList(s)(?TS), list(l)(?A) <_/heap> <out_> rev(?A) </out>
          /\ tree2list(T) = treeList2list(rev(?TS)) @ ?A */
  while (s != NULL) {
    struct treeNode *tn;
    struct listNode *ln;
    struct stackNode *sn;

    sn = s;
    s = s->next ;
    tn = sn->val;
    free(sn) ;
    if (tn->left != NULL) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn->left;
      sn->next = s;
      s = sn;
    }
    if (tn->right != NULL) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn;
      sn->next = s;
      s = sn;
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn->right;
      sn->next = s;
      s = sn;
      tn->left = tn->right = NULL;
    }
    else {
      ln = (struct listNode *) malloc(sizeof(struct listNode));
      ln->val = tn->val;
      ln->next = l;
      l = ln;
      printf("%d ", ln->val);
      free(tn);
    }
  }

  return l;
}


//@ var A, TS : Seq
//@ var T : Tree

