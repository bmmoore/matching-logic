#include<stdlib.h>


struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};


int max(int a, int b)
//@ rule <k> $ => return maxInt(a, b); ...</k>
{
  return a > b ? a : b;
}


int height(struct node *tree)
/*@ rule <k> $ => return height(T); ...</k> <heap>... htree(tree)(T) ...</heap>
    if hasHeight(T) */
{
  return tree ? tree->height : 0;
}

void update_height(struct node *tree)
{
  tree->height = max(height(tree->left), height(tree->right)) + 1;
}


int find_min(struct node *tree)
/*@ rule <k> $ => return m; ...</k> <heap>... htree(tree)(T) ...</heap>
    if ~(tree = 0) /\ isBst(st(T))
       /\ in(m, tree2mset(st(T))) /\ leq({m}, tree2mset(st(T))) */
{
  if (tree->left == NULL)
    return tree->value;
  else
    return find_min(tree->left);
}


struct node* left_rotate(struct node *x)
{
  struct node *y;

  y = x->right;
  x->right = y->left;
  y->left = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node* right_rotate(struct node *x)
{
  struct node *y;

  y = x->left;
  x->left = y->right;
  y->right = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node* balance(struct node *tree)
{
  if (height(tree->left) - height(tree->right) > 1) {
    if (height(tree->left->left) < height(tree->left->right))
      tree->left = left_rotate(tree->left);
    tree = right_rotate(tree);
  }
  else if (height(tree->left) - height(tree->right) < -1) {
    if (height(tree->right->left) > height(tree->right->right))
      tree->right = right_rotate(tree->right);
    tree = left_rotate(tree);
  }

  return tree;
}


struct node* avl_delete(struct node *tree, int value)
/*@ rule <k> $ => return ?tree; ...</k>
         <heap>... htree(tree)(T) => htree(?tree)(?T) ...</heap>
    if isAvl(T) /\ isAvl(?T)
       /\ tree2mset(st(?T)) = diff(tree2mset(st(T)), {value})
       /\ 0 <= height(T) - height(?T) /\ height(T) - height(?T) <= 1 */
{
  int min;

  if (tree == NULL)
    return NULL;

  if (value == tree->value) {
    if (tree->left == NULL) {
      struct node *temp;

      temp = tree->right;
      free(tree);

      return temp;
    }
    else if (tree->right == NULL) {
      struct node *temp;

      temp = tree->left;
      free(tree);

      return temp;
    }
    else {
      min = find_min(tree->right);
      tree->right = avl_delete(tree->right, min);
      tree->value = min;
    }
  }
  else if (value < tree->value)
    tree->left = avl_delete(tree->left, value);
  else
    tree->right = avl_delete(tree->right, value);

  update_height(tree);
  tree = balance(tree);

  return tree;
}


//@ var m : Int
//@ var T : Tree
