#include<stdio.h>
#include<stdlib.h>


struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};


int max(int a, int b)
/*@ rule <k> $ => return maxInt(a, b); <_/k> */
{
  return a > b ? a : b;
}

struct node * new_leaf(int value)
{
  struct node *leaf;
  leaf = (struct node *) malloc(sizeof(struct node));

  leaf->value = value;
  leaf->height = 1;
  leaf->left = NULL;
  leaf->right = NULL;

  return leaf;
}


int height(struct node *tree)
/*@ rule <k> $ => return height(T); <_/k> <heap_> htree(tree)(T) <_/heap>
    if hasHeight(T) */
{
  return tree ? tree->height : 0;
}

int update_height(struct node *tree)
{
  tree->height = max(height(tree->left), height(tree->right)) + 1;
}


int find_min(struct node *tree)
/*@ rule <k> $ => return m; <_/k> <heap_> htree(tree)(T) <_/heap>
    if ~(tree = 0) /\ isBst(st(T))
       /\ in(m, tree2mset(st(T))) /\ leq({m}, tree2mset(st(T))) */
{
  if (tree->left == NULL)
    return tree->value;
  else
    return find_min(tree->left);
}


struct node * left_rotate(struct node *x)
{
  struct node *y;

  y = x->right;
  x->right = y->left;
  y->left = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node * right_rotate(struct node *x)
{
  struct node *y;

  y = x->left;
  x->left = y->right;
  y->right = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node * balance(struct node *tree)
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


struct node * insert(struct node *tree, int value)
/*@ rule <k> $ => return ?tree; <_/k>
         <heap_> htree(tree)(T) => htree(?tree)(?T) <_/heap>
    if isAvl(T) /\ isAvl(?T)
       /\ tree2mset(st(?T)) = tree2mset(st(T)) U {value}
       /\ 0 <= height(?T) - height(T) /\ height(?T) - height(T) <= 1 */
{
  if (tree == NULL)
    return new_leaf(value);

  tree->value;
  if (value < tree->value)
    tree->left = insert(tree->left, value);
  else
    tree->right = insert(tree->right, value);

  update_height(tree);
  tree = balance(tree);

  return tree;
}

struct node * delete(struct node *tree, int value)
/*@ rule <k> $ => return ?tree; <_/k>
         <heap_> htree(tree)(T) => htree(?tree)(?T) <_/heap>
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
      tree->right = delete(tree->right, min);
      tree->value = min;
    }
  }
  else if (value < tree->value)
    tree->left = delete(tree->left, value);
  else
    tree->right = delete(tree->right, value);

  update_height(tree);
  tree = balance(tree);

  return tree;
}

/*
void check_balance(struct node *tree)
{
  if (tree == NULL)
    return;

  check_balance(tree->left);
  check_balance(tree->right);

  // assert(tree->height == max(height(tree->left), height(tree->right)) + 1);
  // assert(fabs(height(tree->left) - height(tree->right)) < 2);
}
*/

void print_tree(struct node *tree, int indent) {
  int i;

  if (tree == NULL)
    return;

  /*
  print_tree(tree->right, indent + 1);
  for(i = 0; i < indent; i++) printf("  ");
  printf("(%d, %d)\n", tree->value, tree->height);
  print_tree(tree->left, indent + 1);
  */
  print_tree(tree->left, indent + 1);
  printf("%d ", tree->value);
  printf("%d\n", tree->height);
  print_tree(tree->right, indent + 1);
}

/*
int main() {
  int i;
  int n;
  struct node *tree;

  return 0;

  i = 0;
  n = 16;
  tree = NULL;
  while(i < n) {
    tree = insert(tree, i);
    i += 1;
  }

  print_tree(tree, 0);
}

  int n, value;
  struct node *tree

  tree = NULL;
  scanf("%d", &n);
  while(n--) {
    scanf("%d", &value);
    printf("insert %d\n", value);
    tree = insert(tree, value);
    check_balance(tree);
  }

  print_tree(tree, 0);

*/

//@ var m : Int
//@ var T : Tree

