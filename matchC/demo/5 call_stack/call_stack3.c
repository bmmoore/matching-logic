#include <stdio.h>


void trusted(int n);
void untrusted(int n);
void any(int n);


void trusted(int n)
/*@ rule <k> $ => return; ...</k> <stack> S </stack> <out>... . => A </out>
    if n >= 10 \/ in(hd(ids(S)), {main, trusted}) */
{
  printf("%d ", n);
  untrusted(n);
  any(n);
  if (n)
    trusted(n - 1);
}

void untrusted(int n)
/*@ rule <k> $ => return; ...</k> <stack> S </stack> <out>... . => A </out>
    if in(trusted, ids(S)) */
{
  printf("%d ", -n);
  if (n)
    any(n - 1);
}

void any(int n)
{
  // untrusted(n);
  if(n > 10)
    // security policy possibly (when any is called) violated if n <= 10
    trusted(n - 1);
}


int main()
{
  trusted(5);
  any(5);
}


//@ var S : ListItem
//@ var A : Seq

