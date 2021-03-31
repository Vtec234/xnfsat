#include <stdio.h>
#include <stdlib.h>

#define POOL	1
#define LINEAR	2

#define DEFAULT	LINEAR

void printCls (int* array, int size) {
  for (int i = 0; i < size; i++)
    printf ("%i ", array[i]);
  printf ("0\n");
}

int printXOR (int* array, int size, int var, int mode) {
  if (size <  1) {
    printf ("0\n");
    return var; }

  if (size == 1) {
    printf ("%i 0\n", -array[0]);
    return var; }

  if (size == 2) {
    printf ("%i %i 0\n",  array[0], -array[1]);
    printf ("%i %i 0\n", -array[0],  array[1]);
    return var; }

  if (size == 3) {
    printf ("%i %i %i 0\n",  array[0],  array[1], -array[2]);
    printf ("%i %i %i 0\n",  array[0], -array[1],  array[2]);
    printf ("%i %i %i 0\n", -array[0],  array[1],  array[2]);
    printf ("%i %i %i 0\n", -array[0], -array[1], -array[2]);
    return var; }

  if (size == 4) {
    printf ("%i %i %i %i 0\n",  array[0],  array[1],  array[2], -array[3]);
    printf ("%i %i %i %i 0\n",  array[0],  array[1], -array[2],  array[3]);
    printf ("%i %i %i %i 0\n",  array[0], -array[1],  array[2],  array[3]);
    printf ("%i %i %i %i 0\n", -array[0],  array[1],  array[2],  array[3]);
    printf ("%i %i %i %i 0\n",  array[0], -array[1], -array[2], -array[3]);
    printf ("%i %i %i %i 0\n", -array[0],  array[1], -array[2], -array[3]);
    printf ("%i %i %i %i 0\n", -array[0], -array[1],  array[2], -array[3]);
    printf ("%i %i %i %i 0\n", -array[0], -array[1], -array[2],  array[3]);
    return var; }

  if (size == 5) {
    printf ("%i %i %i %i %i 0\n",  array[0],  array[1],  array[2], -array[3],  array[4]);
    printf ("%i %i %i %i %i 0\n",  array[0],  array[1], -array[2],  array[3],  array[4]);
    printf ("%i %i %i %i %i 0\n",  array[0], -array[1],  array[2],  array[3],  array[4]);
    printf ("%i %i %i %i %i 0\n", -array[0],  array[1],  array[2],  array[3],  array[4]);
    printf ("%i %i %i %i %i 0\n",  array[0], -array[1], -array[2], -array[3],  array[4]);
    printf ("%i %i %i %i %i 0\n", -array[0],  array[1], -array[2], -array[3],  array[4]);
    printf ("%i %i %i %i %i 0\n", -array[0], -array[1],  array[2], -array[3],  array[4]);
    printf ("%i %i %i %i %i 0\n", -array[0], -array[1], -array[2],  array[3],  array[4]);
    printf ("%i %i %i %i %i 0\n",  array[0],  array[1],  array[2],  array[3], -array[4]);
    printf ("%i %i %i %i %i 0\n",  array[0],  array[1], -array[2], -array[3], -array[4]);
    printf ("%i %i %i %i %i 0\n",  array[0], -array[1],  array[2], -array[3], -array[4]);
    printf ("%i %i %i %i %i 0\n", -array[0],  array[1],  array[2], -array[3], -array[4]);
    printf ("%i %i %i %i %i 0\n",  array[0], -array[1], -array[2],  array[3], -array[4]);
    printf ("%i %i %i %i %i 0\n", -array[0],  array[1], -array[2],  array[3], -array[4]);
    printf ("%i %i %i %i %i 0\n", -array[0], -array[1],  array[2],  array[3], -array[4]);
    printf ("%i %i %i %i %i 0\n", -array[0], -array[1], -array[2], -array[3], -array[4]);
    return var; }

  printf ("%i %i %i %i %i 0\n",  array[0],  array[1],  array[2], -array[3],  var);
  printf ("%i %i %i %i %i 0\n",  array[0],  array[1], -array[2],  array[3],  var);
  printf ("%i %i %i %i %i 0\n",  array[0], -array[1],  array[2],  array[3],  var);
  printf ("%i %i %i %i %i 0\n", -array[0],  array[1],  array[2],  array[3],  var);
  printf ("%i %i %i %i %i 0\n",  array[0], -array[1], -array[2], -array[3],  var);
  printf ("%i %i %i %i %i 0\n", -array[0],  array[1], -array[2], -array[3],  var);
  printf ("%i %i %i %i %i 0\n", -array[0], -array[1],  array[2], -array[3],  var);
  printf ("%i %i %i %i %i 0\n", -array[0], -array[1], -array[2],  array[3],  var);
  printf ("%i %i %i %i %i 0\n",  array[0],  array[1],  array[2],  array[3], -var);
  printf ("%i %i %i %i %i 0\n",  array[0],  array[1], -array[2], -array[3], -var);
  printf ("%i %i %i %i %i 0\n",  array[0], -array[1],  array[2], -array[3], -var);
  printf ("%i %i %i %i %i 0\n", -array[0],  array[1],  array[2], -array[3], -var);
  printf ("%i %i %i %i %i 0\n",  array[0], -array[1], -array[2],  array[3], -var);
  printf ("%i %i %i %i %i 0\n", -array[0],  array[1], -array[2],  array[3], -var);
  printf ("%i %i %i %i %i 0\n", -array[0], -array[1],  array[2],  array[3], -var);
  printf ("%i %i %i %i %i 0\n", -array[0], -array[1], -array[2], -array[3], -var);

  if (mode == POOL) {
    for (int i = 0; i < size - 4; i++) array[i] = array[i+4];
    array[size - 4] = var;
  }

  if (mode == LINEAR) {
    array[0] = var;
    for (int i = 0; i < size - 4; i++) array[i+1] = array[i+4];
  }

  return printXOR (array, size - 3, var + 1, mode);
}

int main (int argc, char** argv) {
  int nVar, nCls;

  FILE* xnf = fopen (argv[1], "r");

  int mode = DEFAULT;
  if (argc > 2) {
    if (argv[2][0] == '-' && argv[2][1] == 'l') mode = LINEAR;
    if (argv[2][0] == '-' && argv[2][1] == 'p') mode = POOL; }

  int tmp = fscanf (xnf, " p xnf %i %i ", &nVar, &nCls);

  int array[nVar];
  int maxVar = nVar + 1;

  while (1) {
    int size = 0;
    int lit;
    tmp = fscanf (xnf, " x %i ", &lit);
    int flag = tmp;
    if (flag == 0) {
      tmp = fscanf (xnf, " %i ", &lit); }

    array[size++] = lit;

    if (tmp == EOF) break;
    while (1) {
      tmp = fscanf (xnf, " %i ", &lit);
      if (lit) array[ size++ ] = lit;
      if (lit == 0 || tmp == EOF) break;
    }
    if (tmp == EOF) break;

    if (flag == 1) {
      if (size > 5) {
        maxVar += (size - 3)/3;
      }
      if (size > 5) {
        nCls += (size - 3)/3 * 16;
        nCls += (1<<((size % 3) + 2)) - 1;
         }
    }
  }
  fclose (xnf);

  printf ("p cnf %i %i\n", maxVar - 1, nCls);

  xnf = fopen (argv[1], "r");
  tmp = fscanf (xnf, " p xnf %i %i ", &nVar, &nCls);
  maxVar = nVar + 1;


  while (1) {
    int size = 0;
    int lit;
    tmp = fscanf (xnf, " x %i ", &lit);
    if (tmp == EOF) break;

    int flag = tmp;
    if (flag == 0) {
      tmp = fscanf (xnf, " %i ", &lit); }
    if (tmp == EOF) break;

    array[size++] = lit;
    if (flag) array[0] = -lit;

    while (1) {
      tmp = fscanf (xnf, " %i ", &lit);
      if (lit) array[ size++ ] = lit;
      if (lit == 0 || tmp == EOF) break;
    }
    if (tmp == EOF) break;

    if (flag == 1) {
      maxVar = printXOR (array, size, maxVar, mode);
    }
    else {
      printCls (array, size);
    }
  }
  fclose (xnf);
}
