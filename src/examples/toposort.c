/*
Toposort needs these datastructures:
- 2d array with subarrays of different length
- stack (or queue) with known max size
*/

#include <stddef.h>
#include <stdio.h>


void toposort(
  int N, // number of nodes
  int** A, // adjacency list for each node
  int* outDegs, // outDegs[i] = length of A[i]
  int* res // empty array of size N for result
) {
  int todo[N];
  int todoSize = 0;
  int resSize = 0;
  int inDegs[N];
  for (int i = 0; i < N; i++) inDegs[i] = 0;
  for (int i = 0; i < N; i++) for (int j = 0; j < outDegs[i]; j++) inDegs[A[i][j]]++;
  for (int i = 0; i < N; i++) if (inDegs[i] == 0) {
    todo[todoSize] = i;
    todoSize++;
  }
  while (todoSize > 0) {
    todoSize--;
    int n = todo[todoSize];
    res[resSize] = n;
    resSize++;
    for (int j = 0; j < outDegs[n]; j++) {
      inDegs[A[n][j]]--;
      if (inDegs[A[n][j]] == 0) {
        todo[todoSize] = A[n][j];
        todoSize++;
      }
    }
  }
}

int main() {
  int N = 6;
  int a0[1] = {5};
  int a1[2] = {2, 5};
  int* a2 = NULL;
  int a3[2] = {1, 2};
  int a4[2] = {1, 5};
  int a5[1] = {2};
  int* A[6] = {a0, a1, a2, a3, a4, a5};
  int outDegs[6] = {1, 2, 0, 2, 2, 1};
  int res[N];
  toposort(N, A, outDegs, res);
  for (int i = 0; i < N; i++) {
    printf("%d ", res[i]);
  }
  printf("\n");
}


