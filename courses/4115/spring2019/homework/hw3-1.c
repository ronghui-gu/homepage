int a[2][3]; /* Globals not optimized */
int i, j;    /* Make names readable */

int access() {
  return a[i][j];
}
