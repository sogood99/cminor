/*@
  requires \valid(x+(0..n-1));
  requires n >= 1;
  decreases n + 2;
 */
void foo(int x[], int n) {
    /*@
      loop invariant i >= 0 && i <= n;
      loop variant i + 1;
     */
	for (int i = n; i > 0; i = i - 1) {}
}
