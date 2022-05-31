/*@
  requires \valid(a_0+(0..n-1));
  requires n >= 1;
  decreases n + 1;
 */
void abs(int a_0[], int n) {
    /*@
      loop invariant 0 <= i <= n;
	  loop invariant \valid(a_0 + (0..n-1));
      loop variant n - i;
     */
	for
		(int i = 0; i < n; i = i + 1) 
	{
		if (a_0[i] < 0) {
			a_0[i] = -a_0[i];
		}
	}
	return;
}
