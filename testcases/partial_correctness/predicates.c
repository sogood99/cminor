/* PiVC allows you to define and use your own predicates. */

/*@
  predicate contains(integer[] arr, integer l, integer u, integer e) =
    \exists integer ix; (l <= ix && ix <= u && arr[ix] == e);
 */

/*@
  requires \valid(a+(0..n-1));
  requires 0 <= l <= u < n;
  ensures \result == 1 <==> contains(a, l, u, e);
 */
int LinearSearch(int a[], int n, int l, int u, int e) {
    /*@
      loop invariant 0 <= l <= i;
      loop invariant i <= u + 1 && u < n;
      loop invariant !contains(a, l, i - 1, e);
      loop invariant \valid(a + (0..n-1));
    */
	for
		(int i = l; i <= u; i = i + 1)
	{
		if (a[i] == e)
			return 1;
	}
	return 0;
}
