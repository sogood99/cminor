/*@
  predicate sorted(integer[] arr, integer low, integer high) =
    (\forall integer sorted_a,sorted_b;
		((low <= sorted_a <= sorted_b <= high)
			==> arr[sorted_a] <= arr[sorted_b]));
*/

/*@
  requires \valid(a_0+(0..n-1));
  requires n >= 1;
  decreases (n + 1, n + 1);
 */
void InsertionSort(int a_0[], int n) {
    /*@
		loop invariant n >= 1;
		loop invariant \valid(a_0 + (0..n-1));
		loop invariant sorted(a_0, 0, i - 1);
		loop invariant 1 <= i <= n + 1;
		loop variant (n - i + 1, n + 1);
     */
	for
		(int i = 1; i < n; i = i + 1)
	{
		int t = a_0[i];
		int j;
		/*@
			loop invariant n >= 1;
			loop invariant \valid(a_0 + (0..n-1));
			loop invariant sorted(a_0, 0, i - 1);
			loop invariant \forall integer ix; j < ix && ix < i ==> a_0[ix] > t;
			loop invariant j < i - 1 ==> sorted(a_0, 0, i);
			loop invariant -1 <= j < i < n;
			loop invariant 1 <= i;
			loop variant (n - i + 1, j + 1);
		*/
		for
			(j = i - 1; j >= 0; j = j - 1)
		{
			if (a_0[j] <= t) break;
			a_0[j + 1] = a_0[j];
		}
		a_0[j + 1] = t;
	}
    //@ assert sorted(a_0, 0, n - 1);
	return;
}
