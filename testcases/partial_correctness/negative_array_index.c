/*@
  predicate sorted(integer[] arr, integer low, integer high) = 
    \forall integer sorted_a,sorted_b; ((low <= sorted_a && sorted_a <= sorted_b && sorted_b <= high) ==> arr[sorted_a]<=arr[sorted_b]);
 */

/*@
  requires \valid(a+(0..n-1));
  requires n > 0;
 */
void InsertionSort(int a[], int n) {
    /*@
      loop invariant sorted(a, 0, i - 1);
	  loop invariant 1 <= i <= n;
	  loop invariant n > 0;
	  loop invariant \valid(a + (0..n-1));
    */
	for
		(int i = 1; i < n; i = i + 1)
	{
		int t = a[i];
		int j;
        /*@
          loop invariant sorted(a, 0, i - 1);
		  loop invariant \forall integer ix; (j < ix && ix < i ==> a[ix] > t);
		  loop invariant j < i - 1 ==> sorted(a, 0, i);
		  loop invariant -1 <= j < i;
		  loop invariant 1 <= i < n;
		  loop invariant n > 0;
		  loop invariant \valid(a + (0..n-1));
         */
		for
			(j = i - 1; j >= 0; j = j - 1)
		{
			if (a[j] <= t) break;
			a[j + 1] = a[j];
		}
		a[j + 1] = t;
	}
  	//@assert sorted(a, 0, n-1);
}
