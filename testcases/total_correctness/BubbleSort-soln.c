/*@
 predicate sorted(integer[] arr, integer low, integer high) = 
  (\forall integer sorted_a,sorted_b; ((low <= sorted_a && sorted_a <= sorted_b && sorted_b <= high) ==> arr[sorted_a]<=arr[sorted_b]));

 predicate partitioned(integer[] arr, integer low1, integer high1, integer low2, integer high2) =
  (\forall integer partitioned_a, partitioned_b; ((low1 <= partitioned_a && partitioned_a <= high1 && low2 <= partitioned_b && partitioned_b <= high2) ==> arr[partitioned_a]<=arr[partitioned_b]));
*/

/*@
  requires \valid(arr_0+(0..n-1));
  requires n >= 1;
  decreases (n + 1) * (n + 1);
 */
void BubbleSort(int arr_0[], int n) {
	/*@
      loop invariant sorted(arr_0, i, n - 1);
      loop invariant 0 <= i < n;
      loop invariant partitioned(arr_0, 0, i, i+1, n-1);
      loop invariant \valid(arr_0 + (0..n-1));
      loop variant (i + 1) * (n + 1);
     */
	for
        (int i = n - 1; i > 0; i = i - 1)
	{
        /*@
            loop invariant \valid(arr_0 + (0..n-1));
            loop invariant partitioned(arr_0, 0, i, i + 1, n - 1);
            loop invariant 0 < i < n;
            loop invariant 0 <= j <= i;
            loop invariant sorted(arr_0, i, n - 1);
            loop invariant partitioned(arr_0, 0, j - 1, j, j);
            loop variant (i + 1) * (n + 1) - j - 1;
        */
		for
            (int j = 0; j < i; j = j + 1)
		{
			if (arr_0[j] > arr_0[j + 1]) {
				int temp = arr_0[j];
				arr_0[j] = arr_0[j + 1];
				arr_0[j + 1] = temp;
			}
		}
	}
   //@ assert sorted(arr_0, 0, n-1) ;
}
