/*@
    requires n > 0;
    requires \valid(arr + (0..n-1));
    decreases n + 1;
    ensures \forall integer ix; (ix >= 0 && ix < n ==> \result >= arr[ix]);
*/
int max(int arr[], int n) {
	int max = arr[0];
    /*@
      loop invariant \forall integer j; (j < i && j >= 0 ==> max >= arr[j]);
	  loop invariant 1 <= i <= n;
	  loop invariant \valid(arr + (0..n-1));
      loop variant n - i;
     */
	for
		(int i = 1; i < n; i = i + 1)
	{
		if(arr[i] >= max) {
			max = arr[i];
		}
	}
	return max;
}
