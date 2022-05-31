/*@
  predicate sorted(integer[] arr, integer low, integer high) = 
  (\forall integer sorted_a,sorted_b;
    ((low <= sorted_a && sorted_a <= sorted_b && sorted_b <= high)
      ==> arr[sorted_a]<=arr[sorted_b]));

predicate partitioned(integer[] arr, integer low1, integer high1, integer low2, integer high2) =
  (\forall integer partitioned_a, partitioned_b;
    ((low1 <= partitioned_a <= high1 && low2 <= partitioned_b <= high2)
      ==> arr[partitioned_a]<=arr[partitioned_b]));
  */

/*@
  requires 0 <= l <= u;
  decreases (u - l, 1);
  ensures l <= \result <= u;
 */
int random(int l, int u)
{
	/* a placeholder: only the post condition is important */
	return u;
}

/*@
  requires 0 <= l <= u;
  requires u < n;
  requires n > 0;
  requires partitioned(a, 0, l - 1, l, u);
  requires partitioned(a, l, u, u + 1, n - 1);
  requires \valid(a + (0..n-1));
  decreases (u - l, 2);
  ensures
      \result >=l && \result <=u &&
      partitioned(a, l, \result - 1, \result, \result) &&
      partitioned(a, \result, \result, \result + 1, u) &&
      partitioned(a, 0, l - 1, l, u) &&
      partitioned(a, l, u, u + 1, n - 1);
*/
int partition(int a[], int n, int l, int u) {
	int pi = random(l, u);

	//swap a[u] and a[pi]	
	int pv = a[pi];
	a[pi] = a[u];
	a[u] = pv;

	int i = l - 1;
    /*@
      loop invariant n > 0;
      loop invariant \valid(a + (0..n-1));
      loop invariant \forall integer x; (l <= x <= i ==> a[x]<=pv);
		  loop invariant \forall integer x; (i < x < j ==> a[x]>=pv);
 		  loop invariant l - 1 <= i < j <= u < n;
      loop invariant 0 <= l <= u;
      loop invariant i >= -1;
      loop invariant a[u] == pv;
      loop invariant partitioned(a, 0, l - 1, l, u);
      loop invariant partitioned(a, l, u, u + 1, n - 1);
      loop variant (u - j, 0);
    */
	for
		(int j = l; j < u; j = j + 1)
	{
		if (a[j] <= pv) {
			i = i + 1;
			
			//swap a[i] and a[j]
			int t = a[i];
			a[i] = a[j];
			a[j] = t;
		}
	}

	//swap a[i+1] and a[u]
	int t = a[i + 1];
	a[i + 1] = a[u];
	a[u] = t;
	
	return i+1;
}

/*@
  requires 0 <= l <= u + 1;
  requires u < n;
  requires n > 0;
  requires partitioned(a_0, 0, l - 1, l, u);
  requires partitioned(a_0, l, u, u + 1, n - 1);
  requires \valid(a_0 + (0..n-1));
  decreases (u - l + 1, 3);
  ensures sorted(a_0, l, u);
  ensures partitioned(a_0, 0, l - 1, l, u);
  ensures partitioned(a_0, l, u, u + 1, n - 1);
*/
void qsort(int a_0[], int n, int l, int u) {
	if (l >= u)
		return;
	else {
		int p = partition(a_0, n, l, u);
		qsort(a_0, n, l, p - 1);
		qsort(a_0, n, p + 1, u);
		return;
  }
}

/*@
  requires n > 0;
  requires \valid(a + (0..n-1));
  decreases (n, 4);
  ensures sorted(a, 0, n - 1);
 */
void QuickSort(int a[], int n)
{
	qsort(a, n, 0, n - 1);
}
