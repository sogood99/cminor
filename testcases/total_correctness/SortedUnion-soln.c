/*@
  predicate sorted(integer[] arr, integer low, integer high) = 
  	(\forall integer sorted_a, sorted_b;
	  	((low <= sorted_a <= sorted_b <= high) ==> arr[sorted_a] <= arr[sorted_b]));
  */

/*@
  requires n > 0 && m > 0;
  requires \valid(a + (0..n-1));
  requires \valid(b + (0..m-1));
  requires \valid(u + (0..n+m-1));
  requires sorted(a, 0, n - 1);
  requires sorted(b, 0, m - 1);
  decreases n + m + 1;
  ensures sorted(u, 0, n + m - 1);
  ensures (\exists integer ix; (0 <= ix <= n - 1 && a[ix] == 1))
           || (\exists integer ix; (0 <= ix <= m - 1 && b[ix] == 1))
          <==> (\exists integer ix; (0 <= ix <= n + m - 1 && u[ix] == 1));
*/
void uni(int a[], int b[], int n, int m, int u[]) {
	int i = 0;
	int j = 0;

    /*@
	  loop invariant n > 0 && m > 0;
	  loop invariant \valid(a + (0..n-1));
	  loop invariant \valid(b + (0..m-1));
	  loop invariant \valid(u + (0..n+m-1));
      loop invariant i + j == k;
	  loop invariant 0 <= i <= n && 0 <= j <= m && k <= n + m;
	  loop invariant sorted(a, 0, n - 1);
	  loop invariant sorted(b, 0, m - 1);
	  loop invariant sorted(u, 0, k - 1);
	  loop invariant k > 0 ==> (i < n ==> u[k - 1] <= a[i]) && (j < m ==> u[k - 1] <= b[j]);
	  loop invariant (\exists integer ix; (0 <= ix < i && a[ix] == 1))
						|| (\exists integer ix; (0 <= ix < j && b[ix] == 1))
					<==> (\exists integer ix; (0 <= ix < k && u[ix] == 1));
      loop variant n + m - k;
     */
	for (int k = 0; k < n + m; k = k + 1)
	{
		if (i >= n) {
			u[k] = b[j];
			j = j + 1;
		}
		else if (j >= m) {
			u[k] = a[i];
			i = i + 1;
		}
		else if (a[i] <= b[j]) {
			u[k] = a[i];
			i = i + 1;
		}
		else {
			u[k] = b[j];
			j = j + 1;
		}
	}

	return;
}
