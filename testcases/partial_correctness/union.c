/*@
  predicate inRange(integer target, integer[] arr, integer n, integer low, integer high) =
    ((low <= high && 0 <= low && high <= n - 1) ==>
    (\exists integer ix; (low <= ix && ix <= high && arr[ix] == target)));

  predicate in(integer target, integer[] arr, integer n ) =
    inRange(target, arr, n, 0, n - 1 );
 */

/*@
  requires \valid(a+(0..n-1));
  requires \valid(b+(0..m-1));
  requires \valid(u+(0..n+m-1));
  requires n > 0 && m > 0;
  ensures \valid(u+(0..n+m-1));
  ensures ((\exists integer ix; (0 <= ix && ix <= n - 1 && a[ix] == 1)
        || \exists integer ix; (0 <= ix && ix <= m - 1 && b[ix] == 1))
          <==> \exists integer ix; (0 <= ix && ix <= n + m - 1 && u[ix] == 1));
 */
void unio(int a[], int n, int b[], int m, int u[]) {
    int j = 0;

    /*@ 
      loop invariant n > 0 && m > 0;
      loop invariant j >= 0;
      loop invariant i > 0 && j > 0 && a[i - 1] == u[j - 1]
                      ==> (\exists integer ix; (0 <= ix <= i - 1 && a[ix] == 1)
                            <==> \exists integer ix; (0 <= ix <= j - 1 && u[ix] == 1));
    */
    for (int i = 0; i < n; i = i + 1)
    {
            u[j] = a[i];
            j = j + 1;
    }
    /*@
        loop invariant n > 0 && m > 0;
        loop invariant (in(1,a, n) || in(1,b, m) <==> in(1,u, n+m));
     */
    for (int i = 0; i < m; i = i + 1)
    {
            u[j] = b[i];
            j = j + 1;
    }
}
