/*@
    requires n > 0 && 0 <= l && u < n;
    requires \valid(a + (0..n-1));
    decreases n + 2;
    ensures \result == 1 <==> \exists integer ix; (l <= ix && ix <= u && a[ix] == e);
*/
int LinearSearch(int a[], int n, int l, int u, int e) {
    /*@
     loop invariant n > 0;
     loop invariant \valid(a + (0..n-1));
     loop invariant 0 <= l <= i && u < n && (i <= u + 1 || i <= l);
     loop invariant \forall integer ix; l <= ix && ix < i ==> a[ix] != e;
     loop variant n + l + 1 - i;
     */
	for
		(int i = l; i <= u; i = i + 1)
	{
		if (a[i] == e)
			return 1;
	}
	return 0;
}
