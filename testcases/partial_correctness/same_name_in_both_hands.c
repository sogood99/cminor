/*@ 
  requires x == 1;
  ensures \result == 2;
 */
int fun(int x) {
	{
		int x = x + 1;
		return x;
	}
}
