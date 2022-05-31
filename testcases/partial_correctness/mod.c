/*@
  requires x == 7;
  ensures \result == 1;
 */
int foo(int x) {
	return x % 3;
}
