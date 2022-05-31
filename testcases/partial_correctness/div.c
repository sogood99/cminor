/*@
  requires x == 1;
  ensures \result == 42;
 */
int foo(int x) {
	return x / 2;
}
