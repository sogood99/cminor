/*@
  requires \true;
  ensures \result == 42;
 */
int forty_two() {
	return 42;
}

/*@
  requires \true;
  ensures \true;
 */
void foo(int x) {
	int ft = forty_two();
	//@ assert x == ft;
}
