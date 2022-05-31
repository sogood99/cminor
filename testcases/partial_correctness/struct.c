struct A {
	int x;
};

/*@
  requires \true;
  ensures \result > 0;
 */
int fun() {
	struct A a;
	a.x = 2;
	return a.x;
}
