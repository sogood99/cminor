/*
 * If you put in a lot more of these lines, we slot down a lot.
 */

/*@
  requires \valid(x+(0..0));
 */
void foo(int x[]) {
    x[0] = 0;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	x[0] = x[0] + 1;
	//@assert x[0] == 10;
}
