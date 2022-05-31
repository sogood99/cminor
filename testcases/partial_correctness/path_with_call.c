/*@
  requires \true;
  ensures \result > x && \result > y;
 */
int larger(int x, int y) {
	if (x > y)
		return x + 1;
	else
		return y + 1;
}

/*@
  requires \true;
  ensures \true;
 */
void main(int x) {
	int y = larger(x, 2 * x);
	//@ assert y > 2*x;
}
