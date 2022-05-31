// all specifications should hold

/*@
  requires x_0 >= 0 && x_0 % 2 == 0;
  ensures \result == x_0 /2 + y_0;
 */
int twoxy(int x_0, int y_0) {
	int x = x_0;
	int y = y_0;
    /*@
      loop invariant x >= 0;
	  loop invariant x % 2 == 0;
	  loop invariant x_0 % 2 == 0;
      loop invariant y == (x_0 - x) / 2 + y_0;
     */
	while
	(x > 0)
	{
		x = x - 2;
		y = y + 1;
	}
	return y;
}
