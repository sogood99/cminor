/*@
  requires x>=0 && y>=0;
  ensures \result >= 0;
 */
int ack(int x, int y) {
	if (x == 0)
		return y + 1;
	else if (y == 0)
		return ack(x - 1, 1);
	else
		return ack(x - 1, ack(x, y - 1));
}
