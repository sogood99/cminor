/*@
  requires \true;
  ensures \true;
 */
void main() {
	int x;
	//@ assert x >= 0;
	//@ assert x >= 0;
	x = x + 1;
	//@ assert x >= 1;
}
