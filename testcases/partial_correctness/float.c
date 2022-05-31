/*@
  requires \true;
  ensures \true;
 */
float pi() {
	return 3.14159;
}

/*@
  requires \true;
  ensures \true;
 */
void main() {
	float f;
	f = 2.5;
	f = f + pi();
}
