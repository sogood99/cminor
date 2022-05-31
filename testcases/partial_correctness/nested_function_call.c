/*@
  requires \true;
  ensures \result == 2;
 */
int main2() {
	return 2;
}
/*@
  requires \true;
  ensures \result == a;
 */
int main3(int a) {
	return a;
}
/*@
  requires \true;
  ensures \result == 2;
 */
int main(int x) {
	int a = main3(main2());
	return a;
}
