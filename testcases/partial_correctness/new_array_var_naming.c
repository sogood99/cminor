/*@
  requires \true;
  ensures \true;
 */
void foo() {
	int new_array[42];
	int new_array2[42];
	//@ assert new_array[0] == new_array2[0];
}
