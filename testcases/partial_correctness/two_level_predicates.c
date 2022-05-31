/*@
  predicate a(integer i) = \true;
  predicate b(integer i) = a(i);
 */

/*@
  requires \true;
  ensures b(1);
 */
void main() {}
