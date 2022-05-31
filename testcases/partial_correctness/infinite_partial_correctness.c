// A program that won't terminate
// However, it's partial correctness can be verified.

/*@
  requires \true;
  ensures \result > 0;
 */
int fun() {
    return fun();
}
