/*@
  requires \true;
  decreases 10;
  ensures \result == 15;
 */
int fun() {
    int sum = 0;
    /*@
      loop invariant 0 <= i && i <= 6 && (
            0 <= i && i < 6 && sum == i * (i - 1) / 2
            || i == 6 && sum == 15);
      loop variant (6 - i);
     */
    for (int i = 0; i < 6; i = i + 1)
    {
        sum = sum + i;
    }
    return sum;
}
