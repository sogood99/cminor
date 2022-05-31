/*@
  decreases n + 1;
 */
void fun(int n) {
    /*@
        loop variant n;
    */
    while
    (n < 10)
    {
        n = n - 1;
    }
}
