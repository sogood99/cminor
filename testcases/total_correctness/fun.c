/*@ requires \true;
  @ decreases 11;
  @ ensures \result == 10; */
int fun() {
    int count = 0;
    /*@ loop invariant count <= 10;
      @ loop variant 10 - count; */
    while (count < 10)
    {
        count = count + 1;
    }
    return count;
}