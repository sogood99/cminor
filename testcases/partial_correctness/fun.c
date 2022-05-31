/*@ requires \true;
  @ ensures \result == 10; */
int fun() {
    int count = 0;
    //@ loop invariant count <= 10;
    while (count < 10)
    {
        count = count + 1;
    }
    return count;
}