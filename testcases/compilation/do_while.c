/*@
  @ requires \true;
  @ ensures \true;
  */
void fun() {
    int x = 0;
    //@ loop invariant x < 1;
    do
    {
      x = x + 1;
    } while(x < 1);

    // ++x;
    // //@ loop invariant x < 1;
    // while (x < 1)
    //     ++x;

    //@ assert x == 1;
}