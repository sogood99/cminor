struct A {
    int x;
};

/*@ requires \true;
  @ ensures \result.x == 1;
*/
struct A fun() {
    struct A a;
    a.x = 2;
    return a;
}