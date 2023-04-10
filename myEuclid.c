#include <stdio.h>
#include <limits.h>
/*@
    axiomatic MyEuclid{
    logic integer MyEuclid(integer m, integer n);

    axiom div_minus_l:
        \forall integer m, n;
        m > n ==> MyEuclid(m,n) == MyEuclid(m-n, n);
    axiom div_minus_r:
        \forall integer m, n;
        n > m ==> MyEuclid(m,n) == MyEuclid(m, n-m);
    axiom gcd_ref:
        \forall integer m, n;
        m == n ==> MyEuclid(m,n) == m;
    }
*/

/*@
    requires m >= 1;
    requires m <= INT_MAX;
    requires n >= 1;
    requires n <= INT_MAX;
    requires m-n <= INT_MAX;
    ensures \result == MyEuclid(m, n);
*/

int myEuclid(int m, int n) {
    int x,y,tmp;
    x = m;
    y = n;
    /*@ 
        loop invariant MyEuclid(m,n) ==  MyEuclid(\at(m,Pre), \at(n,Pre));
        loop assigns x, y, tmp;
        loop invariant x-y <= INT_MAX;
    */
    while (x != y) {
        if (x < y) {
            tmp = x;
            x = y;
            y = tmp;
        }
        x = x - y;
    }
    return x;
}