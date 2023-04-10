#include <limits.h>

/* @
    requires n > 0;
    requires \valid( a + (0..n-1));
    requires \forall int i; a[i]+1 <= INT_MAX;
    requires \forall int i; 0 <= i <= n ==> a[i] <= a[i+1];
    ensures \forall int i; 0 <= i <= n ==> a[i] <= a[i+1];
    assigns a[0..n-1];
*/
void add1(int* a, int n) {
    int i;
/*@ 
    loop invariant 0 <= i <=n;
    loop invariant \forall int k; 0 <= k < i-1 ==> a[k] <= a[k+1];
    loop invariant \forall int k; i <= k < n-1 ==> a[k] <= a[k+1];
    loop invariant a[i-1] <= a[i]+1;
    loop invariant \forall int j; 0 <= j < n ==> a[j+1] - a[j] == \at(a[j+1],Pre) - \at(a[j],Pre);
    loop invariant \valid (a + i);
    loop assigns i, a[0..n-1];
    loop variant n-i-1;
    
*/
    for (i=0; i<n; i++){
        a[i]++;
    }
}
