#include <stdio.h>
#include <limits.h>
 /*
7,9,3,1,10,6,5,4
​
j   i 	arr
==========================
0 	-1  {7,9,3,1,10,6,5,4}
1 	-1  {7,9,3,1,10,6,5,4}
2 	-1  {7,9,3,1,10,6,5,4}
3     0  {3,9,7,1,10,6,5,4}
4     1  {3,1,7,9,10,6,5,4}
5     1  {3,1,7,9,10,6,5,4}
6     1  {3,1,7,9,10,6,5,4}
            {3,1,4,9,10,6,5,7}
             ensures \forall integer k; \result <= k<= r ==> a[k] >= \old(a[r]) ;
*/
/*@ requires \valid(a+(p..r));
    requires r >p;
    requires r > 0;
    requires r < INT_MAX;
    requires p >= 0;
    requires p+1 < INT_MAX;
    ensures \forall integer k; p<= k <=\result-1   ==> a[k] <= \old(a[r]) ;
   
    assigns a[p..r];
*/
 void QuickSort(int *a, int p, int r){
    if(p>r){
        int q = partition(a, p, r);
        QuickSort(a,p,q-1);
        QuickSort(a,q+1,r);
    }
 }
int partition(int *a, int p, int r) {
​
    int x = a[r];
    int i = p-1;
    int temp;
    /* loop invariant \forall integer k; p<=k<=i ==> a[k] <= a[r] && i < p <=k < r  ;*/
    /*@ 
        loop invariant \forall integer k; p <= k <= i ==> a[k] <= x;
        loop invariant \valid(a+(p..r-1));
        loop invariant i==p-1 || p<=i<=r-1;
        loop invariant p<=j<=r;
        loop invariant i<j;
	    loop assigns j, i, temp, a[p..r-1];
        loop variant r-j;
        
    */
    for(int j = p; j < r; j++){
        if(a[j] <= x){
            i = i+1;
            temp = a[i];
	        a[i] = a[j];
	        a[j] = temp;
        }
    }
    temp = a[r];
    a[r] = a[i+1];
    a[i+1] = temp;
    return i+1;
}
​
​
int main(){
    int arr[8] = {7,9,3,1,10,6,5,4};
    int p=0;
    int r=7;
    QuickSort(arr,p,r);
    for (int j=0;j<8;j++){
        printf("%d\n",arr[j]);
    }
​
}
