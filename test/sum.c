#include <stdio.h>
#define printInt(e) printf("%d\n",e)

int main () {
  int n = 100;
  int sum = 0;
  int k   = 0;
  while (n > k) {
    k   = k + 1;
    sum = sum + k;
  }
  printInt(sum);
}
