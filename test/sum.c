#include <stdio.h>
#define printInt(e) printf("%d\n",e)

int main () {
  int n = 100;
  int sum = 0;
  while (n > 0) {
    sum = sum + n;
    n = n - 1;
  }
  printInt(sum);
}
