#include <stdio.h>
#define printInt(e) printf("%d\n",e)

int main () {
  int n = 10;
  int i = 0;
  int j = 1;
  int h = 0;
  while (n > 0) {
    h = i;
    i = j;
    j = j + h;
    n = n - 1;
  }
  printInt(i);
}
