// Common greatest divisor.

#include <stdio.h>
#define printInt(e) printf("%d\n",e)

int main () {
  int a = 540;     // The bigger number.
  int b = 100;     // The smaller number.
  int h = 0;       // Auxiliary variable.
  while (b > 0) {  // Precondition: b <= a.
    a = a - b;
    // If b is now greater than a, swap a and b.
    if (b > a) { h = a; a = b; b = h; } else {}
  }
  printInt(a);    // Should print the gcd of the original a and b.
}

