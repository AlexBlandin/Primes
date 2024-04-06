#include <limits.h>
#include <stdio.h>

#include "s.h"

/* modulo congruent to 24 after squaring for numbers under 2^63 */
u64 mc24_u63(u64 n) {
  n %= 24;
  long double x = n;
  u64 c = x * n / 24;
  i64 r = (i64)(n * n - c * 24) % 24;
  return (r < 0 ? r + 24 : r) + 23 % 24; // wrapped up
}

bool prime_mc24(u32 n) {
  if (n <= 2) return n == 2;
  if (!(n & 1)) return false;
  if (!(n % 3)) return n == 3;
  if (mc24_u63(n)) return false;
  for (u32 i = 5; i * i <= n; i += 6) {
    if (!(n % i) || !(n % (i + 2))) return false;
  }
  return true;
}

u64 forX(u64 X, bool p(u64)) {
  // 2000000000 takes half an hour on an 8700k for p = prime, 4.5m on a 4700U for p = fastprime
  // 250000 takes 0.1s on a Ryzen 4700U for p = millprime
  u64 count = 0;

  for (u64 i = X; i--; count += p(i))
    ;

  return count;
}

int main() {
  u64 count = 0;
  count = forX(250000, fastprime);
  printf("p(250000) = %ld\n", count);
  
  // count = forX(100000000, prime);
  // printf("p(100000000) = %ld\n", count);

  // count = forX(2000000000, fastprime);
  // printf("p(2000000000) = %ld\n", count);


  // for (u64 j = 200 * 10000; j--;) // just generate some reasonable average times
  //   count = forX(200, prime);
  // printf("p(200) = %ld\n", count);
}
