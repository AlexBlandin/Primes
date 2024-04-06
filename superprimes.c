#include <stdio.h>
#include <stdlib.h>

#include "s.h"

#include "superprimes.h"

int is_prime_2_64(u64 n) {
  if (n == 2 || n == 3 || n == 5 || n == 7) return true;
  if (n % 2 == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0) return false;
  if (n < 121) return (n > 1);
  return is_SPRP(2ull, n) && is_SPRP(bases[hashh(n)], n);
}

int main(void) {
  u32 count = 0;
  u32 X = 100000000; // 2000000000 takes half an hour on an 8700k for prime
  for (u64 i = X; i--; count += is_prime_2_64(i)) // about 2x faster
    ;
  printf("%d", count);
}
