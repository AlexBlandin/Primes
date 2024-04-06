#include "s.h"

#include "superprimes.h"

bool easy_prime(int n) { // my current "easy prime"
  if (n == 2 || n == 3 || n == 5 || n == 7) return true;
  if (!(n & 1) || !(n % 3) || !(n % 5) || !(n % 7)) return false;
  if (n < 121) return (n > 1);

  for (int i = 11; i * i <= n; i += 6)
    if (!(n % i) || !(n % (i + 2))) return false;

  return true;
}

u32 slow_powmod(u32 base, u32 exp, u32 mod) {
  u64 result = 0;
  for (int i = 0; i < exp; i++) {
    result *= base;
    result %= mod;
  }
  return result % mod;
}

u32 loop_ipowmod(u32 base, u32 exp, u32 mod) {
    u64 result = 1;
    for (;;) {
        if (exp & 1)
          result *= base;
        exp >>= 1;
        if (!exp)
          break;
        base *= base;
    }
    return result % mod;
}

u32 ipowmod(u8 base, u8 exp, u32 mod) {
    static const u8 highest_bit_set[] = {
        0, 1, 2, 2, 3, 3, 3, 3,
        4, 4, 4, 4, 4, 4, 4, 4,
        5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5,
        6, 6, 6, 6, 6, 6, 6, 6,
        6, 6, 6, 6, 6, 6, 6, 6,
        6, 6, 6, 6, 6, 6, 6, 6,
        6, 6, 6, 6, 6, 6, 6, 255, // anything past 63 is a guaranteed overflow
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
        255, 255, 255, 255, 255, 255, 255, 255,
    };
    
    u64 result = 1;
    switch (highest_bit_set[exp]) {
    case 255: // we use 255 as an overflow marker and return 0 on overflow/underflow
        if (base == 1) {
            return 1;
        }
        return 0;
    case 6:
        if (exp & 1) result *= base;
        exp >>= 1;
        exp >>= 1;
    case 5:
        if (exp & 1) result *= base;
        exp >>= 1;
        base *= base;
    case 4:
        if (exp & 1) result *= base;
        exp >>= 1;
        base *= base;
    case 3:
        if (exp & 1) result *= base;
        exp >>= 1;
        base *= base;
    case 2:
        if (exp & 1) result *= base;
        exp >>= 1;
        base *= base;
    case 1:
        if (exp & 1) result *= base;
    default:
        return result % mod;
    }
}

bool trial_composite(int a, int d, int s, int n) {
  if (ipowmod(a, d, n) == 1)
    return false;
  for (int i = 0; i<s; i++)
    if (ipowmod(a, (1<<i) * d, n) == n-1)
      return false;
  return true;
}

bool mill_prime(int n) {
  /*
  Miller primality test for signed ints (covers all i32).
  */
  
  if (n == 2 || n == 3 || n == 5 || n == 7) return true;
  if (!(n & 1) || !(n % 3) || !(n % 5) || !(n % 7)) return false;
  
  int s = 0;
  int d = n-1;
  while ((d % 2) == 0) {
    d >>= 1;
    s += 1;
  }
  assert((1<<s) * d == n-1);
  
  if (trial_composite(2, d, s, n) || trial_composite(3, d, s, n) || trial_composite(5, d, s, n) || trial_composite(6, d, s, n))
    return false;
  return true;
}

bool super_prime(u64 n) { // wtf
  if (n == 2 || n == 3 || n == 5 || n == 7) return true;
  if (n % 2 == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0) return false;
  if (n < 121) return (n > 1);
  return is_SPRP(2ull, n) && is_SPRP(bases[hashh(n)], n);
}

/*
 * Timing Data
 * build on 8700k ~4.3GHz                      | easyp(10^8) | millp(10^8) | super(10^8) |
 * clang easy_primes.c                         |    30.1s    |    00.0s    |    50.4s    |
 * clang -O2 easy_primes.c                     |    28.0s    |    00.0s    |    17.5s    |
 * clang -O2 -march=native easy_primes.c       |    25.9s    |    00.0s    |    17.6s    |
 * zig cc -O2 easy_primes.c                    |    27.5s    |    00.0s    |    20.5s    |
 * cosmo easy_primes.c                         |    26.0s    |    00.0s    |    21.9s    |
 */

int main(void) {
  printf("|<algo>(N)| = <#primes under N> for sanity checking\n");
  
  clock();
  double time;
  int count;
  const int X = 100000000; // X = 2000000000 takes half an hour @ 4GHz for easy prime
  
  time = dclock();
  count = 0;
  for (int i = X; i--; count += easy_prime(i))
    ;
  time = dclock() - time;
  printf("|easyp(%d)| = %d, took %.1fs\n", X, count, time / CLOCKS_PER_SEC);
  
  time = dclock();
  count = 0;
  for (int i = X; i--; count += mill_prime(i))
    ;
  time = dclock() - time;
  printf("|millp(%d)| = %d, took %.1fs\n", X, count, time / CLOCKS_PER_SEC);
  
  time = dclock();
  count = 0;
  for (int i = X; i--; count += super_prime(i))
    ;
  time = dclock() - time;
  printf("|super(%d)| = %d, took %.1fs\n", X, count, time / CLOCKS_PER_SEC);
  
  printf("\n");
  printf("Source @ https://repl.it/@alexblandin/Easy-Primality\n");
  return 0;
}
