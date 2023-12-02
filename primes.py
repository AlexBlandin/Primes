from collections.abc import Callable
from random import randrange
from time import time
from math import log
import re

from primes_extra import superprime  # noqa: F401

try:
  from gmpy2 import bit_scan1 as ctz  # type: ignore
except ModuleNotFoundError:

  def ctz(v):
    return (v & -v).bit_length() - 1


def isqrt(n):
  x, y = n, (n + 1) // 2
  while y < x:
    x, y = y, (y + n // y) // 2
  return x


def ilog2(x):
  return x.bit_length() - 1


def easyprime(n):
  if n in {2, 3, 5, 7}:
    return True
  if not n & 1 or not n % 3 or not n % 5 or not n % 7:
    return False
  if n < 121:
    return n > 1

  sqrt = isqrt(n)
  assert sqrt * sqrt <= n
  for i in range(11, sqrt, 6):
    if not n % i or not n % (i + 2):
      return False
  return True


def regexprime(n):  # DO NOT RUN ON PRIMES LARGER THAN 2**19-1, YOUR COMPUTER WILL EXPLODE
  return not re.match(r"^1?$|^(11+?)\1+$", "1" * n)


def probprime(n, trials=8):
  """
  Miller-Rabin primality test.

  - Returns False when n is not prime.
  - Returns True when n is a prime < 3317044064679887385961981, or otherwise when n is very likely a prime.

  Increase the number of trials to increase the confidence for n > 3317044064679887385961981
  """

  if n in {2, 3, 5, 7}:
    return True
  if not (n & 1) or not (n % 3) or not (n % 5) or not (n % 7):
    return False
  if n < 121:
    return n > 1

  d = n - 1
  s = ctz(d)
  d >>= s

  # assert(2**s * d == n-1)

  def witness(a):
    if pow(a, d, n) == 1:
      return False
    for i in range(s):
      if pow(a, 2**i * d, n) == n - 1:
        return False
    return True

  if n < 2047:
    b = [2]
  elif n < 1373653:
    b = [2, 3]
  elif n < 9080191:
    b = [31, 73]
  elif n < 25326001:
    b = [2, 3, 5]
  elif n < 3215031751:
    b = [2, 3, 5, 7]
  elif n < 4759123141:
    b = [2, 7, 61]
  elif n < 1122004669633:
    b = [2, 13, 23, 1662803]
  elif n < 2152302898747:
    b = [2, 3, 5, 7, 11]
  elif n < 3474749660383:
    b = [2, 3, 5, 7, 11, 13]
  elif n < 341550071728321:
    b = [2, 3, 5, 7, 11, 13, 17]
  elif n < 318665857834031151167461:
    b = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]  # covers 64bit
  elif n < 3317044064679887385961981:
    b = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
  else:
    b = [2] + [randrange(3, n, 2) for _ in range(trials)]

  for a in b:
    if witness(a):
      return False
  return True
  # return not any(witness(a) for a in b)


def millerprime(n):
  if n < 2 or not n & 1:
    return False

  # if n < 2047: b = [2]
  # elif n < 1373653: b = [2, 3]
  # elif n < 9080191: b = [31, 73]
  # elif n < 25326001: b = [2, 3, 5]
  # elif n < 3215031751: b = [2, 3, 5, 7]
  # elif n < 4759123141: b = [2, 7, 61]
  # elif n < 1122004669633: b = [2, 13, 23, 1662803]
  # elif n < 2152302898747: b = [2, 3, 5, 7, 11]
  # elif n < 3474749660383: b = [2, 3, 5, 7, 11, 13]
  # elif n < 341550071728321: b = [2, 3, 5, 7, 11, 13, 17]
  # elif n < 318665857834031151167461: b = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] # covers 64bit
  # elif n < 3317044064679887385961981: b = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
  # else: b = range(2, min(n-2, int(2*log(n)**2))+1)
  b = range(2, min(n - 2, int(2 * log(n) ** 2)) + 1)  # to test if above is somehow broken

  # write n as 2^r d + 1 with d odd (by factoring out powers of 2 from n - 1)
  r, d = next((r, d) for r, d in enumerate(map(lambda r: (n - 1) // 2**r, range((n - 1).bit_length()))) if d & 1 and n == 2**r * d + 1)
  assert n == 2**r * d + 1
  # def trial_composite(a):
  #   if pow(a, d, n) == 1:
  #     return False
  #   for i in range(s):
  #     if pow(a, 2**i * d, n) == n-1:
  #       return False
  #   return True
  for a in b:
    # if trial_composite(a):
    #   return False
    x = pow(a, d, n)
    if x == 1 or x == n - 1:
      continue
    for _ in range(r - 1):
      x = pow(x, 2, n)
      if x == n - 1:
        break
    else:
      return False
  return True


def aksprime(n):
  """Not the actual AKS-primality test (poly-time), but a reduced version"""
  if n == 2:
    return True
  c = 1
  for i in range(n // 2 + 1):
    c *= (n - i) // (i + 1)
    if c % n:
      return False
  return True


def tf(func: Callable, *args, __pretty_tf=True, **kwargs):
  """time func func, as in, func to time the function func"""
  start = time()
  r = func(*args, **kwargs)
  end = time()
  if __pretty_tf:
    fargs = list(map(str, map(lambda a: a.__name__ if hasattr(a, "__name__") else a, args))) + [f"{k}={v}" for k, v in kwargs.items()]
    print(f"{func.__qualname__}({", ".join(fargs)}) = {r} ({human_time(end - start)})")
  else:
    print(human_time(end - start))
  return r


def human_time(t: float, seconds=True):
  """because nobody makes it humanly readable"""
  return f"{t // 60:.0f}m {t % 60:.3f}s" if t > 60 else f"{t:.3f}s" if t > 0.1 and seconds else f"{t * 1000:.3f}ms" if t > 0.0001 else f"{t * 10**6:.3f}us"


def main():
  """
  The ideal is I make something that has parity with Wolfram's PrimeQ
  - Miller under 3317044064679887385961981 (~10**24)
  - Atkin–Morain under 10**50 (so not even lil_prime)
  - Pollard P test, Pollard Rho test
  """
  """
  Timings table (in seconds on an 8700k), pyjion can't handle bigints right now
  Tested: cpython 3.10.0, pypy 3.7.4 (7.3.2-alpha0), pyjion 1.0.0 w/ .NET 6.0.0
  
  ----------------------------------------------------------------------
  |        |           easyprime         |         superprime          |
  | Prime! |-----------------------------|-----------------------------|
  |        | cpython |   pypy  |  pyjion | cpython |   pypy  |  pyjion |
  |--------|-----------------------------|-----------------------------|
  |  tiny  | 4.016ms | 4.963ms |         |         |         |         |
  |  pico  | 158.93s |  79.90s | 108.42s |         |         |         |
  |   lil  |         |         |   N/A   |         |         |   N/A   |
  |   big  |         |         |   N/A   |         |         |   N/A   |
  | bigger |         |         |   N/A   |         |         |   N/A   |
  ----------------------------------------------------------------------
  """
  # Tiny prime, a 35 bit prime (~10**10), the billionth prime
  tiny_prime = 22801763489
  # Pico prime, a 63 bit prime (~10**18), the 200000000000000000th prime
  pico_prime = 8512677386048191063
  # Lil' prime, a 192 bit prime (~10**57), even if I call it lil', it's ~5600x the size of the Monster Group
  lil_prime = 4547337172376300111955330758342147474062293202868155909489  # noqa: F841
  # Big prime, a 332 bit prime (~10**99)
  big_prime = 6513516734600035718300327211250928237178281758494417357560086828416863929270451437126021949850746381  # noqa: F841
  # Bigger prime, a 697 bit prime (~10**209)
  bigger_prime = 643808006803554439230129854961492699151386107534013432918073439524138264842370630061369715394739134090922937332590384720397133335969549256322620979036686633213903952966175107096769180017646161851573147596390153  # noqa: F841, E501

  prime = tiny_prime or pico_prime
  test = (probprime,)  # easyprime, # superprime, # millerprime, # aksprime, # regexprime,
  for t in test:
    tf(t, prime)
  for t in test:
    tf(sum, map(t, range(250000)))

  # superprime is not working
  # millerprime is super slow
  # aksprime is super slow
  # regexprime? DO NOT USE UNLESS YOU HAVE INFINITE MEMORY


if __name__ == "__main__":
  main()
