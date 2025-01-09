"""
primes.

Copyright 2019 Alex Blandin
"""

import contextlib
import math
import re
from collections.abc import Callable
from itertools import islice
from math import log
from random import randrange
from time import time

try:
  from gmpy2 import bit_scan1 as ctz
except ModuleNotFoundError:

  def ctz(v):  # noqa: ANN001, ANN201, D103
    return (v & -v).bit_length() - 1


def isqrt(n):  # noqa: ANN001, ANN201, D103
  x, y = n, (n + 1) // 2
  while y < x:
    x, y = y, (y + n // y) // 2
  return x


def ilog2(x):  # noqa: ANN001, ANN201, D103
  return x.bit_length() - 1


def easyprime(n):  # noqa: ANN001, ANN201, D103
  if n in {2, 3, 5, 7}:
    return True
  if not n & 1 or not n % 3 or not n % 5 or not n % 7:
    return False
  if n < 121:  # noqa: PLR2004
    return n > 1

  sqrt = isqrt(n)
  assert sqrt * sqrt <= n  # noqa: S101
  return all(not (not n % i or not n % (i + 2)) for i in range(11, sqrt + 1, 6))


def regexprime(n) -> bool:  # DO NOT RUN ON PRIMES LARGER THAN 2**19-1, YOUR COMPUTER WILL EXPLODE  # noqa: ANN001, D103
  return not re.match(r"^1?$|^(11+?)\1+$", "1" * n)


def probprime(n, trials=8):  # noqa: ANN001, ANN201, C901, PLR0912
  """Miller-Rabin primality test.

  - Returns False when n is not prime.
  - Returns True when n is a prime < 3317044064679887385961981, or otherwise when n is very likely a prime.

  Increase the number of trials to increase the confidence for n > 3317044064679887385961981
  """
  if n in {2, 3, 5, 7}:
    return True
  if not (n & 1) or not (n % 3) or not (n % 5) or not (n % 7):
    return False
  if n < 121:  # noqa: PLR2004
    return n > 1

  d = n - 1
  s = ctz(d)
  d >>= s

  # assert(2**s * d == n-1)

  def witness(a):  # noqa: ANN001, ANN202
    if pow(a, d, n) == 1:
      return False
    return all(pow(a, 2**i * d, n) != n - 1 for i in range(s))

  if n < 2047:  # noqa: PLR2004
    b = [2]
  elif n < 1373653:  # noqa: PLR2004
    b = [2, 3]
  elif n < 9080191:  # noqa: PLR2004
    b = [31, 73]
  elif n < 25326001:  # noqa: PLR2004
    b = [2, 3, 5]
  elif n < 3215031751:  # noqa: PLR2004
    b = [2, 3, 5, 7]
  elif n < 4759123141:  # noqa: PLR2004
    b = [2, 7, 61]
  elif n < 1122004669633:  # noqa: PLR2004
    b = [2, 13, 23, 1662803]
  elif n < 2152302898747:  # noqa: PLR2004
    b = [2, 3, 5, 7, 11]
  elif n < 3474749660383:  # noqa: PLR2004
    b = [2, 3, 5, 7, 11, 13]
  elif n < 341550071728321:  # noqa: PLR2004
    b = [2, 3, 5, 7, 11, 13, 17]
  elif n < 318665857834031151167461:  # noqa: PLR2004
    b = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]  # covers 64bit
  elif n < 3317044064679887385961981:  # noqa: PLR2004
    b = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
  else:
    b = [2] + [randrange(3, n, 2) for _ in range(trials)]

  return all(not witness(a) for a in b)


def millerprime(n) -> bool:  # noqa: ANN001, D103
  if n < 2 or not n & 1:  # noqa: PLR2004
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
  r, d = next(
    (r, d) for r, d in enumerate((n - 1) // 2**r for r in range((n - 1).bit_length())) if d & 1 and n == 2**r * d + 1
  )
  assert n == 2**r * d + 1  # noqa: S101
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
    if x in {1, n - 1}:
      continue
    for _ in range(r - 1):
      x = pow(x, 2, n)
      if x == n - 1:
        break
    else:
      return False
  return True


def aksprime(n) -> bool:  # noqa: ANN001
  """Not the actual AKS-primality test (poly-time), but a reduced version."""
  if n == 2:  # noqa: PLR2004
    return True
  c = 1
  for i in range(n // 2 + 1):
    c *= (n - i) // (i + 1)
    if c % n:
      return False
  return True


# sieve, factor, and iter_index are recipes given by python's itertools (iter_index is also in more-itertools)
def sieve(n):  # noqa: ANN001, ANN201
  "Primes less than n."
  # sieve(30) → 2 3 5 7 11 13 17 19 23 29
  if n > 2:  # noqa: PLR2004
    yield 2
  data = bytearray((0, 1)) * (n // 2)
  for p in iter_index(data, 1, start=3, stop=math.isqrt(n) + 1):
    data[p * p : n : p + p] = bytes(len(range(p * p, n, p + p)))
  yield from iter_index(data, 1, start=3)


def factor(n):  # noqa: ANN001, ANN201
  "Prime factors of n."
  # factor(99) → 3 3 11
  # factor(1_000_000_000_000_007) → 47 59 360620266859
  # factor(1_000_000_000_000_403) → 1000000000000403
  for prime in sieve(math.isqrt(n) + 1):
    while not n % prime:
      yield prime
      n //= prime
      if n == 1:
        return
  if n > 1:
    yield n


def iter_index(iterable, value, start=0, stop=None):  # noqa: ANN001, ANN201
  "Return indices where a value occurs in a sequence or iterable."
  # iter_index('AABCADEAF', 'A') → 0 1 4 7
  seq_index = getattr(iterable, "index", None)
  if seq_index is None:
    iterator = islice(iterable, start, stop)
    for i, element in enumerate(iterator, start):
      if element is value or element == value:
        yield i
  else:
    stop = len(iterable) if stop is None else stop
    i = start
    with contextlib.suppress(ValueError):
      while True:
        yield (i := seq_index(value, i, stop))
        i += 1


def reciprime(n):  # noqa: ANN001, ANN201
  "Uses the recipies from the python's itertools stdlib module."
  return len(list(factor(n))) == 1


def tf(func: Callable, *args, __pretty_tf=True, **kwargs):  # noqa: ANN001, ANN002, ANN003, ANN201
  """Time func func, as in, func to time the function func."""
  start = time()
  r = func(*args, **kwargs)
  end = time()
  if __pretty_tf:
    fargs = list(map(str, (a.__name__ if hasattr(a, "__name__") else a for a in args))) + [
      f"{k}={v}" for k, v in kwargs.items()
    ]
    print(f"{func.__qualname__}({', '.join(fargs)}) = {r} ({human_time(end - start)})")  # noqa: T201
  else:
    print(human_time(end - start))  # noqa: T201
  return r


def human_time(t: float, *, seconds: bool = True) -> str:
  """Because nobody makes it humanly readable."""
  return (
    f"{t // 60:.0f}m {t % 60:.3f}s"
    if t > 60  # noqa: PLR2004
    else f"{t:.3f}s"
    if t > 0.1 and seconds  # noqa: PLR2004
    else f"{t * 1000:.3f}ms"
    if t > 0.0001  # noqa: PLR2004
    else f"{t * 10**6:.3f}us"
  )


def main() -> None:
  """
  The ideal is I make something that has parity with Wolfram's PrimeQ.

  - Miller under 3317044064679887385961981 (~10**24)
  - Atkin-Morain under 10**50 (so not even lil_prime)
  - Pollard P test, Pollard Rho test.

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
  lil_prime = 4547337172376300111955330758342147474062293202868155909489
  # Big prime, a 332 bit prime (~10**99)
  big_prime = 6513516734600035718300327211250928237178281758494417357560086828416863929270451437126021949850746381
  # Bigger prime, a 697 bit prime (~10**209)
  bigger_prime = 643808006803554439230129854961492699151386107534013432918073439524138264842370630061369715394739134090922937332590384720397133335969549256322620979036686633213903952966175107096769180017646161851573147596390153  # noqa: E501

  print(tiny_prime, pico_prime, lil_prime, big_prime, bigger_prime)  # noqa: T201

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
