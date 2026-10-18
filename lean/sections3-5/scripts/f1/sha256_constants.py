#!/usr/bin/env python3
"""Prints the SHA-256 constants (FIPS 180-4, 4.2.2 and 5.3.3) in Lean syntax, computed with integer roots:
K[t] = the first 32 bits of the fractional part of the cube root of the t-th prime (t < 64),
H0[i] = the first 32 bits of the fractional part of the square root of the i-th prime (i < 8)."""
from math import isqrt


def icbrt(x):
    lo, hi = 0, 1
    while hi ** 3 <= x:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** 3 <= x:
            lo = mid
        else:
            hi = mid
    return lo


primes = []
k = 2
while len(primes) < 64:
    if all(k % p for p in primes):
        primes.append(k)
    k += 1
K = [icbrt(p << 96) & 0xffffffff for p in primes]
H = [isqrt(p << 64) & 0xffffffff for p in primes[:8]]
print('K := #[' + ', '.join('0x%08x' % x for x in K) + ']')
print('H0 := #[' + ', '.join('0x%08x' % x for x in H) + ']')
