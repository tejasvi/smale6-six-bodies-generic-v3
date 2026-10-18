#!/usr/bin/env python3
"""Exact text form of the complex arrays of approximate solutions (k4_sols_1_2_3_30.txt, kc/kc_sols_1_2_3_30.txt),
which replace the original NumPy .npy files. Line 1 is a comment, line 2 is 'shape ROWS COLS', then one row per line,
each entry as its real and imaginary part in float.hex, so the values are exact.

  load_array(path)          -> numpy complex128 array (bit for bit the array of the original .npy file)
  save_array(path, array)   writes the text form
  arrayio.py SOLS.npy OUT.txt   converts a .npy file (and checks the round trip bit for bit)"""
import sys
import numpy as np


def save_array(path, a):
    a = np.asarray(a)
    assert a.dtype == np.complex128 and a.ndim == 2, (a.dtype, a.shape)
    with open(path, 'w') as f:
        f.write('# complex128 array; each entry as real and imaginary part in float.hex\n')
        f.write(f'shape {a.shape[0]} {a.shape[1]}\n')
        for row in a:
            f.write(' '.join(f'{float(z.real).hex()} {float(z.imag).hex()}' for z in row) + '\n')


def load_array(path):
    with open(path) as f:
        head = f.readline()
        assert head.startswith('#'), head
        tag, r, c = f.readline().split()
        assert tag == 'shape'
        r, c = int(r), int(c)
        a = np.empty((r, c), dtype=np.complex128)
        for i in range(r):
            v = f.readline().split()
            assert len(v) == 2 * c, (i, len(v))
            a[i] = [complex(float.fromhex(v[2 * j]), float.fromhex(v[2 * j + 1])) for j in range(c)]
        assert f.read() == '', 'trailing data'
    return a


if __name__ == '__main__':
    src, out = sys.argv[1], sys.argv[2]
    a = np.load(src)
    save_array(out, a)
    b = load_array(out)
    assert a.shape == b.shape and a.dtype == b.dtype and a.tobytes() == b.tobytes(), 'round trip differs'
    print(f'{src}: {a.shape} {a.dtype} -> {out}; round trip bit for bit')
