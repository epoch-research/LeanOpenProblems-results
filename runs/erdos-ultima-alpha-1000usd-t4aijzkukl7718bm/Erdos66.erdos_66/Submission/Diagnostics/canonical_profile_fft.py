"""Finite diagnostic only: canonical floor rounding of sqrt(sum H_(n+1) z^n).

Profile coefficients and floor decisions use floating point.  The integer
representation counts are recovered by rounding an FFT convolution and
checked for parity.  This script proves nothing about the infinite set.
"""
import argparse
import numpy as np
from scipy.signal import fftconvolve


def conv(a, b, n):
    return fftconvolve(a, b)[:n]


def inverse(f, n):
    g = np.array([1.0 / f[0]], dtype=f.dtype)
    while len(g) < n:
        m = min(2 * len(g), n)
        fg = conv(f[:m], g, m)
        if len(fg) < m:
            fg = np.pad(fg, (0, m-len(fg)))
        fg[0] -= 2.0
        g = -conv(g, fg, m)
    return g


def harmonic_root(n, dtype=np.float64):
    h = np.cumsum(1.0 / np.arange(1, n+1, dtype=dtype))
    f = np.array([1.0], dtype=dtype)
    while len(f) < n:
        old = len(f)
        m = min(2 * old, n)
        g = inverse(f, m)
        ff = conv(f, f, m)
        if len(ff) < m:
            ff = np.pad(ff, (0, m-len(ff)))
        residual = h[:m] - ff
        residual[:old] = 0.0
        correction = 0.5 * conv(residual, g, m)
        f = np.pad(f, (0, m-old)) + correction
    return f, h


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--power', type=int, default=20)
    ap.add_argument('--extended', action='store_true')
    ap.add_argument('--save')
    args = ap.parse_args()
    n = 2 ** args.power
    p, h = harmonic_root(n+1, np.longdouble if args.extended else np.float64)
    discrepancy = conv(p, p, n+1) - h
    cumulative = np.concatenate(([0.0], np.cumsum(p)))
    counts = np.floor(cumulative).astype(np.int64)
    bits = np.diff(counts)
    assert np.all((bits == 0) | (bits == 1))
    raw_r = conv(bits.astype(float), bits.astype(float), n+1)
    r = np.rint(raw_r).astype(np.int64)
    assert np.all(r[1::2] % 2 == 0)
    assert np.all(r[::2] % 2 == bits[:len(r[::2])])
    print('FINITE FLOATING-POINT DIAGNOSTIC; NO INFINITE CLAIM')
    print('N', n, 'cardinality', int(bits.sum()), 'dtype', p.dtype)
    if args.save:
        np.savez_compressed(args.save, bits=bits, cumulative=cumulative, r=r)
    print('profile convolution max residual', float(np.max(np.abs(discrepancy))))
    print('representation FFT max rounding residual', float(np.max(np.abs(raw_r-r))))
    interior = cumulative[2:]
    print('minimum noninitial distance to integer', float(np.min(np.abs(interior-np.rint(interior)))))
    print('dyadic_window min_ratio max_ratio max_abs_error/sqrt_log zeros')
    for k in range(10, args.power+1):
        lo, hi = 2**(k-1), 2**k
        idx = np.arange(lo, hi+1)
        logs = np.log(idx)
        ratio = r[idx] / logs
        err = (r[idx]-logs) / np.sqrt(logs)
        print(lo, hi, float(ratio.min()), float(ratio.max()),
              float(np.max(np.abs(err))), int(np.count_nonzero(r[idx]==0)))
    for name, i in [('maximum_ratio', np.argmax(r[n//2:]/np.log(np.arange(n//2,n+1)))+n//2),
                    ('minimum_ratio', np.argmin(r[n//2:]/np.log(np.arange(n//2,n+1)))+n//2)]:
        inds = np.flatnonzero(bits[:i+1] & bits[i::-1])
        print(name, 'n', i, 'r', r[i], 'ratio', r[i]/np.log(i), 'endpoints', inds.tolist())

if __name__ == '__main__':
    main()
