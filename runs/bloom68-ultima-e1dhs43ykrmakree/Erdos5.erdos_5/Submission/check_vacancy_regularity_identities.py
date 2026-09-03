#!/usr/bin/env python3
"""Exhaustive finite checks for VacancyRegularityAttempt.md.

Every binary word is extended by zero outside its finite window.  No prime
asymptotics are tested or assumed.  All checks use exact integer arithmetic.
Run: python3 Submission/check_vacancy_regularity_identities.py [--max-length 10]
"""

from argparse import ArgumentParser
from collections import Counter
from functools import lru_cache


def check_word(word: int, size: int) -> int:
    def p(n: int) -> int:
        return (word >> n) & 1 if 0 <= n < size else 0

    @lru_cache(None)
    def mask(n: int, h: int) -> int:
        assert h >= 1
        lo, hi = max(n + 1, 0), min(n + h, size)
        if hi <= lo:
            return 1
        return int(word & (((1 << (hi - lo)) - 1) << lo) == 0)

    def empty(lo: int, hi: int) -> int:
        """Product of (1-p(i)) on the inclusive integer interval [lo,hi]."""
        return int(all(not p(i) for i in range(lo, hi + 1)))

    @lru_cache(None)
    def a(n: int, h: int) -> int:
        return p(n) * mask(n, h)

    @lru_cache(None)
    def t(h: int) -> int:
        if h <= 0:
            return 0
        return sum(a(n, h) * p(n + h) for n in range(size))

    @lru_cache(None)
    def u2(h: int) -> int:
        return sum(p(n) * p(n + h) for n in range(size))

    @lru_cache(None)
    def u3(k: int, h: int) -> int:
        assert 0 < k < h
        return sum(p(n) * p(n + k) * p(n + h) for n in range(size))

    positions = [n for n in range(size) if p(n)]
    gaps = [b - a for a, b in zip(positions, positions[1:])]
    counts = Counter(gaps)

    def vacancy(k: int) -> int:
        return sum(max(d - k, 0) for d in gaps)

    def tail(h: int) -> int:
        return sum(a(n, h) for n in range(size))

    cases = 0
    # Include shifts longer than the whole window, as well as small shifts.
    shifts = sorted(set(range(1, min(size + 1, 4) + 1)) | {size + 1})
    for h in range(1, size + 2):
        assert t(h) == counts[h]
        assert tail(h) - tail(h + 1) == t(h)
        assert vacancy(h - 1) - 2 * vacancy(h) + vacancy(h + 1) == t(h)

        # Exact first-prime decomposition of the original interior mask.
        for n in range(size):
            assert 1 - mask(n, h) == sum(
                p(n + k) * mask(n, k) for k in range(1, h)
            )

        for ell in shifts:
            for n in range(size):
                strip = empty(n + h, n + h + ell - 1)
                assert mask(n, h + ell) == mask(n, h) * strip
                assert 1 - strip == sum(
                    p(n + h + r) * empty(n + h, n + h + r - 1)
                    for r in range(ell)
                )

            dr = sum(
                a(n, h) * (p(n + h + ell) - p(n + h))
                for n in range(size)
            )
            br = sum(
                p(n) * p(n + h + r) * p(n + h + ell) * mask(n, h + r)
                for r in range(ell)
                for n in range(size)
            )
            br_product = sum(
                a(n, h) * p(n + h + ell)
                * (1 - empty(n + h, n + h + ell - 1))
                for n in range(size)
            )
            assert br == br_product >= 0
            assert t(h + ell) - t(h) == dr - br
            assert br <= sum(u3(h + ell - s, h + ell) for s in range(1, ell + 1))

            dl = sum(
                (p(n - ell) - p(n)) * mask(n, h) * p(n + h)
                for n in range(size)
            )
            bl_product = sum(
                p(n - ell) * p(n + h) * mask(n, h)
                * (1 - empty(n - ell + 1, n))
                for n in range(size)
            )
            # Last prime in the new left strip; its successor is n+h.
            bl = sum(
                p(n - ell) * p(n - ell + s) * p(n + h)
                * mask(n - ell + s, h + ell - s)
                for s in range(1, ell + 1)
                for n in range(size)
            )
            assert bl == bl_product >= 0
            assert t(h + ell) - t(h) == dl - bl
            assert bl <= sum(u3(s, h + ell) for s in range(1, ell + 1))
            assert dr - dl == br - bl

            # Summation by parts in the base point keeps a prime factor.
            translated = sum(
                p(n + h) * (a(n - ell, h) - a(n, h))
                for n in range(size)
            )
            assert dr == translated

            # Removing the mask leaves a full-width SIGNED triple remainder.
            interior_flux = sum(
                p(n) * p(n + k) * mask(n, k)
                * (p(n + h + ell) - p(n + h))
                for k in range(1, h)
                for n in range(size)
            )
            assert dr == u2(h + ell) - u2(h) - interior_flux
            cases += 1

    for ell in shifts:
        # Signed, nonconstant, finitely supported integer weights, zero at h<=0.
        def weight(h: int) -> int:
            return ((7 * h * h + 3 * h + word) % 17) - 8 if 1 <= h <= size + 2 else 0

        lhs = sum(weight(h) * (t(h + ell) - t(h)) for h in range(1, size + 3))
        rhs = sum(t(k) * (weight(k - ell) - weight(k)) for k in range(1, size + 3))
        assert lhs == rhs

    return cases


def main() -> None:
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-length", type=int, default=10)
    args = parser.parse_args()
    if args.max_length < 0:
        parser.error("--max-length must be nonnegative")
    words, cases = 0, 0
    for size in range(args.max_length + 1):
        for word in range(1 << size):
            cases += check_word(word, size)
            words += 1
    print(
        f"PASS: {words} binary words (lengths 0..{args.max_length}); "
        f"{cases} (word,h,ell) cases."
    )
    print(
        "Verified exact gap/vacancy/tail identities, nested masks, right/left "
        "strip expansions, triple majorants, boundary balance, base-point "
        "translation, full-mask removal, and signed summation by parts."
    )
    print("This checks finite algebra only; it does NOT establish Q3 or prime cancellation.")


if __name__ == "__main__":
    main()
