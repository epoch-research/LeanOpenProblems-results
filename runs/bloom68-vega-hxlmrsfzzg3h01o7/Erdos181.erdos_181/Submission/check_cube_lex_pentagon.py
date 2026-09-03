#!/usr/bin/env python3
"""Exact checks of explicit lex-C5 cube embeddings; no embedding search.

The all-dimensional proof is in CubeLexPentagonAttempt.md. Bits are numbered
from least significant to most significant, so x >> 1 is the parity-class rank.
"""

from itertools import combinations


def base_five_word(value: int, length: int) -> tuple[int, ...]:
    assert 0 <= value < 5**length
    digits = [0] * length
    for j in range(length - 1, -1, -1):
        value, digits[j] = divmod(value, 5)
    assert value == 0
    return tuple(digits)


def first_difference_colour(u: tuple[int, ...], v: tuple[int, ...]) -> str:
    assert len(u) == len(v)
    for a, b in zip(u, v):
        if a != b:
            return "red" if (a - b) % 5 in (1, 4) else "blue"
    raise AssertionError("The host has no loops")


def embedding(x: int, d: int, t: int, colour: str) -> tuple[int, ...]:
    assert colour in ("red", "blue")
    assert 0 <= x < 2**d
    assert 2 ** (d - 1) <= 5 ** (t - 1)
    parity = x.bit_count() % 2
    first = parity if colour == "red" else 2 * parity
    return (first,) + base_five_word(x >> 1, t - 1)


def check_colour_swap() -> None:
    # Multiplication by 2 is a digit permutation and swaps every digit-pair
    # colour; coordinatewise it therefore swaps the lexicographic colours.
    assert {(2 * a) % 5 for a in range(5)} == set(range(5))
    for a, b in combinations(range(5), 2):
        assert first_difference_colour((a,), (b,)) != first_difference_colour(
            ((2 * a) % 5,), ((2 * b) % 5,)
        )


def check_explicit_embedding(t: int, colour: str) -> tuple[int, int, int]:
    s = 5 ** (t - 1)
    # bit_length(s) = 1 + floor(log_2(s)), exactly for every integer s >= 1.
    d = s.bit_length()
    n = 5**t
    order = 2**d
    assert order // 2 <= s < order
    assert order <= n
    assert order <= 2 * s
    # The gap bound log_2(n) - d < log_2(5) in exact multiplicative form.
    assert n < 5 * order
    assert d >= n.bit_length() - 1 - 2

    images = [embedding(x, d, t, colour) for x in range(order)]
    assert len(set(images)) == order
    assert all(len(w) == t and all(0 <= a < 5 for a in w) for w in images)

    # Decode (parity, rank) to check the explicit inverse as well.
    for x, image in enumerate(images):
        parity = image[0] if colour == "red" else image[0] // 2
        rank = 0
        for digit in image[1:]:
            rank = 5 * rank + digit
        low_bit = parity ^ (rank.bit_count() % 2)
        assert (rank << 1) | low_bit == x

    edges = 0
    for x in range(order):
        for j in range(d):
            y = x ^ (1 << j)
            if x < y:
                # In particular, every source edge crosses the first classes.
                assert images[x][0] != images[y][0]
                assert first_difference_colour(images[x], images[y]) == colour
                edges += 1
    assert edges == d * 2 ** (d - 1)
    return d, order, edges


def main() -> None:
    check_colour_swap()
    print("Colour-swapping digit permutation: PASS (all 10 digit pairs)")
    print("Explicit injections; every required edge checked in BOTH colours")
    print("t | N=5^t | d_t | cube vertices | cube edges per colour | status")
    total_edges = 0
    for t in range(1, 9):
        red = check_explicit_embedding(t, "red")
        blue = check_explicit_embedding(t, "blue")
        assert red == blue
        d, order, edges = red
        total_edges += 2 * edges
        print(f"{t} | {5**t} | {d} | {order} | {edges} | PASS")
    print(f"Total required edge-colour checks: {total_edges}")
    print("PASS: dimensions, capacities, word validity, injectivity, inverse, edges")
    print("No search performed. All-t theorem proved in CubeLexPentagonAttempt.md.")


if __name__ == "__main__":
    main()
