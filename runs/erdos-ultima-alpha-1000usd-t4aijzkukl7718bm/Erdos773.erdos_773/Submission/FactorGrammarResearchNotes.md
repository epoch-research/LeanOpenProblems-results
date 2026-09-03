# Factorization and binary-grammar continuation

This continuation did not settle Erdős 773 or improve a main-gap exponent.
`Spec.lean` was not modified, and no proof submission was made.

## Factorization route

The identity b^2-a^2=(b-a)(b+a) was reconsidered as a way of selecting
canonical factorizations. No theorem giving a near-linear root selector was
obtained. Prime roots and bounded representation multiplicities are already
known not to supply the missing argument by themselves. In particular, the
existing fractional capacity result still has no proved integral rounding
with subpower loss.

## Exact grammar screens

The script `/tmp/square_digit_grammar.py` checks every unordered pair,
including repeats, in each candidate class. Output is in
`/tmp/square_digit_grammar.log`. These are exploratory integer computations,
not new Lean theorems.

* Binary expansions with no adjacent 1s fail at six bits:

      4^2 + 33^2 = 9^2 + 32^2 = 1105.

  The words are 100, 100001, 1001, and 100000.

* Binary expansions with every run of 1s of even length fail at seven bits:

      12^2 + 99^2 = 27^2 + 96^2 = 9945.

  The words are 1100, 1100011, 11011, and 1100000.
  This is the preceding numerical collision scaled by 3.

* Base-four expansions using only digits 0 and 1 fail at seven binary bits:

      1^2 + 68^2 = 20^2 + 65^2 = 4625.

  The base-four words are 1, 1010, 110, and 1001.
  Symbolically the difference of these square sums, with 4 replaced by B,
  is B^3*(B-4); it is not a formal polynomial identity.

No claim is made that these failures rule out more complicated digit codes.
The outstanding goal remains actual N^(1-o(1)) Sidon roots, or a fixed
positive exponent loss along an unbounded sequence. The admission remains
for 0 < epsilon <= 1/3.
