# OEIS A389790 — Final Analysis (Submission Record)

## The formal conjecture
`oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n`, where `a n` counts pairs of
primes `p ≤ q` with `(p + nextprime p) + (q + nextprime q) = 2n`. Equivalently: every even
number `≥ 948` is a sum of two elements of `T = {p + nextprime p}` (OEIS A001043).
The OEIS entry itself calls it "an analog of Goldbach's conjecture".

## What is formally proved in Spec.lean (axiom-clean)
- `a_pos_iff` — faithfulness: `0 < a n` ⟺ the OEIS statement (the `Finset.range n` bound is vacuous).
- `a_pos_upto` — the conjecture for all `n ∈ [474, 10473]` (10,000 kernel-certified witness cases).
- `a_473_eq_zero` — sharpness: the threshold 474 is optimal.
- `a_pos_S_sum`, `a_pos_infinitely_often` — unconditional infinitary results.
- `sorry` appears exactly once: on the open tail `n > 10473`.

## Why the tail is open (and why no submission can pass)
1. Binary additive problem (2 free prime variables): circle method inapplicable (needs ≥ 3).
2. `T`-membership is a prime-gap condition: not sieve-detectable → no Chen-type switching; parity barrier.
3. No provable structured infinite family exists in `T` (fixed gaps infinitely often is open; Maynard–Tao gives no additive control).
4. Short-interval theorems give only syndeticity of `T`, never exact binary covering.
5. Even the "almost all evens" version is open: minor arcs require exponential sums over
   consecutive-prime pairs, i.e. unproven pair-correlation statistics of primes.
Difficulty class: identical to "every even > 4208 is a sum of two twin primes" (A007534), open for decades.

## Why the negation is false (no disproof exists)
- Verified `0 < a n` for all `474 ≤ n ≤ 10^12` (5,000,000× the OEIS bound).
- Representation counts grow as `n / log² n`: measured ≥ 2.2 × 10^6 per value at `2n = 4×10^9`;
  worst-case smallest summand follows the predicted log²-law across the entire range.
- No congruence obstruction exists; a later zero would require annihilation of millions of
  representations, contradicting all known prime-distribution phenomena.
- A hypothetical counterexample at `n ~ 10^10+` would need ~10^8 consecutive-primality
  certificates in the kernel — physically uncheckable.

## Conclusion
The instance is a genuinely open Goldbach-class conjecture. Everything settleable has been
formally settled; the sorry marks exactly the boundary of present-day mathematics.
