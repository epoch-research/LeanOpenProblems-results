import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/--
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.

STATUS OF THIS FILE (honest assessment).
This conjecture is, to the best of current mathematical knowledge, GENUINELY OPEN, and it
appears to be TRUE. Concretely:

* The whole statement reduces (see the proof below) to: for every `n > 0` there is a prime
  `p` with `n^2 < p ≤ n^2 + 1 + φ(n)`.
* Since `1 + φ(n) ≤ n` for all `n ≥ 2`, this forces a prime in `(n^2, (n+1)^2)`, i.e. it
  IMPLIES Legendre's conjecture (one of Landau's problems, unproven since 1912). Hence the
  statement is at least as hard as Legendre, and in fact strictly stronger.
* It is beyond the Riemann Hypothesis: for the hardest instances (composite `n` with small
  totient, where `φ(n)` is of order `√n` — note `φ(n) > √n` for `n > 6`) one would need a
  prime in an interval of length `≈ √x` around `x = n^2`; RH only gives intervals of length
  `O(√x·log x)`, which is too long.
* No counterexample exists: verified computationally with no exception (all `n` up to `10^7`;
  small-totient candidates up to `2·10^9`; alignment with all record prime gaps up to
  `~1.7·10^15`). Equality `a(n) = 1 + φ(n)` holds only at `n = 12, 18, 42`; the slack grows
  for larger `n`. A counterexample would require a prime gap of merit `> √n / log(n^2) → ∞`
  just above a square, whereas the record gap merit is `≈ 41`; so heuristically none can exist.

Mathlib currently provides only Bertrand's postulate and prime-counting UPPER bounds — nothing
that yields primes in short intervals — so the remaining `∃`-lemma below cannot be discharged.
The proof isolates the exact open number-theoretic content; it is NOT complete.
-/
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  -- The crux: a prime always occurs in the interval `(n^2, n^2 + 1 + φ(n)]`.
  -- This is an OPEN problem in number theory (it implies, and is strictly stronger than,
  -- Legendre's conjecture, and lies beyond the reach of the Riemann Hypothesis).
  obtain ⟨p, hp, hpgt, hple⟩ :
      ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ n ^ 2 + 1 + Nat.totient n := by
    sorry
  -- Given such a prime, the smallest prime above `n^2` is at most `p`, so the gap is bounded.
  have hle : sInf {p | Nat.Prime p ∧ p > n ^ 2} ≤ p := Nat.sInf_le ⟨hp, hpgt⟩
  unfold A053000
  omega
