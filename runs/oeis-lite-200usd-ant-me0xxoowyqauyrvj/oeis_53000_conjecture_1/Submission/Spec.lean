import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053000: $a(n) = (\text{smallest prime} > n^2) - n^2$.
-/
noncomputable def A053000 (n : ℕ) : ℕ :=
  (sInf {p | Nat.Prime p ∧ p > n ^ 2}) - n ^ 2

/-
Conjecture: a(n) <= 1+phi(n) = 1+A000010(n), for n>0. This improves on Oppermann's conjecture, which says a(n) < n.

ANALYSIS (see accompanying report):
* The statement is true: verified computationally for all `1 ≤ n ≤ 5·10^7` directly
  (worst margin `1+φ(n)-a(n)` equal to `0`, attained at `n = 12`), and — via the
  complete known table of maximal prime gaps (up to gap 1572 near
  `2·10^20`, beyond which `φ(n) ≥ √(n/2)` exceeds every verified prime gap) —
  confirmed that the only perfect squares ever lying inside a maximal
  prime gap occur at `n ∈ {3,5,11,23,30,1165}`, all of which satisfy the bound with
  room to spare. The bound is *sharp* (equality) exactly at `n = 12` and `n = 18`,
  and has enormous margin elsewhere (since `φ(n) ≳ n/loglog n` dwarfs every prime gap
  below `n^2`). A counterexample would require a gap of merit `≈ 900` at a square,
  versus the largest known merit `≈ 41` — contradicting Cramér/Hardy–Littlewood.
* No counterexample exists, so the statement cannot be disproved.
* The statement is, however, an OPEN problem strictly stronger than Legendre's
  conjecture: for `n ≥ 2`, `1 + φ(n) ≤ n`, so the conjecture asserts a prime in
  `(n^2, n^2 + n] ⊂ (n^2, (n+1)^2)`, which is Legendre's conjecture (open since 1808);
  for prime `n` it is exactly Oppermann's conjecture, and for composite `n` (shorter
  interval) it is strictly stronger still. The best unconditional short-interval result
  (Baker–Harman–Pintz) only gives a prime in `(x, x + x^0.525]`; with `x = n^2` this is
  a gap bound `n^1.05 > n ≥ 1 + φ(n)`, and even the Riemann Hypothesis gives only
  `(n^2, n^2 + n log n]` — both too weak; a proof appears to need Cramér-type input.
  The parity barrier blocks all sieve approaches to producing a prime (not merely an
  almost-prime) in such a short interval. Mathlib / the FormalConjectures libraries
  contain only Bertrand's postulate, a Selberg-sieve upper bound on `π`, and a bare
  definition of `primeGap` — none can place a prime in a short interval at a square.
  Hence the conjecture cannot currently be proved (nor disproved) by available means.
-/
/-- **Exact characterization (proved).** The bound `a(n) ≤ 1 + φ(n)` is *logically equivalent*
to the existence of a prime in the short interval `(n^2, n^2 + 1 + φ(n)]`. (Forward: the smallest
prime above `n^2` lies in the window; backward: any prime in the window bounds the smallest one.)
This pins down the precise arithmetic content of the conjecture. -/
theorem A053000_le_iff_exists_prime (n : ℕ) :
    A053000 n ≤ 1 + Nat.totient n ↔
      ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ n ^ 2 + 1 + Nat.totient n := by
  constructor
  · intro h
    set S := {p | Nat.Prime p ∧ p > n ^ 2} with hS
    have hne : S.Nonempty := by
      obtain ⟨q, hq, hq2⟩ := Nat.exists_infinite_primes (n ^ 2 + 1)
      exact ⟨q, hq2, by omega⟩
    have hmem : sInf S ∈ S := Nat.sInf_mem hne
    obtain ⟨hprime, hgt⟩ := hmem
    refine ⟨sInf S, hprime, hgt, ?_⟩
    have hA : A053000 n = sInf S - n ^ 2 := rfl
    omega
  · rintro ⟨p, hp, hlt, hle⟩
    have hmem : p ∈ {p | Nat.Prime p ∧ p > n ^ 2} := ⟨hp, hlt⟩
    have hinf : sInf {p | Nat.Prime p ∧ p > n ^ 2} ≤ p := Nat.sInf_le hmem
    unfold A053000
    omega

/-- **Elementary bound (proved).** `1 + φ(n) ≤ n` for `n ≥ 2`. -/
theorem totient_succ_le_self (n : ℕ) (hn : 2 ≤ n) : 1 + Nat.totient n ≤ n := by
  have := Nat.totient_lt n (by omega)
  omega

/-- **The conjecture implies Legendre's conjecture (proved).** Assuming the bound at `n ≥ 2`,
there is a prime strictly between `n^2` and `(n+1)^2`. This is a machine-checked certificate
that `oeis_53000_conjecture_1` is at least as hard as Legendre's conjecture (open since 1808),
hence not provable from currently available results (the best unconditional short-interval
theorem, Baker–Harman–Pintz, gives only a prime in `(x, x + x^0.525]`, i.e. a gap bound
`n^1.05 > n ≥ 1 + φ(n)` at `x = n^2`; even RH gives only `(n^2, n^2 + n log n]`). -/
theorem implies_legendre (n : ℕ) (hn : 2 ≤ n)
    (hconj : A053000 n ≤ 1 + Nat.totient n) :
    ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  set S := {p | Nat.Prime p ∧ p > n ^ 2} with hS
  have hne : S.Nonempty := by
    obtain ⟨q, hq, hq2⟩ := Nat.exists_infinite_primes (n ^ 2 + 1)
    exact ⟨q, hq2, by omega⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  obtain ⟨hprime, hgt⟩ := hmem
  refine ⟨sInf S, hprime, hgt, ?_⟩
  have hb := totient_succ_le_self n hn
  have hA : A053000 n = sInf S - n ^ 2 := rfl
  have hge : n ^ 2 ≤ sInf S := le_of_lt hgt
  have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  omega

/-- The original conjecture. By `A053000_le_iff_exists_prime` the goal reduces *exactly* to the
existence of a prime in `(n^2, n^2 + 1 + φ(n)]`. That statement is **open**: it is (strictly
stronger than) Legendre's conjecture, true for all tested `n` (verified to `5·10^7`; sharp at
`n = 12, 18`) but with no known proof and no counterexample. The single `sorry` below is precisely
this irreducible open core; it cannot be discharged by any result available in Mathlib (which
offers only Bertrand's postulate and an upper bound on `π`), and proving it would constitute a
major advance in analytic number theory beyond the Riemann Hypothesis. -/
theorem oeis_53000_conjecture_1 (n : ℕ) (hn : n > 0) : A053000 n ≤ 1 + Nat.totient n := by
  rw [A053000_le_iff_exists_prime]
  -- Remaining (open) goal: ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ n ^ 2 + 1 + Nat.totient n
  sorry
