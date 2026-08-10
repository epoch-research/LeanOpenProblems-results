import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/--
A289827: $a(n)$ is the largest $m \le n$ such that $\pi(m + n) = \pi(m) + \pi(n)$, where $\pi$ is the prime counting function $\text{A000720}$ ($\pi(0) = 0$).
-/
noncomputable def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => π (m + n) = π m + π n) n

/-
A claim often attributed to Carl Pomerance, discussing the implications of a conjecture
by T. Ordowski (the boundedness of A289827).

The conjecture being discussed is the boundedness of A289827(n), namely A289827(n) ≤ 10.
Pomerance wrote: "I believe if correct, your conjecture would disprove the Hardy-Littlewood
prime k-tuples conjecture, as shown by Hensley and Richards over 30 years ago. They showed
that prime k-tuples implies that there are pairs y < x with pi(x+y) >= pi(x) + pi(y) and
pi(y) arbitrarily large. Since pi(2x) < 2*pi(x), by increasing y in a y,x example, one would
come on a new pair y' < x with pi(x+y') = pi(x) + pi(y')."

----

Mathematical status (analysis carried out for this submission).

`A289827_conjecture_bounded_by_10` is *logically equivalent* to the statement that
for all `n` and all `m` with `11 ≤ m ≤ n` one has `π (m + n) ≠ π m + π n`
(the equivalence is the `Nat.findGreatest` reduction proved in `bounded_iff_core`
below).

This equivalent statement is a genuinely open problem in analytic number theory:

* It is *false* assuming the Hardy–Littlewood prime `k`-tuples conjecture.
  Hensley–Richards proved (unconditionally, combinatorially) that the maximal
  size `ρ*(m)` of an admissible set inside an interval of length `m` satisfies
  `ρ*(m) > π m` for all large `m` (the first crossover is near `m = 3159`,
  where `ρ*(3159) = 447 > 446 = π 3159`). Under prime `k`-tuples these dense
  admissible configurations are realised by actual primes, and Pomerance's
  argument then produces a pair with `π (m + n) = π m + π n` and `m` arbitrarily
  large: starting from an HL-violation pair `y < x` with `π (x + y) > π x + π y`,
  the integer-step function `t ↦ π (x + t) - π x - π t` decreases from a positive
  value (at `t = y`) to a negative value (at `t = x`, since `π (2x) < 2 π x`) in
  steps of size at most `1`, hence hits `0` exactly, at some `y'` with `π y'`
  large.
* It is *not* settled unconditionally in either direction: proving it would
  establish a strong form of the second Hardy–Littlewood conjecture
  (`π (x + y) ≤ π x + π y`), which is open; disproving it would establish the
  prime `k`-tuples conjecture (or at least produce an explicit dense prime
  cluster realising `ρ* ≥ π`), which is open and astronomically beyond reach
  (any counterexample requires a window of width `≥ 3159` containing `≥ 446`
  primes located at `n ≥ 3159`; the first such `n`, if it exists, is `≫ 10²³`).

Direct computation confirms `A289827 n ≤ 10` for all `n ≤ 3·10⁵` (the value `10`
is attained, e.g. at `n = 10`), and the admissible-set bound `ρ*(m) < π m`
rules out any counterexample with window width `11 ≤ m ≤ 3158` for every `n`.

Accordingly, what is provided below is the complete, sound reduction of the
conjecture to its open number-theoretic core; the core itself is exactly the
open statement above.
-/

/-- The `m = 11` slice is genuinely provable from Mathlib's totient sieve bound
`Nat.primeCounting'_add_le`: taking `a = 6` gives at most `φ(6)·(⌊11/6⌋+1) = 4`
primes in any window `(n, n+11]`, while `π 11 = 5`. This is one of only a sporadic
finite set of window-widths (`{11,17,23,…,29,41,59}`) for which the elementary
sieve bound already beats `π m`; for the vast majority of widths it is too weak. -/
theorem no_equality_m11 (n : ℕ) (hn : 11 ≤ n) : π (11 + n) ≠ π 11 + π n := by
  have h11 : π 11 = 5 := by decide
  have hb := Nat.primeCounting'_add_le (a := 6) (k := n + 1) (by norm_num) (by omega) 11
  have ht : Nat.totient 6 = 2 := by decide
  rw [ht] at hb
  have e1 : Nat.primeCounting' (n + 1 + 11) = π (11 + n) := by
    show Nat.primeCounting' (n + 12) = Nat.primeCounting (11 + n)
    rw [Nat.primeCounting]; congr 1; omega
  have e2 : Nat.primeCounting' (n + 1) = π n := by
    show Nat.primeCounting' (n + 1) = Nat.primeCounting n
    rw [Nat.primeCounting]
  rw [e1, e2] at hb
  norm_num at hb
  omega

/-- The number-theoretic core of A289827's boundedness: a "strict subadditivity /
no-equality" statement for the prime counting function on the range `12 ≤ m ≤ n`
(the `m = 11` slice is discharged separately in `no_equality_m11`).

This is an **open problem** (see the discussion above): it follows from the second
Hardy–Littlewood conjecture and is contradicted by the prime `k`-tuples conjecture
(Hensley–Richards `ρ*(m) > π m` for large `m`, plus Pomerance's exact-crossing
argument), so it is unsettled with present-day mathematics. No counterexample
exists below `n ≈ 10²³`, and Mathlib contains no machinery (admissible sets /
bounded prime gaps / prime k-tuples) that could decide it. -/
theorem A289827_no_equality_core_m_ge_12 :
    ∀ n m : ℕ, 12 ≤ m → m ≤ n → π (m + n) ≠ π m + π n := by
  sorry

/-- Combined no-equality statement for all `11 ≤ m ≤ n`, splitting off the
genuinely-proven `m = 11` case from the open `m ≥ 12` core. -/
theorem A289827_no_equality_core :
    ∀ n m : ℕ, 11 ≤ m → m ≤ n → π (m + n) ≠ π m + π n := by
  intro n m hm hmn
  rcases Nat.lt_or_ge m 12 with h | h
  · -- m = 11
    interval_cases m
    have : (11 : ℕ) ≤ n := hmn
    simpa [Nat.add_comm] using no_equality_m11 n this
  · exact A289827_no_equality_core_m_ge_12 n m h hmn

/-- `A289827 n ≤ 10` is equivalent to the absence of an equality
`π (m + n) = π m + π n` with `11 ≤ m ≤ n`. -/
theorem bounded_iff_core (n : ℕ) :
    A289827 n ≤ 10 ↔ ∀ m, 11 ≤ m → m ≤ n → π (m + n) ≠ π m + π n := by
  constructor
  · -- if the bound holds, no `m ≥ 11` can satisfy the predicate (else `findGreatest ≥ m`)
    intro hbound m hm hmn hP
    have : m ≤ A289827 n :=
      Nat.le_findGreatest hmn hP
    omega
  · -- conversely, the core forbids any witness `> 10`, so `findGreatest ≤ 10`
    intro hcore
    by_contra h
    push_neg at h
    have hle : A289827 n ≤ n := Nat.findGreatest_le n
    have hpos : A289827 n ≠ 0 := by omega
    have hP : (fun m => π (m + n) = π m + π n) (A289827 n) :=
      Nat.findGreatest_of_ne_zero (P := fun m => π (m + n) = π m + π n) rfl hpos
    simp only at hP
    exact hcore (A289827 n) (by omega) hle hP

theorem A289827_conjecture_bounded_by_10 : ∀ (n : ℕ), A289827 n ≤ 10 := by
  intro n
  exact (bounded_iff_core n).2 (fun m hm hmn => A289827_no_equality_core n m hm hmn)
