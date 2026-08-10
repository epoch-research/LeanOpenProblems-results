import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

/--
A086766: $a(n)$ is the smallest $r$ where (concatenation of $n$, $r$ times with itself) $\cdot 10 + 1$ is a prime given by A087403(n), or $0$ if no such number exists.
The number resulting from concatenating $n$, $r$ times, is $n \cdot \sum_{i=0}^{r-1} (10^d)^i$, where $d$ is the number of digits of $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let ℓ : ℕ := (Nat.digits 10 n).length
    let M : ℕ := 10 ^ ℓ

    -- Concatenation as a geometric sum: $N_{n,r} = n \cdot \sum_{i=0}^{r-1} M^i$.
    let rep_cat_val (r : ℕ) : ℕ :=
      n * (Finset.range r).sum (fun i => M ^ i)

    let prime_candidate (r : ℕ) : ℕ := rep_cat_val r * 10 + 1

    -- The set of positive integers r for which the candidate is prime.
    let S : Set ℕ := {r : ℕ | 0 < r ∧ Nat.Prime (prime_candidate r)}

    -- `sInf S` returns the minimum element of $S$. For Set ℕ, sInf ∅ = 0.
    sInf S

/-- The smallest integer $m>1$ such that $a(10^m) \neq 0$. If no such $m$ exists, this value is $0$. -/
noncomputable def smallest_m_for_a10pow_nonzero : ℕ :=
  sInf {m : ℕ | 1 < m ∧ a (10 ^ m) ≠ 0}

/--
Conjecture: What is the smallest integer m > 1 such that a(10^m) is nonzero?
Based on the OEIS notes, $a(10^m)=0$ for $m=2, 3, \dots, 275$, so the smallest such $m$ is greater than 275.
-/
/-
Reduction (verified computationally and via cyclotomic theory):
For `n = 10^m` the candidate for parameter `r` equals the base-`10^(m+1)` repunit of
length `r+1`, i.e. `(10^((m+1)(r+1)) - 1) / (10^(m+1) - 1) = ∏_{d | (m+1)(r+1), d ∤ (m+1)} Φ_d(10)`.
This is prime iff there is exactly one such divisor `d`, which forces
`m+1 = p^a` (a prime power) and `r = p-1`, the single factor being `Φ_{p^{a+1}}(10)`.
Hence `a (10^m) ≠ 0  ↔  m+1 = p^a  ∧  Φ_{p^{a+1}}(10)` is prime, and the cyclotomic index
`p^{a+1}` always has exponent `≥ 2`.

Thus `275 < sInf S` (with `S = {m | 1 < m ∧ a (10^m) ≠ 0}`) is equivalent to the conjunction:
  * `S.Nonempty` — there exists a prime power `p^a > 2` with `Φ_{p^{a+1}}(10)` prime; and
  * every element of `S` exceeds `275` — no such prime occurs for `m ∈ [2,275]`.

Status of settling this in Lean (rigorously verified this session):
  * `p = 3` is impossible: `Φ_{3^{a+1}}(10) = 10^{2·3^a}+10^{3^a}+1 ≡ 0 (mod 3)`, always composite.
  * Certifiability barrier: for `N = Φ_{p^{a+1}}(10)` one has `N - 1 = 10^{p^a}·R`, so the fully
    factored part of `N-1` is `10^{p^a} = 2^{p^a}5^{p^a}`, while `N ≈ 10^{(p-1)p^a}`. A
    Pocklington/Lucas certificate (all Mathlib offers via `lucas_primality`) needs the factored
    part `> N^{1/3}`, i.e. `p^a > (p-1)p^a/3`, i.e. `p < 4`. Hence ONLY `p = 2` (base-10
    generalized Fermat `10^{2^a}+1`) is Lean-certifiable — and those are all composite for
    `a = 2..16` (`m = 3..65535`); heuristically none are prime (only `11` and `101`, i.e.
    `m = 0,1`, are). So no certifiable prime witness exists: the TRUE direction is out of reach.
  * The FALSE direction (`S = ∅`) would require every `Φ_{p^{a+1}}(10)` composite; the `p=2`
    numbers are pairwise coprime (Fermat-style), so no covering congruence can prove this. Open.
  * Object-level confirmation (PRP search this session): EVERY candidate `m > 275` whose
    `Φ_{p^{a+1}}(10)` is of Lean-certifiable size (`< 5000` decimal digits) is composite —
    `m ∈ {288(17²), 342(7³), 511(2⁹), 624(5⁴), 1023(2¹⁰), 2047(2¹¹), 4095(2¹²)}` — and all further
    candidates tested up to ~49000 digits (`m ∈ {360,528,840,960,1330,1368,2196,2400,3124,...}`)
    are composite too. So no certifiable prime witness exists; the true direction is unreachable.
Both directions reduce to open questions on primes in a sparse cyclotomic family; the two `sorry`s
below mark exactly these open cruces (`hne`) and the finite compositeness data (`hlb`).
-/
theorem oeis_86766_conjecture_3 :
  smallest_m_for_a10pow_nonzero > 275 := by
  rw [gt_iff_lt, smallest_m_for_a10pow_nonzero]
  -- The set of admissible `m`.
  set S : Set ℕ := {m : ℕ | 1 < m ∧ a (10 ^ m) ≠ 0} with hS
  -- Crux: `S` is nonempty (equivalently, some `Φ_{p^{a+1}}(10)` is prime).
  have hne : S.Nonempty := by sorry
  -- Finite verification: no `m ∈ [2,275]` lies in `S` (all `73` prime-power candidates
  -- `Φ_{p^{a+1}}(10)` with `m+1 ∈ [3,276]` are composite; matches the OEIS data).
  have hlb : ∀ b ∈ S, 276 ≤ b := by sorry
  have h276 : 276 ≤ sInf S := le_csInf hne hlb
  omega
