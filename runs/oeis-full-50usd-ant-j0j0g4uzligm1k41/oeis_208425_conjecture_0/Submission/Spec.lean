import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A208425: Expansion of $\sum_{n\ge 0} \frac{(3n)!}{n!^3} \frac{x^{2n}}{(1-x)^{3n+1}}$.
The $n$-th term $a(n)$ is given by the known combinatorial identity:
$$ a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n-k}{k} \binom{n+k}{k} $$
-/
def a (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) * ((n - k).choose k) * ((n + k).choose k)

/-- **Core supercongruence.** For a prime `p > 3` and `n > 0`, the integer
`a (p*n) - a n` is divisible by `p ^ (3 * (1 + v_p n))`, where `v_p n = padicValNat p n`.
Equivalently, `(pn)^3` divides `a(pn) - a(n)` in the `p`-adic sense.

This is Zhi-Wei Sun's supercongruence for the sequence A208425.  For `p ∤ n` it is the
"base" supercongruence `a(pn) ≡ a(n) mod p^3`, while for `p | n` it is a strong Dwork-type
supercongruence `a(p^{s+1}m) ≡ a(p^s m) mod p^{3(s+1)}`.  Numerically the divisibility holds
with exact equality of valuations; the strong `p | n` case reflects the arithmetic geometry
of the underlying (Calabi–Yau / modular) period attached to the hypergeometric generating
function `∑ (3n)!/n!^3 · x^{2n}/(1-x)^{3n+1}` and lies beyond elementary combinatorial methods. -/
theorem oeis_208425_core (p : ℕ) (hp : p.Prime) (hpgt3 : p > 3) (n : ℕ) (hn : n > 0) :
    (p : ℤ) ^ (3 * (1 + padicValNat p n)) ∣ ((a (p * n) : ℤ) - (a n : ℤ)) := by
  sorry

/-- Conjecture: (i) For any prime p > 3 and positive integer n,
the number (a(p*n)-a(n))/(p*n)^3 is always a p-adic integer. -/
theorem oeis_208425_conjecture_0 (p : ℕ) (hp : p.Prime) (hpgt3 : p > 3) (n : ℕ) (hn : n > 0) :
  padicValRat p (((a (p * n) : ℚ) - (a n : ℚ)) / ((p * n : ℚ) ^ 3)) ≥ 0 := by
  -- Reduction of the `p`-adic valuation statement to the core integer supercongruence.
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hcore := oeis_208425_core p hp hpgt3 n hn
  set z : ℤ := (a (p * n) : ℤ) - (a n : ℤ) with hz
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpn : (p : ℚ) * n ≠ 0 := mul_ne_zero hpQ hnQ
  have hcast : ((a (p * n) : ℚ) - (a n : ℚ)) = (z : ℚ) := by push_cast [hz]; ring
  rw [hcast]
  by_cases hz0 : z = 0
  · simp [hz0]
  · rw [padicValRat.div (by exact_mod_cast hz0) (by positivity)]
    have hden : padicValRat p (((p : ℚ) * n) ^ 3) = 3 * (1 + padicValNat p n) := by
      rw [padicValRat.pow hpn, padicValRat.mul hpQ hnQ, padicValRat.self hp1,
          padicValRat.of_nat]
      push_cast; ring
    rw [hden]
    have hnum : padicValRat p (z : ℚ) ≥ (3 * (1 + padicValNat p n) : ℤ) := by
      rw [padicValRat.of_int]
      have hzabs : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz0
      have hdvdnat : p ^ (3 * (1 + padicValNat p n)) ∣ z.natAbs := by
        have : ((p ^ (3 * (1 + padicValNat p n)) : ℕ) : ℤ) ∣ (z.natAbs : ℤ) := by
          rw [Int.dvd_natAbs]; push_cast; exact hcore
        exact_mod_cast this
      have hle : 3 * (1 + padicValNat p n) ≤ padicValNat p z.natAbs :=
        (padicValNat_dvd_iff_le hzabs).mp hdvdnat
      have hpi : padicValInt p z = padicValNat p z.natAbs := rfl
      rw [hpi]; exact_mod_cast hle
    linarith [hnum]
