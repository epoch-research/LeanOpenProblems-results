import Submission.KnownBoundsLower

/-!
# Erdős Problem 30 — conditional reduction

This file does **not** settle `Erdos30.erdos_30`. It records precisely what is missing:

* `Erdos30.lower_of_prime_gaps`: if every interval `[x - x^δ, x]` (`δ > 0`, `x` large) contains a
  prime — a hypothesis far beyond current knowledge (even beyond RH) — then Singer's construction
  gives the lower half `√N - 2 N^ε ≤ h N` eventually, for every `ε > 0`.
* `Erdos30.erdos_30_of_prime_gaps_of_upper`: that hypothesis together with the (open, Erdős \$1000)
  upper bound `h N - √N ≤ C_ε N^ε` implies the statement of `Erdos30.erdos_30`.
-/

namespace Erdos30

open Filter

/-- Primes in all short intervals `[x - x^δ, x]` (an open hypothesis, stronger than what RH gives). -/
def PrimesInShortIntervals : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ (x : ℝ) - (x : ℝ) ^ δ ≤ p ∧ p ≤ x

/-- The upper half of Erdős Problem 30 (open; Erdős offered \$1000). -/
def UpperConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, (h N : ℝ) - Real.sqrt N ≤ C * (N : ℝ) ^ ε

/-- Conditional lower half: primes in short intervals + Singer ⇒ `√N - 2 N^ε ≤ h N` eventually. -/
theorem lower_of_prime_gaps (hPG : PrimesInShortIntervals) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.sqrt N - 2 * (N : ℝ) ^ ε ≤ h N := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hPG ε hε)
  rw [eventually_atTop]
  refine ⟨(X + 2) ^ 2, fun N hN => ?_⟩
  set s := Nat.sqrt N with hs
  have hsN : s ^ 2 ≤ N := Nat.sqrt_le' N
  have hNs : N < (s + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hXs : X + 2 ≤ s := Nat.le_sqrt'.mpr hN
  obtain ⟨p, hp, hp1, hp2⟩ := hX (s - 1) (by omega)
  haveI := Fact.mk hp
  have hpN : p ^ 2 + p + 1 ≤ N := by
    have : p + 1 ≤ s := by omega
    nlinarith
  have h1 : p + 1 ≤ h N := (singer_le_h p).trans (h_mono hpN)
  have h1R : (p : ℝ) + 1 ≤ h N := by exact_mod_cast h1
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (by nlinarith) hN
    exact_mod_cast this
  -- √N < s + 1
  have hsqrt : Real.sqrt N < s + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast hNs
  -- (s-1)^ε ≤ N^ε
  have hs1 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hsle : ((s - 1 : ℕ) : ℝ) ≤ N := by
    have : s - 1 ≤ N := le_trans (Nat.sub_le _ _) (le_trans (Nat.le_self_pow (by norm_num) s) hsN)
    exact_mod_cast this
  have hpow : ((s - 1 : ℕ) : ℝ) ^ ε ≤ (N : ℝ) ^ ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hsle hε.le
  have hNe : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  rw [hs1] at hp1
  rw [hs1] at hpow
  linarith

/-- **Reduction.** Primes in short intervals + the upper conjecture ⇒ the statement of Erdős 30. -/
theorem erdos_30_of_prime_gaps_of_upper (hPG : PrimesInShortIntervals) (hU : UpperConjecture) :
    ∀ᵉ (ε > 0), (fun N => h N - (N : Real).sqrt) =O[atTop] fun N => (N : ℝ)^(ε : ℝ) := by
  intro ε hε
  obtain ⟨C, hC⟩ := hU ε hε
  have hL := lower_of_prime_gaps hPG ε hε
  refine Asymptotics.IsBigO.of_bound (max C 2) ?_
  filter_upwards [hC, hL, eventually_ge_atTop 1] with N hCN hLN hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNe : (0 : ℝ) ≤ (N : ℝ) ^ ε := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hNe, abs_le]
  constructor
  · have : 2 * (N : ℝ) ^ ε ≤ max C 2 * (N : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hNe
    linarith
  · have : C * (N : ℝ) ^ ε ≤ max C 2 * (N : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hNe
    linarith

end Erdos30
