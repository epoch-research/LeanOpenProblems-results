import Submission.LogarithmicSignedReduction

/-! Finite quantization of normalized largest-prime-factor logarithms. Bounded
multipliers act EXACTLY trivially once they lie below the first quantization
threshold. No distributional independence is used. -/
namespace Erdos371
open Finset Filter

noncomputable def unitQuantize (Q : ℕ) (x : ℝ) : Fin (Q+1) :=
  ⟨min Q ⌊(Q : ℝ)*x⌋₊, Nat.lt_succ_of_le (min_le_left _ _)⟩

lemma unitQuantize_mono (Q : ℕ) : Monotone (unitQuantize Q) := by
  intro x y hxy
  exact min_le_min_left Q (Nat.floor_mono (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg Q)))

lemma unitQuantize_max (Q : ℕ) (x y : ℝ) :
    unitQuantize Q (max x y) = max (unitQuantize Q x) (unitQuantize Q y) :=
  (unitQuantize_mono Q).map_max

lemma unitQuantize_eq_zero (Q : ℕ) (x : ℝ) (hx : (Q : ℝ)*x < 1) : unitQuantize Q x = 0 := by
  apply Fin.ext
  simp only [unitQuantize, (Nat.floor_eq_zero).mpr hx, _root_.min_zero, Fin.val_zero]

lemma unitQuantize_value_le (Q : ℕ) (hQ : 0 < Q) (x : ℝ) (hx : 0 ≤ x) :
    ((unitQuantize Q x).val : ℝ)/Q ≤ x := by
  apply (div_le_iff₀ (by exact_mod_cast hQ)).mpr
  have hmin : ((unitQuantize Q x).val : ℝ) ≤ ⌊(Q : ℝ)*x⌋₊ := by
    exact_mod_cast (min_le_right Q ⌊(Q : ℝ)*x⌋₊)
  have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg Q) hx)
  nlinarith

/-- One-sided quantization error on the unit interval. -/
lemma unitQuantize_error (Q : ℕ) (hQ : 0 < Q) (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x-((unitQuantize Q x).val : ℝ)/Q ∧
      x-((unitQuantize Q x).val : ℝ)/Q < 1/(Q : ℝ) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hfloor : ⌊(Q : ℝ)*x⌋₊ ≤ Q := by
    have hf := Nat.floor_mono (mul_le_mul_of_nonneg_left hx1 hQr.le)
    simpa only [mul_one, Nat.floor_natCast] using hf
  constructor
  · exact sub_nonneg.mpr (unitQuantize_value_le Q hQ x hx)
  · change x-(min Q ⌊(Q : ℝ)*x⌋₊ : ℕ)/Q < 1/(Q : ℝ)
    rw [min_eq_right hfloor]
    have hf := Nat.lt_floor_add_one ((Q : ℝ)*x)
    apply (mul_lt_mul_iff_left₀ hQr).mp
    field_simp
    rw [mul_comm (Q : ℝ) x] at hf
    nlinarith

lemma unitQuantize_lt_of_gap (Q : ℕ) (hQ : 0 < Q) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hgap : 1/(Q : ℝ) < y-x) :
    unitQuantize Q x < unitQuantize Q y := by
  have hxv := unitQuantize_value_le Q hQ x hx
  have hyv := (unitQuantize_error Q hQ y hy hy1).2
  have hdiv : ((unitQuantize Q x).val : ℝ)/Q < ((unitQuantize Q y).val : ℝ)/Q := by linarith
  have hv := (div_lt_div_iff_of_pos_right (by exact_mod_cast hQ : (0 : ℝ) < Q)).mp hdiv
  exact_mod_cast hv

noncomputable def primeQuantLabel (Q N n : ℕ) : Fin (Q+1) :=
  unitQuantize Q (normalizedPrimeLog N n)

lemma normalizedPrimeLog_mul_max (N k n : ℕ) (hN : 1 < N) (hk : 0 < k) (hn : 0 < n) :
    normalizedPrimeLog N (k*n) = max (normalizedPrimeLog N k) (normalizedPrimeLog N n) := by
  unfold normalizedPrimeLog
  rw [primeLog_mul k n hk hn, max_div_div_right (Real.log_pos (by exact_mod_cast hN)).le]

/-- All inputs, not merely most inputs, are invariant under a multiplier below
the first quantization threshold. -/
theorem primeQuantLabel_mul (Q N k n : ℕ) (hN : 1 < N) (hk : 0 < k) (hsmall : k^Q < N) :
    primeQuantLabel Q N (k*n) = primeQuantLabel Q N n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hlog : (Q : ℝ)*primeLog k < Real.log N := by
      have hleft := mul_le_mul_of_nonneg_left (primeLog_le_log k) (Nat.cast_nonneg (α := ℝ) Q)
      have hright := Real.log_lt_log (by positivity : (0 : ℝ) < (k : ℝ)^Q)
        (show (k : ℝ)^Q < N by exact_mod_cast hsmall)
      rw [Real.log_pow] at hright
      exact hleft.trans_lt hright
    have hkzero : unitQuantize Q (normalizedPrimeLog N k) = 0 := by
      apply unitQuantize_eq_zero
      unfold normalizedPrimeLog
      rw [← mul_div_assoc, div_lt_one (Real.log_pos (by exact_mod_cast hN))]
      exact hlog
    unfold primeQuantLabel
    rw [normalizedPrimeLog_mul_max N k n hN hk (by omega), unitQuantize_max, hkzero,
      max_eq_right (Fin.zero_le _)]

/-- The stability threshold is uniform over every multiplier up to a fixed B. -/
theorem primeQuantLabel_eventually_mul (Q B : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ k, 0 < k → k ≤ B → ∀ n,
      primeQuantLabel Q N (k*n) = primeQuantLabel Q N n := by
  filter_upwards [eventually_gt_atTop (max 1 (B^Q))] with N hN
  intro k hk hkB n
  exact primeQuantLabel_mul Q N k n (lt_of_le_of_lt (le_max_left _ _) hN) hk
    ((Nat.pow_le_pow_left hkB Q).trans_lt (lt_of_le_of_lt (le_max_right _ _) hN))

lemma primeQuantLabel_error (Q N n : ℕ) (hQ : 0 < Q) (hN : 1 < N) (hn : n ≤ N) :
    0 ≤ normalizedPrimeLog N n - ((primeQuantLabel Q N n).val : ℝ)/Q ∧
      normalizedPrimeLog N n - ((primeQuantLabel Q N n).val : ℝ)/Q < 1/(Q : ℝ) :=
  unitQuantize_error Q hQ _ (normalizedPrimeLog_mem_unit N n hN hn).1
    (normalizedPrimeLog_mem_unit N n hN hn).2

#print axioms primeQuantLabel_mul
#print axioms primeQuantLabel_eventually_mul
#print axioms primeQuantLabel_error
end Erdos371
