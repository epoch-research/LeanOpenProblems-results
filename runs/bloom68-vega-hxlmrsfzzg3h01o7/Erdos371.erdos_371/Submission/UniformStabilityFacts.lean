import FormalConjecturesUtil
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Kernel-checked elementary facts for uniform multiplicative stability.
This file does not import Submission.Spec or claim the density theorem.
-/

namespace Erdos371Uniform

noncomputable def exponent (n : ℕ) : ℝ :=
  Real.log (Nat.maxPrimeFac n : ℝ) / Real.log (n : ℝ)

/-- The algebraic normalization estimate, with its exact constant. -/
theorem normalized_increment_bound {L c a d : ℝ}
    (hL : 0 < L) (hc : 0 ≤ c) (ha0 : 0 ≤ a) (haL : a ≤ L)
    (hd0 : 0 ≤ d) (hdc : d ≤ c) :
    |(a + d) / (L + c) - a / L| ≤ c / (L + c) := by
  have hLc : 0 < L + c := by positivity
  have he : (a + d) / (L + c) - a / L = (d - c * (a / L)) / (L + c) := by
    field_simp
    ring
  have ha : 0 ≤ a / L := div_nonneg ha0 hL.le
  have hb : a / L ≤ 1 := (div_le_one hL).mpr haL
  rw [he, abs_div, abs_of_pos hLc]
  apply (div_le_div_iff_of_pos_right hLc).mpr
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hc ha, mul_le_mul_of_nonneg_left hb hc]
  · nlinarith [mul_nonneg hc ha]

private theorem maxPrimeFac_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < Nat.maxPrimeFac n := by
  rcases eq_or_lt_of_le hn with h | h
  · subst n
    simp
  · exact (Nat.prime_maxPrimeFac_of_one_lt n h).pos

/-- Uniform in BOTH integers, not only a fixed multiplier. -/
theorem exponent_mul_stability {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    |exponent (k * n) - exponent n| ≤
      Real.log (k : ℝ) / Real.log (k * n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hpn : 0 < (Nat.maxPrimeFac n : ℝ) := by
    exact_mod_cast maxPrimeFac_pos (by omega : 1 ≤ n)
  have hpk : 0 < (Nat.maxPrimeFac k : ℝ) := by
    exact_mod_cast maxPrimeFac_pos hk
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hc : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have ha0 : 0 ≤ Real.log (Nat.maxPrimeFac n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Nat.maxPrimeFac n by
      have := maxPrimeFac_pos (by omega : 1 ≤ n)
      omega))
  have haL : Real.log (Nat.maxPrimeFac n : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hpn (by exact_mod_cast Nat.maxPrimeFac_le (n := n))
  have hpkL : Real.log (Nat.maxPrimeFac k : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log hpk (by exact_mod_cast Nat.maxPrimeFac_le (n := k))
  have hlog : Real.log (Nat.maxPrimeFac (k * n) : ℝ) =
      max (Real.log (Nat.maxPrimeFac k : ℝ)) (Real.log (Nat.maxPrimeFac n : ℝ)) := by
    rw [Nat.maxPrimeFac_mul hk0 hn0, Nat.cast_max]
    rcases le_total (Nat.maxPrimeFac k : ℝ) (Nat.maxPrimeFac n : ℝ) with h | h
    · rw [max_eq_right h, max_eq_right (Real.log_le_log hpk h)]
    · rw [max_eq_left h, max_eq_left (Real.log_le_log hpn h)]
  have hd0 : 0 ≤ Real.log (Nat.maxPrimeFac (k * n) : ℝ) -
      Real.log (Nat.maxPrimeFac n : ℝ) := by
    rw [hlog]
    exact sub_nonneg.mpr (le_max_right _ _)
  have hdc : Real.log (Nat.maxPrimeFac (k * n) : ℝ) -
      Real.log (Nat.maxPrimeFac n : ℝ) ≤ Real.log (k : ℝ) := by
    rw [hlog]
    have hh : max (Real.log (Nat.maxPrimeFac k : ℝ))
        (Real.log (Nat.maxPrimeFac n : ℝ)) ≤
        Real.log (Nat.maxPrimeFac n : ℝ) + Real.log (k : ℝ) := by
      apply max_le
      · linarith
      · linarith
    linarith
  have h := normalized_increment_bound hL hc ha0 haL hd0 hdc
  simp only [add_sub_cancel] at h
  simpa [exponent, Nat.cast_mul, Real.log_mul hkR.ne' hnR.ne', add_comm] using h

/-- The subpower consequence retains the sharp delta/(1+delta). -/
theorem ratio_bound {L c δ : ℝ} (hL : 0 < L) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hcδ : c ≤ δ * L) : c / (L + c) ≤ δ / (1 + δ) := by
  have hLc : 0 < L + c := by positivity
  have h1δ : 0 < 1 + δ := by positivity
  rw [div_le_div_iff₀ hLc h1δ]
  nlinarith

/-- In particular, all multipliers with log k ≤ δ log n are controlled at once. -/
theorem exponent_subpower_stability {n k : ℕ} {δ : ℝ}
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hδ : 0 ≤ δ)
    (hkδ : Real.log (k : ℝ) ≤ δ * Real.log (n : ℝ)) :
    |exponent (k * n) - exponent n| ≤ δ / (1 + δ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hb := exponent_mul_stability hn hk
  rw [Real.log_mul hkR hnR, add_comm (Real.log (k : ℝ))] at hb
  exact hb.trans (ratio_bound
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
    (Real.log_nonneg (by exact_mod_cast hk)) hδ hkδ)

/-- Divisor form of uniform stability. -/
theorem stability_on_divisor {g : ℕ → ℝ}
    (h : ∀ n k : ℕ, 2 ≤ n → 1 ≤ k →
      |g (k * n) - g n| ≤ Real.log (k : ℝ) / Real.log (k * n : ℝ))
    {d n : ℕ} (hd : 2 ≤ d) (hdn : d ∣ n) (hn : 0 < n) :
    |g n - g d| ≤ (Real.log (n : ℝ) - Real.log (d : ℝ)) / Real.log (n : ℝ) := by
  obtain ⟨k, rfl⟩ := hdn
  have hk : 1 ≤ k := by
    by_contra he
    have : k = 0 := by omega
    simp [this] at hn
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hh := h d k hd hk
  have he : Real.log (d * k : ℝ) - Real.log (d : ℝ) = Real.log (k : ℝ) := by
    rw [Real.log_mul hdR hkR]
    ring
  push_cast
  rw [he]
  simpa [mul_comm] using hh

/-- Prime calibration makes every such model pointwise dominate the actual exponent. -/
theorem prime_calibrated_domination {g : ℕ → ℝ}
    (h : ∀ n k : ℕ, 2 ≤ n → 1 ≤ k →
      |g (k * n) - g n| ≤ Real.log (k : ℝ) / Real.log (k * n : ℝ))
    (hp : ∀ p : ℕ, p.Prime → g p = 1) {n : ℕ} (hn : 2 ≤ n) :
    exponent n ≤ g n := by
  have hpr := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hb := stability_on_divisor h hpr.two_le Nat.maxPrimeFac_dvd (by omega : 0 < n)
  rw [hp _ hpr, abs_le] at hb
  have hL : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  unfold exponent
  have he : (Real.log (n : ℝ) - Real.log (Nat.maxPrimeFac n : ℝ)) /
      Real.log (n : ℝ) = 1 - Real.log (Nat.maxPrimeFac n : ℝ) / Real.log (n : ℝ) := by
    rw [sub_div, div_self hL]
  rw [he] at hb
  linarith [hb.1]

/-- Matching both endpoints in reverse order using bounded positive multipliers
necessarily needs a multiplier at least of square-root size. -/
theorem small_multiplier_reflection_barrier {a b c d n m K : ℤ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hn : 1 ≤ n)
    (haK : a ≤ K) (hbK : b ≤ K) (hcK : c ≤ K) (hdK : d ≤ K)
    (h1 : a * n = b * (m + 1)) (h2 : c * (n + 1) = d * m) :
    n ≤ 2 * K ^ 2 := by
  have he : (a * d - b * c) * n = b * (c + d) := by
    nlinarith [congrArg (fun z : ℤ => d * z) h1,
      congrArg (fun z : ℤ => b * z) h2]
  have hbc : 0 < b * (c + d) := by positivity
  have hdet : 1 ≤ a * d - b * c := by
    have : 0 < a * d - b * c := by
      by_contra hh
      have : (a * d - b * c) * n ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) (by omega)
      linarith
    omega
  have hK : 0 ≤ K := by omega
  have hprod : b * (c + d) ≤ K * (2 * K) :=
    mul_le_mul hbK (by omega) (by omega) hK
  have hnn : n ≤ (a * d - b * c) * n := by nlinarith
  nlinarith


/-- Rigidity of the scalar metric forced by testing growing prime and power-of-two
multipliers. Its application to `T ∘ exponent` is proved analytically in the note. -/
theorem scalar_metric_rigidity {T : ℝ → ℝ}
    (hmetric : ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ 1 →
      |T y - T x| ≤ y ∧ |T y - T x| ≤ 1 - x / y)
    (hzero : ∃ x : ℝ, x ∈ Set.Icc 0 1 ∧ T x = 0)
    (hone : ∃ x : ℝ, x ∈ Set.Icc 0 1 ∧ T x = 1) :
    (∀ x : ℝ, x ∈ Set.Icc 0 1 → T x = x) ∨
    (∀ x : ℝ, x ∈ Set.Icc 0 1 → T x = 1 - x) := by
  obtain ⟨a, ha, hTa⟩ := hzero
  obtain ⟨b, hb, hTb⟩ := hone
  have hends : (T 0 = 0 ∧ T 1 = 1) ∨ (T 0 = 1 ∧ T 1 = 0) := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have hh := hmetric a b ha.1 hab hb.2
      rw [hTa, hTb] at hh
      norm_num at hh
      have hbone : b = 1 := le_antisymm hb.2 hh.1
      subst b
      simp only [div_one] at hh
      have hazero : a = 0 := by linarith [ha.1, hh.2]
      subst a
      exact Or.inl ⟨hTa, hTb⟩
    · have : (0 : ℝ) = 1 := hTa.symm.trans (hab ▸ hTb)
      norm_num at this
    · have hh := hmetric b a hb.1 hab ha.2
      rw [hTa, hTb] at hh
      norm_num at hh
      have haone : a = 1 := le_antisymm ha.2 hh.1
      subst a
      simp only [div_one] at hh
      have hbzero : b = 0 := by linarith [hb.1, hh.2]
      subst b
      exact Or.inr ⟨hTb, hTa⟩
  rcases hends with he | he
  · left
    intro x hx
    by_cases h0 : x = 0
    · simpa [h0] using he.1
    by_cases h1 : x = 1
    · simpa [h1] using he.2
    have hlow := (hmetric 0 x (by norm_num) (lt_of_le_of_ne hx.1 (Ne.symm h0)) hx.2).1
    have hupp := (hmetric x 1 hx.1 (lt_of_le_of_ne hx.2 h1) (by norm_num)).2
    rw [he.1, sub_zero, abs_le] at hlow
    rw [he.2, div_one, abs_le] at hupp
    linarith [hlow.2, hupp.2]
  · right
    intro x hx
    by_cases h0 : x = 0
    · simpa [h0] using he.1
    by_cases h1 : x = 1
    · simpa [h1] using he.2
    have hlow := (hmetric 0 x (by norm_num) (lt_of_le_of_ne hx.1 (Ne.symm h0)) hx.2).1
    have hupp := (hmetric x 1 hx.1 (lt_of_le_of_ne hx.2 h1) (by norm_num)).2
    rw [he.1, abs_le] at hlow
    rw [he.2, zero_sub, abs_neg, div_one, abs_le] at hupp
    linarith [hlow.1, hupp.2]

#print axioms normalized_increment_bound
#print axioms exponent_mul_stability
#print axioms ratio_bound
#print axioms exponent_subpower_stability
#print axioms stability_on_divisor
#print axioms prime_calibrated_domination
#print axioms small_multiplier_reflection_barrier
#print axioms scalar_metric_rigidity

end Erdos371Uniform
