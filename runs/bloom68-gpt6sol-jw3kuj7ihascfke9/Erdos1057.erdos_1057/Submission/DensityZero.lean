import Submission.SmoothSplit
import Submission.Reduction

/-!
# Carmichael numbers have natural density zero

For a fixed smoothness threshold `Y`, the smooth/large-prime split gives
`C(X) ≤ 2 ^ (#Y.primesBelow) * X.sqrt + 2 * X / Y`.  After dividing by `X`,
the first term tends to zero as `X → ∞`; the second can be made arbitrarily
small by choosing `Y` large.
-/

open Filter
open scoped Topology

namespace Erdos1057

private theorem carmichaelsUpTo_card_le_real (X Y : ℕ) (hY : 3 ≤ Y) :
    (({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard : ℝ) ≤
      (2 ^ Y.primesBelow.card : ℝ) * Real.sqrt (X : ℝ) + 2 * (X : ℝ) / (Y : ℝ) := by
  have hdiv : ((2 * X / Y : ℕ) : ℝ) ≤ 2 * (X : ℝ) / (Y : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.cast_div_le (α := ℝ) (m := 2 * X) (n := Y))
  calc
    (({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard : ℝ) ≤
        ((2 ^ Y.primesBelow.card * X.sqrt + 2 * X / Y : ℕ) : ℝ) := by
      exact_mod_cast carmichaelsUpTo_card_le_smooth_split X Y hY
    _ = (2 ^ Y.primesBelow.card : ℝ) * (X.sqrt : ℝ) +
        ((2 * X / Y : ℕ) : ℝ) := by
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 ^ Y.primesBelow.card : ℝ) * Real.sqrt (X : ℝ) +
        2 * (X : ℝ) / (Y : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)) hdiv

private theorem carmichaelsUpTo_ratio_le (X Y : ℕ) (hY : 3 ≤ Y) (hX : 0 < X) :
    (({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard : ℝ) / (X : ℝ) ≤
      (2 ^ Y.primesBelow.card : ℝ) / Real.sqrt (X : ℝ) + 2 / (Y : ℝ) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
  have hYne : (Y : ℝ) ≠ 0 := by exact_mod_cast (by omega : Y ≠ 0)
  have hcancel : (2 * (X : ℝ) / (Y : ℝ)) / (X : ℝ) = 2 / (Y : ℝ) := by
    field_simp
  calc
    _ ≤ ((2 ^ Y.primesBelow.card : ℝ) * Real.sqrt (X : ℝ) +
        2 * (X : ℝ) / (Y : ℝ)) / (X : ℝ) :=
      div_le_div_of_nonneg_right (carmichaelsUpTo_card_le_real X Y hY) hXpos.le
    _ = (2 ^ Y.primesBelow.card : ℝ) / Real.sqrt (X : ℝ) + 2 / (Y : ℝ) := by
      rw [add_div, mul_div_assoc, Real.sqrt_div_self', hcancel]
      ring

/-- The number of Carmichael numbers up to `X`, divided by `X`, tends to zero
along the natural numbers. This proof does not use the unproved target in `Spec.lean`. -/
theorem carmichaels_density_zero :
    Tendsto (fun X : ℕ => (({n : ℕ | IsCarmichael n ∧ n ≤ X}).ncard : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall (fun X =>
      lt_of_lt_of_le ha (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  · intro a ha
    have hYev : ∀ᶠ Y : ℕ in atTop, 3 ≤ Y ∧ (2 : ℝ) / (Y : ℝ) < a / 2 :=
      (eventually_ge_atTop 3).and
        ((tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 2).eventually
          (gt_mem_nhds (by linarith : (0 : ℝ) < a / 2)))
    obtain ⟨Y, hY, hYsmall⟩ := hYev.exists
    have hsmooth : Tendsto (fun X : ℕ =>
        (2 ^ Y.primesBelow.card : ℝ) / Real.sqrt (X : ℝ)) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop
        (2 ^ Y.primesBelow.card : ℝ)
    have hsmall : ∀ᶠ X : ℕ in atTop,
        (2 ^ Y.primesBelow.card : ℝ) / Real.sqrt (X : ℝ) < a / 2 :=
      hsmooth.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 2))
    filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with X hterm hX
    exact lt_of_le_of_lt (carmichaelsUpTo_ratio_le X Y hY hX) (by linarith)

/-- The real counting function from `Submission.Reduction` is also `o(x)` as
`x → +∞` through the real numbers. -/
theorem countAux_div_self_tendsto_zero :
    Tendsto (fun x : ℝ => countAux x / x) atTop (𝓝 0) := by
  have hprod : Tendsto (fun x : ℝ =>
      ((({n : ℕ | IsCarmichael n ∧ n ≤ ⌊x⌋₊}).ncard : ℝ) / (⌊x⌋₊ : ℝ)) *
        ((⌊x⌋₊ : ℝ) / x)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (carmichaels_density_zero.comp (tendsto_nat_floor_atTop (α := ℝ))).mul
        (tendsto_nat_floor_div_atTop (R := ℝ))
  have heq : (fun x : ℝ =>
      (({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}).ncard : ℝ) / x) =ᶠ[atTop]
      (fun x : ℝ =>
        ((({n : ℕ | IsCarmichael n ∧ n ≤ ⌊x⌋₊}).ncard : ℝ) / (⌊x⌋₊ : ℝ)) *
          ((⌊x⌋₊ : ℝ) / x)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hfloor : (⌊x⌋₊ : ℝ) ≠ 0 := by
      have hf : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
      exact_mod_cast (by omega : ⌊x⌋₊ ≠ 0)
    have hset : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} =
        {n : ℕ | IsCarmichael n ∧ n ≤ ⌊x⌋₊} := by
      ext n
      change (IsCarmichael n ∧ (n : ℝ) ≤ x) ↔ (IsCarmichael n ∧ n ≤ ⌊x⌋₊)
      rw [Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x)]
    rw [hset]
    field_simp [hfloor]
  change Tendsto (fun x : ℝ =>
    (({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}).ncard : ℝ) / x) atTop (𝓝 0)
  exact hprod.congr' heq.symm

end Erdos1057
