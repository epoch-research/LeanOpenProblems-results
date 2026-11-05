import Submission.Carmichael

/-!
# Analytic preparation for Erdős Problem 1057

This file defines the Carmichael counting function independently of the admitted
statements in `Submission.Spec`. It proves elementary bounds, eventual positivity,
and exact real- and natural-variable reformulations of the logarithmic limit.

The power lower bounds in these reformulations are hypotheses, not unconditional
arithmetic estimates. In particular, this file does not assert the Erdős target
or its negation.
-/

open Set Real Filter
open scoped Topology

namespace Erdos1057.Preparation

/-- The number of Carmichael numbers not exceeding the real number `x`. -/
noncomputable def count (x : ℝ) : ℝ :=
  ({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℝ)

/-- The set being counted is finite, even when `x` is negative. -/
theorem count_set_finite (x : ℝ) :
    {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.Finite := by
  apply (Set.finite_Iic (b := ⌊x⌋₊)).subset
  intro n hn
  exact Nat.le_floor hn.2

theorem count_nonneg (x : ℝ) : 0 ≤ count x := by
  dsimp [count]
  positivity

/-- Compositeness excludes `0` and permits comparison with the interval `[1, ⌊x⌋₊]`. -/
theorem count_le (x : ℝ) (hx : 0 ≤ x) : count x ≤ x := by
  have hs : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} ⊆
      (Finset.Icc 1 ⌊x⌋₊ : Set ℕ) := by
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_Icc]
    have hcomp : Nat.Composite n :=
      ((CarmichaelKorselt.isCarmichael_iff_korselt n).mp hn.1).1
    exact ⟨hcomp.1.le, Nat.le_floor hn.2⟩
  have hc := Set.ncard_le_ncard hs (Finset.finite_toSet _)
  have hc' : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard ≤ ⌊x⌋₊ := by
    simpa only [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] using hc
  exact (Nat.cast_le.mpr hc').trans (Nat.floor_le hx)

theorem count_monotone : Monotone count := by
  intro x y hxy
  apply Nat.cast_le.mpr
  exact Set.ncard_le_ncard (fun n hn => ⟨hn.1, hn.2.trans hxy⟩)
    (count_set_finite y)

/-- The explicit Carmichael number `561` gives a uniform positive lower bound. -/
theorem one_le_count_of_561_le {x : ℝ} (hx : 561 ≤ x) : 1 ≤ count x := by
  have hc : 0 < {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard :=
    (Set.ncard_pos (count_set_finite x)).mpr
      ⟨561, CarmichaelKorselt.isCarmichael_561, by simpa using hx⟩
  change (1 : ℝ) ≤ ({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℝ)
  exact_mod_cast (Nat.succ_le_iff.mpr hc)

theorem eventually_one_le_count : ∀ᶠ x : ℝ in atTop, 1 ≤ count x := by
  filter_upwards [eventually_ge_atTop (561 : ℝ)] with x hx
  exact one_le_count_of_561_le hx

/-- The logarithmic ratio is in `[0, 1]` once `x ≥ 561`. -/
theorem logratio_mem_Icc_of_561_le {x : ℝ} (hx : 561 ≤ x) :
    Real.log (count x) / Real.log x ∈ Set.Icc (0 : ℝ) 1 := by
  have hxone : 1 < x := by linarith
  have hc : 1 ≤ count x := one_le_count_of_561_le hx
  have hlog : 0 < Real.log x := Real.log_pos hxone
  constructor
  · exact div_nonneg (Real.log_nonneg hc) hlog.le
  · apply (div_le_iff₀ hlog).mpr
    simpa using Real.log_le_log (by linarith : 0 < count x)
      (count_le x (by linarith))

theorem eventually_logratio_mem_Icc :
    ∀ᶠ x : ℝ in atTop, Real.log (count x) / Real.log x ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [eventually_ge_atTop (561 : ℝ)] with x hx
  exact logratio_mem_Icc_of_561_le hx

/-- Eventual real power lower bounds suffice for the logarithmic limit. -/
theorem limit_of_lower_bound
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ count x) :
    Tendsto (fun x : ℝ => Real.log (count x) / Real.log x) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have heps : 0 < (1 - a) / 2 := by linarith
    filter_upwards [hlow ((1 - a) / 2) heps, eventually_gt_atTop (1 : ℝ)] with x hc hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hl := Real.le_log_of_rpow_le (zero_lt_one.trans hx) hc
    have hquot : 1 - (1 - a) / 2 ≤ Real.log (count x) / Real.log x :=
      (le_div_iff₀ hlog).mpr hl
    linarith
  · intro a ha
    filter_upwards [eventually_logratio_mem_Icc] with x hx
    exact hx.2.trans_lt ha

/-- The original real-variable limit is exactly the family of eventual real power bounds. -/
theorem limit_iff_lower_bound :
    Tendsto (fun x : ℝ => Real.log (count x) / Real.log x) atTop (𝓝 1) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ count x := by
  constructor
  · intro h ε hε
    have hlo := (tendsto_order.mp h).1 (1 - ε) (by linarith)
    filter_upwards [hlo, eventually_one_le_count, eventually_gt_atTop (1 : ℝ)]
      with x hxlo hc hx
    apply (Real.rpow_le_iff_le_log (zero_lt_one.trans hx)
      (by linarith : 0 < count x)).mpr
    exact ((lt_div_iff₀ (Real.log_pos hx)).mp hxlo).le
  · exact limit_of_lower_bound

/-- Exact negation: one fixed positive epsilon fails at arbitrarily large real arguments. -/
theorem not_limit_iff :
    ¬ Tendsto (fun x : ℝ => Real.log (count x) / Real.log x) atTop (𝓝 1) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ x : ℝ in atTop, count x < x ^ (1 - ε) := by
  rw [limit_iff_lower_bound]
  simp only [not_forall, Filter.not_eventually, not_le, exists_prop]

/-- Natural power bounds imply real power bounds without a multiplicative constant.
For `0 < ε < 1`, apply the natural bound with `ε / 2` to `⌊x⌋₊`. The estimates
`x ≤ 2 * ⌊x⌋₊` and eventually `2 ≤ x ^ (ε / 2)` absorb the rounding loss.
For `ε ≥ 1`, the unconditional bound `1 ≤ count x` suffices. -/
theorem real_lower_bound_of_nat_lower_bound
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (1 - ε) ≤ count (N : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ count x := by
  intro ε hε
  by_cases hεone : ε < 1
  · have hhalf : 0 < ε / 2 := by linarith
    have hexp : 0 ≤ 1 - ε / 2 := by linarith
    have hnat : ∀ᶠ x : ℝ in atTop,
        (⌊x⌋₊ : ℝ) ^ (1 - ε / 2) ≤ count (⌊x⌋₊ : ℝ) :=
      tendsto_nat_floor_atTop.eventually (hlow (ε / 2) hhalf)
    have hlarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (ε / 2) :=
      (tendsto_rpow_atTop hhalf).eventually (eventually_ge_atTop (2 : ℝ))
    filter_upwards [hnat, hlarge, eventually_ge_atTop (2 : ℝ)] with x hn hp hx
    have hxpos : 0 < x := by linarith
    have hfloorone : 1 ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ x))
    have hxfloor : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one x
      linarith
    have htwo : (2 : ℝ) ^ (1 - ε / 2) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : 1 - ε / 2 ≤ 1)
    have hupper : x ^ (1 - ε / 2) ≤ 2 * (⌊x⌋₊ : ℝ) ^ (1 - ε / 2) := by
      calc
        x ^ (1 - ε / 2) ≤ (2 * (⌊x⌋₊ : ℝ)) ^ (1 - ε / 2) :=
          Real.rpow_le_rpow hxpos.le hxfloor hexp
        _ = (2 : ℝ) ^ (1 - ε / 2) * (⌊x⌋₊ : ℝ) ^ (1 - ε / 2) :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
        _ ≤ 2 * (⌊x⌋₊ : ℝ) ^ (1 - ε / 2) :=
          mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hlower : 2 * x ^ (1 - ε) ≤ x ^ (1 - ε / 2) := by
      calc
        2 * x ^ (1 - ε) ≤ x ^ (ε / 2) * x ^ (1 - ε) :=
          mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hxpos.le _)
        _ = x ^ (1 - ε / 2) := by
          rw [← Real.rpow_add hxpos]
          congr 1
          ring
    have hpow : x ^ (1 - ε) ≤ (⌊x⌋₊ : ℝ) ^ (1 - ε / 2) := by
      linarith
    exact hpow.trans (hn.trans (count_monotone (Nat.floor_le hxpos.le)))
  · filter_upwards [eventually_one_le_count, eventually_ge_atTop (1 : ℝ)] with x hc hx
    exact (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)).trans hc

/-- Eventual exact power lower bounds on reals and naturals are equivalent. -/
theorem lower_bound_real_iff_nat :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ count x) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - ε) ≤ count (N : ℝ) := by
  constructor
  · intro h ε hε
    exact tendsto_natCast_atTop_atTop.eventually (h ε hε)
  · exact real_lower_bound_of_nat_lower_bound

/-- The original real-variable limit reduces exactly to natural power lower bounds. -/
theorem limit_iff_nat_lower_bound :
    Tendsto (fun x : ℝ => Real.log (count x) / Real.log x) atTop (𝓝 1) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - ε) ≤ count (N : ℝ) :=
  limit_iff_lower_bound.trans lower_bound_real_iff_nat

/-- Exact natural-variable obstruction to the real-variable limit. -/
theorem not_limit_iff_nat :
    ¬ Tendsto (fun x : ℝ => Real.log (count x) / Real.log x) atTop (𝓝 1) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ N : ℕ in atTop, count (N : ℝ) < (N : ℝ) ^ (1 - ε) := by
  rw [limit_iff_nat_lower_bound]
  simp only [not_forall, Filter.not_eventually, not_le, exists_prop]

end Erdos1057.Preparation
