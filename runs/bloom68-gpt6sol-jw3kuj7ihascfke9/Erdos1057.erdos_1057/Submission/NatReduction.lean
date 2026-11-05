import Submission.Reduction

/-!
# Natural-bound reduction for the Carmichael counting limit

The real counting function is constant between consecutive natural bounds.  A small
loss in the exponent absorbs the difference between `x` and `⌊x⌋₊`.
-/

open Filter
open scoped Topology

namespace Erdos1057

private theorem countAux_floor (x : ℝ) (hx : 0 ≤ x) :
    countAux x = (({n : ℕ | IsCarmichael n ∧ n ≤ ⌊x⌋₊}).ncard : ℝ) := by
  change (({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}).ncard : ℝ) = _
  have hset : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} =
      {n : ℕ | IsCarmichael n ∧ n ≤ ⌊x⌋₊} := by
    ext n
    change (IsCarmichael n ∧ (n : ℝ) ≤ x) ↔ (IsCarmichael n ∧ n ≤ ⌊x⌋₊)
    rw [Nat.le_floor_iff hx]
  rw [hset]

private theorem countAux_nat (N : ℕ) :
    countAux (N : ℝ) = (({n : ℕ | IsCarmichael n ∧ n ≤ N}).ncard : ℝ) := by
  simpa only [Nat.floor_natCast] using countAux_floor (N : ℝ) (Nat.cast_nonneg N)

private theorem eventually_rpow_le_floor_rpow (ε δ : ℝ)
    (hδpos : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hεδ : 2 * δ ≤ ε) :
    ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ (⌊x⌋₊ : ℝ) ^ (1 - δ) := by
  have hfloor : ∀ᶠ x : ℝ in atTop, 1 / 2 < (⌊x⌋₊ : ℝ) / x :=
    (tendsto_nat_floor_div_atTop (R := ℝ)).eventually
      (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hpow : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ δ :=
    (tendsto_rpow_atTop hδpos).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hfloor, hpow] with x hx hxfl hxd
  have hxpos : 0 < x := by linarith
  have hfloor' : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have hf : (1 / 2 : ℝ) * x < (⌊x⌋₊ : ℝ) :=
      (lt_div_iff₀ hxpos).mp hxfl
    linarith
  have hxdpos : 0 < x ^ (1 - δ) := Real.rpow_pos_of_pos hxpos _
  have hfactor : x ^ (1 - δ) * x ^ δ = x := by
    simpa only [sub_add_cancel, Real.rpow_one] using
      (Real.rpow_add hxpos (1 - δ) δ).symm
  have hpbase : x ^ (1 - δ) ≤ (⌊x⌋₊ : ℝ) := by
    have hmul : x ^ (1 - δ) * 2 ≤ x :=
      (mul_le_mul_of_nonneg_left hxd hxdpos.le).trans hfactor.le
    linarith
  calc
    x ^ (1 - ε) ≤ x ^ ((1 - δ) * (1 - δ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
      nlinarith [sq_nonneg δ]
    _ = (x ^ (1 - δ)) ^ (1 - δ) := Real.rpow_mul hxpos.le _ _
    _ ≤ (⌊x⌋₊ : ℝ) ^ (1 - δ) :=
      Real.rpow_le_rpow hxdpos.le hpbase (by linarith : 0 ≤ 1 - δ)

/-- The real logarithmic limit is equivalent to nearlinear lower bounds at
natural cutoffs. This is a reduction, not a proof of either side. -/
theorem countAux_limit_iff_nat_lower :
    Tendsto (fun x : ℝ => Real.log (countAux x) / Real.log x) atTop (𝓝 1) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (1 - ε) ≤ (({n : ℕ | IsCarmichael n ∧ n ≤ N}).ncard : ℝ) := by
  constructor
  · intro h ε hε
    have hnat : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 - ε) ≤ countAux (N : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        ((countAux_limit_iff_lower.mp h) ε hε)
    filter_upwards [hnat] with N hN
    simpa only [countAux_nat] using hN
  · intro h
    apply countAux_limit_iff_lower.mpr
    intro ε hε
    let δ : ℝ := min (ε / 2) (1 / 2)
    have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
    have hεδ : 2 * δ ≤ ε := by
      have hδle : δ ≤ ε / 2 := min_le_left _ _
      linarith
    have hlo : ∀ᶠ x : ℝ in atTop,
        (⌊x⌋₊ : ℝ) ^ (1 - δ) ≤
          (({n : ℕ | IsCarmichael n ∧ n ≤ ⌊x⌋₊}).ncard : ℝ) :=
      (tendsto_nat_floor_atTop (α := ℝ)).eventually (h δ hδpos)
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      eventually_rpow_le_floor_rpow ε δ hδpos hδhalf hεδ, hlo] with x hx hp hn
    simpa only [countAux_floor x hx] using hp.trans hn

end Erdos1057
