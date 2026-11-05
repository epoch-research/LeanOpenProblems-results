import FormalConjecturesUtil

/-! Elementary counting facts and the precise analytic form of Erdős 1057. -/

open Nat Real Filter Set
open scoped Topology Asymptotics

namespace Erdos1057

private def nums (x : ℝ) : Set ℕ := {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}
noncomputable def countAux (x : ℝ) : ℝ := ((nums x).ncard : ℝ)

private theorem carmichael_is_composite {n : ℕ} (h : IsCarmichael n) : n.Composite := by
  have hpsp : n.FermatPsp 1 := h 1 (by omega) (by simp)
  exact ⟨hpsp.2.2, hpsp.2.1⟩

private theorem nums_finite (x : ℝ) : (nums x).Finite := by
  obtain ⟨k, hk⟩ := exists_nat_ge x
  apply (finite_le_nat k).subset
  intro n hn
  exact_mod_cast (hn.2.trans hk)

private theorem nums_subset_Ioc (x : ℝ) : nums x ⊆ Set.Ioc 0 ⌊x⌋₊ := by
  rintro n ⟨hn, hx⟩
  exact ⟨by have := (carmichael_is_composite hn).1; omega, Nat.le_floor hx⟩

private theorem ncard_Ioc_zero (k : ℕ) : (Set.Ioc 0 k).ncard = k := by
  have h : ((Finset.Ioc 0 k : Finset ℕ) : Set ℕ).ncard = k := by
    rw [Set.ncard_coe_finset, Nat.card_Ioc, Nat.sub_zero]
  simpa using h

private theorem countAux_le_self {x : ℝ} (hx : 0 ≤ x) : countAux x ≤ x := by
  have h : (nums x).ncard ≤ ⌊x⌋₊ := by
    calc
      (nums x).ncard ≤ (Set.Ioc 0 ⌊x⌋₊).ncard :=
        Set.ncard_le_ncard (nums_subset_Ioc x) (Set.finite_Ioc 0 ⌊x⌋₊)
      _ = ⌊x⌋₊ := ncard_Ioc_zero _
  have hcast : countAux x ≤ (⌊x⌋₊ : ℝ) := by
    change ((nums x).ncard : ℝ) ≤ _
    exact_mod_cast h
  exact hcast.trans (Nat.floor_le hx)

private theorem countAux_mono : Monotone countAux := by
  intro x y hxy
  apply Nat.cast_le.mpr
  apply Set.ncard_le_ncard (ht := nums_finite y)
  rintro n ⟨hn, hx⟩
  exact ⟨hn, hx.trans hxy⟩

private theorem limit_implies_lower
    (hl : Tendsto (fun x : ℝ ↦ Real.log (countAux x) / Real.log x) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ countAux x := by
  let δ := min ε (1 / 2 : ℝ)
  have hdpos : 0 < δ := lt_min hε (by norm_num)
  have hdlt : δ < 1 := (min_le_right ε (1 / 2 : ℝ)).trans_lt (by norm_num)
  have hdle : δ ≤ ε := min_le_left ε (1 / 2 : ℝ)
  have hstay : ∀ᶠ x : ℝ in atTop, 1 - δ < Real.log (countAux x) / Real.log x :=
    hl.eventually (lt_mem_nhds (by linarith : 1 - δ < (1 : ℝ)))
  filter_upwards [hstay, eventually_gt_atTop (1 : ℝ)] with x hbound hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hloglt : (1 - δ) * Real.log x < Real.log (countAux x) :=
    (lt_div_iff₀ hlogx).mp hbound
  have hnonneg : 0 ≤ countAux x := by unfold countAux; positivity
  have hlogpos : 0 < Real.log (countAux x) :=
    (mul_nonneg (by linarith : 0 ≤ 1 - δ) hlogx.le).trans_lt hloglt
  have hcountpos : 0 < countAux x :=
    (by norm_num : (0 : ℝ) < 1).trans ((Real.log_pos_iff hnonneg).mp hlogpos)
  have hpow : x ^ (1 - δ) ≤ countAux x := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos (by linarith : 0 < x) _) hcountpos).mp
    rw [Real.log_rpow (by linarith : 0 < x)]
    exact le_of_lt hloglt
  exact (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
    (by linarith : 1 - ε ≤ 1 - δ)).trans hpow

private theorem lower_implies_limit
    (hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ countAux x) :
    Tendsto (fun x : ℝ ↦ Real.log (countAux x) / Real.log x) atTop (𝓝 1) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    let δ := min ((1 - a) / 2) (1 / 2 : ℝ)
    have hdpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hda : a < 1 - δ := by
      have hh : δ ≤ (1 - a) / 2 := min_le_left _ _
      linarith
    filter_upwards [hlo δ hdpos, eventually_gt_atTop (1 : ℝ)] with x hlow hx
    have hx0 : 0 < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos hx
    have hpowpos : 0 < x ^ (1 - δ) := Real.rpow_pos_of_pos hx0 _
    have hcountpos : 0 < countAux x := hpowpos.trans_le hlow
    have hlog : (1 - δ) * Real.log x ≤ Real.log (countAux x) := by
      rw [← Real.log_rpow hx0]
      exact Real.log_le_log hpowpos hlow
    have hratio : 1 - δ ≤ Real.log (countAux x) / Real.log x :=
      (le_div_iff₀ hlogx).mpr hlog
    exact hda.trans_le hratio
  · intro a ha
    filter_upwards [hlo (1 / 2) (by norm_num), eventually_gt_atTop (1 : ℝ)] with x hlow hx
    have hx0 : 0 < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos hx
    have hcountpos : 0 < countAux x := (Real.rpow_pos_of_pos hx0 _).trans_le hlow
    have hratio : Real.log (countAux x) / Real.log x ≤ 1 := by
      apply (div_le_iff₀ hlogx).mpr
      simpa using Real.log_le_log hcountpos (countAux_le_self (by linarith : 0 ≤ x))
    exact hratio.trans_lt ha

theorem countAux_limit_iff_lower :
    Tendsto (fun x : ℝ ↦ Real.log (countAux x) / Real.log x) atTop (𝓝 1) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ countAux x :=
  ⟨limit_implies_lower, lower_implies_limit⟩

theorem countAux_not_limit_iff_frequently_deficient :
    ¬ Tendsto (fun x : ℝ ↦ Real.log (countAux x) / Real.log x) atTop (𝓝 1) ↔
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ x : ℝ in atTop, countAux x < x ^ (1 - ε) := by
  simp only [countAux_limit_iff_lower, not_forall, not_eventually, not_le, exists_prop]

end Erdos1057
