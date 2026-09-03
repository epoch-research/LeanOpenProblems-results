import Submission.CosetExplore

/-! Mixed representation counts for two unions of finite-field parabolas.
These estimates concern sets in one common finite group. -/
namespace Erdos66CrossGraph
open Erdos66FiniteField Erdos66OriginRepair Erdos66Coset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def crossCharFiber (U V : Finset F) (w : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ V, if u + v = w then quadraticChar F u * quadraticChar F v else 0

noncomputable def crossGraphCount (U V : Finset F) (t s : F) : ℤ :=
  ∑ u ∈ U, ∑ v ∈ V,
    (Fintype.card {x : F // x ^ 2 / u + (t - x) ^ 2 / v = s} : ℤ)

lemma crossGraphCount_identity (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u + v ≠ 0) (t s : F) :
    crossGraphCount U V t s = (U.card : ℤ) * V.card +
      ∑ w : F, crossCharFiber U V w * quadraticChar F (w * s - t ^ 2) := by
  have hcount : crossGraphCount U V t s = (U.card : ℤ) * V.card +
      ∑ u ∈ U, ∑ v ∈ V, quadraticChar F u * quadraticChar F v *
        quadraticChar F ((u + v) * s - t ^ 2) := by
    calc
      _ = ∑ u ∈ U, ∑ v ∈ V,
          (1 + quadraticChar F u * quadraticChar F v *
            quadraticChar F ((u + v) * s - t ^ 2)) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        exact parabola_sum_count hF u v t s (hU u hu) (hV v hv) (hUV u hu v hv)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcount]
  congr 1
  symm
  simp only [crossCharFiber, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma crossGraphCount_error (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u + v ≠ 0) (t s : F) :
    |crossGraphCount U V t s - (U.card : ℤ) * V.card| ≤
      ∑ w : F, |crossCharFiber U V w| := by
  rw [crossGraphCount_identity hF U V hU hV hUV, add_sub_cancel_left]
  calc
    _ ≤ ∑ w : F, |crossCharFiber U V w * quadraticChar F (w * s - t ^ 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro w hw
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (quadraticChar_abs_le_one (w * s - t ^ 2)) (abs_nonneg (crossCharFiber U V w))

lemma crossGraphCount_eq_conv (U V : Finset F) (t s : F) :
    crossGraphCount U V t s = finiteConv (graphWeight U) (graphWeight V) (t, s) := by
  classical
  unfold crossGraphCount finiteConv graphWeight
  symm
  simp only [Finset.sum_mul_sum, Prod.fst_sub, Prod.snd_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  exact graph_pair_count u v t s

lemma finiteConv_two_zeroMass (f g : F × F → ℤ) (a b : ℤ) (z : F × F) :
    finiteConv (fun x ↦ f x + a * (if x = 0 then 1 else 0))
        (fun x ↦ g x + b * (if x = 0 then 1 else 0)) z =
      finiteConv f g z + a * g z + b * f z + a * b * (if z = 0 then 1 else 0) := by
  classical
  let δ : F × F → ℤ := fun x ↦ if x = 0 then 1 else 0
  have he (x : F × F) : (f x + a * δ x) * (g (z - x) + b * δ (z - x)) =
      f x * g (z - x) + a * (δ x * g (z - x)) + b * (f x * δ (z - x)) +
        a * b * (δ x * δ (z - x)) := by ring
  change (∑ x, (f x + a * δ x) * (g (z - x) + b * δ (z - x))) = _
  simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
  change finiteConv f g z + a * finiteConv δ g z + b * finiteConv f δ z +
      a * b * finiteConv δ δ z = _
  rw [finiteConv_zero_left, finiteConv_zero_right, finiteConv_zero_left]

lemma crossGraphCount_correction (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (hUne : U.Nonempty) (hVne : V.Nonempty) (t s : F) :
    crossGraphCount U V t s = finiteConv (graphIndicator U) (graphIndicator V) (t, s) +
      ((U.card : ℤ) - 1) * graphIndicator V (t, s) +
      ((V.card : ℤ) - 1) * graphIndicator U (t, s) +
      ((U.card : ℤ) - 1) * ((V.card : ℤ) - 1) * (if (t, s) = 0 then 1 else 0) := by
  rw [crossGraphCount_eq_conv]
  have hUW : graphWeight U = fun x ↦ graphIndicator U x +
      ((U.card : ℤ) - 1) * (if x = 0 then 1 else 0) :=
    funext (graphWeight_eq_indicator U hU hUne)
  have hVW : graphWeight V = fun x ↦ graphIndicator V x +
      ((V.card : ℤ) - 1) * (if x = 0 then 1 else 0) :=
    funext (graphWeight_eq_indicator V hV hVne)
  rw [hUW, hVW]
  exact finiteConv_two_zeroMass _ _ _ _ _

lemma parabolaSet_crossCount_eq (U V : Finset F) (z : F × F) :
    (pairCount (parabolaSet U) (parabolaSet V) z : ℤ) =
      finiteConv (graphIndicator U) (graphIndicator V) z := by
  rw [pairCount_eq_indicatorConv]
  congr 1 <;> funext a <;> simp [graphIndicator, parabolaSet]

lemma cross_graph_error (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u + v ≠ 0)
    (hUne : U.Nonempty) (hVne : V.Nonempty) (z : F × F) (hz : z ≠ 0) :
    |(pairCount (parabolaSet U) (parabolaSet V) z : ℤ) - (U.card : ℤ) * V.card| ≤
      (∑ w : F, |crossCharFiber U V w|) + U.card + V.card := by
  obtain ⟨t, s⟩ := z
  rw [parabolaSet_crossCount_eq]
  have hu : 0 ≤ (U.card : ℤ) - 1 := by
    have hh : 1 ≤ U.card := Finset.card_pos.mpr hUne
    omega
  have hv : 0 ≤ (V.card : ℤ) - 1 := by
    have hh : 1 ≤ V.card := Finset.card_pos.mpr hVne
    omega
  obtain ⟨hiU0, hiU1⟩ := graphIndicator_bounds U (t, s)
  obtain ⟨hiV0, hiV1⟩ := graphIndicator_bounds V (t, s)
  have he := crossGraphCount_correction U V hU hV hUne hVne t s
  rw [if_neg hz, mul_zero, add_zero] at he
  have hb := crossGraphCount_error hF U V hU hV hUV t s
  rw [abs_le] at hb ⊢
  constructor <;> nlinarith [mul_nonneg hu hiV0, mul_nonneg hv hiU0,
    mul_nonneg hu (sub_nonneg.mpr hiV1), mul_nonneg hv (sub_nonneg.mpr hiU1)]

lemma cross_graph_origin (hF : ringChar F ≠ 2) (U V : Finset F)
    (hU : ∀ u ∈ U, u ≠ 0) (hV : ∀ v ∈ V, v ≠ 0)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u + v ≠ 0)
    (hUne : U.Nonempty) (hVne : V.Nonempty) :
    pairCount (parabolaSet U) (parabolaSet V) 0 = 1 := by
  have hu0 : graphIndicator U (0, 0) = 1 := by
    obtain ⟨u, hu⟩ := hUne
    simp [graphIndicator, show ∃ v, v ∈ U from ⟨u, hu⟩]
  have hv0 : graphIndicator V (0, 0) = 1 := by
    obtain ⟨v, hv⟩ := hVne
    simp [graphIndicator, show ∃ u, u ∈ V from ⟨v, hv⟩]
  have he := crossGraphCount_correction U V hU hV hUne hVne 0 0
  rw [crossGraphCount_identity hF U V hU hV hUV, hu0, hv0] at he
  norm_num at he
  have hh : (pairCount (parabolaSet U) (parabolaSet V) (0, 0) : ℤ) = 1 := by
    rw [parabolaSet_crossCount_eq]
    nlinarith
  exact_mod_cast hh

end Erdos66CrossGraph
