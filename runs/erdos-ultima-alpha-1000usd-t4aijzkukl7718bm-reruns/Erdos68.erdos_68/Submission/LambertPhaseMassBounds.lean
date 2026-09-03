import Submission.LambertCyclicMass

/-! Full-window mass estimates for the uncancelled Lambert rows.
No boundary-clearing assertion is made. -/

namespace LambertPhaseMassBounds

open Finset LambertDifferenceOperators LambertRawBounds LambertTailRows
  LambertSharperOperatorBounds FactorialGeometricProductBound
  LambertCyclicRowLowerBound LambertCyclicCombinationLowerBound
  LambertLongBoundedCombinations LambertCyclicMass LambertUniformRawNonvanishing

noncomputable section

variable (d : ℕ) [NeZero d]

lemma shift_mass_upper (k : ℕ) (f : ZMod d → ℝ) :
    mass (cyclicShift d k f) ≤ (1+(k.factorial : ℝ)/rate d^k)*mass f := by
  have hp := rate_pos d
  have he : (∑ h : ZMod d, |f (h+k)|) = mass f :=
    Equiv.sum_comp (Equiv.addRight (k : ZMod d)) (fun h => |f h|)
  have hh (h : ZMod d) : |cyclicShift d k f h| ≤
      ((k.factorial : ℝ)/rate d^k)*|f (h+k)|+|f h| := by
    unfold cyclicShift
    exact (abs_sub _ _).trans_eq (by rw [abs_mul, abs_of_nonneg (by positivity)])
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hh h)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, he] at hs
  change mass (cyclicShift d k f) ≤ (k.factorial : ℝ)/rate d^k*mass f+mass f at hs
  nlinarith

lemma cyclicApply_mass_upper (ks : List ℕ) (f : ZMod d → ℝ) :
    mass (cyclicApply d ks f) ≤
      (ks.map (fun k => 1+(k.factorial : ℝ)/rate d^k)).prod * mass f := by
  have hp := rate_pos d
  induction ks generalizing f with
  | nil => simp [cyclicApply]
  | cons k ks ih =>
    have hprod : 0 ≤ (ks.map (fun k => 1+(k.factorial : ℝ)/rate d^k)).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      positivity
    calc
      _ ≤ (ks.map (fun k => 1+(k.factorial : ℝ)/rate d^k)).prod *
          mass (cyclicShift d k f) := ih _
      _ ≤ (ks.map (fun k => 1+(k.factorial : ℝ)/rate d^k)).prod *
          ((1+(k.factorial : ℝ)/rate d^k)*mass f) :=
        mul_le_mul_of_nonneg_left (shift_mass_upper d k f) hprod
      _ = _ := by simp only [List.map_cons, List.prod_cons]; ring

lemma rowModel_mass (hd : 12 ≤ d) : mass (rowModel d) = 1/(rate d-1) := by
  have hp := rate_pos d
  have h2 := rate_ge_two d hd
  have hf : (2 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le (by omega : 2 ≤ d)
  have hn (h : ZMod d) : 0 ≤ rowModel d h := by
    unfold rowModel
    exact div_nonneg (pow_nonneg hp.le _) (by linarith)
  have he : mass (rowModel d) = ∑ h : ZMod d, rowModel d h := by
    unfold mass
    apply Finset.sum_congr rfl
    intro h _
    exact abs_of_nonneg (hn h)
  have hshift : (∑ h : ZMod d, rowModel d (h+1)) = ∑ h : ZMod d, rowModel d h :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod d)) (rowModel d)
  have hj := congrArg (fun f : ZMod d → ℝ => ∑ h, f h)
    (funext (fun h => rowModel_jump d (by omega) h))
  dsimp only at hj
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hshift, ← he] at hj
  have htest (h : ZMod d) : h+1=0 ↔ h=-1 := by constructor <;> intro hh <;> linear_combination hh
  simp only [htest] at hj
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hj
  apply (eq_div_iff (by linarith : rate d-1 ≠ 0)).mpr
  nlinarith

lemma phase_sum_eq_mass (H : ℕ) (f : ZMod d → ℝ) :
    (∑ h ∈ Finset.range d, |f ((H+h : ℕ) : ZMod d)|) = mass f := by
  classical
  apply Finset.sum_bij (fun h _ => ((H+h : ℕ) : ZMod d))
  · intro h hh; exact Finset.mem_univ _
  · intro h hh k hk he
    have hc : (h : ZMod d)=(k : ZMod d) := by
      simpa only [Nat.cast_add, add_left_cancel_iff] using he
    have hv := congrArg ZMod.val hc
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hh),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)] using hv
  · intro k _
    refine ⟨(k-(H : ZMod d)).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    ring
  · intros; rfl

lemma phase_sum_le_mass (H D : ℕ) (hD : D ≤ d) (f : ZMod d → ℝ) :
    (∑ h ∈ Finset.range D, |f ((H+h : ℕ) : ZMod d)|) ≤ mass f := by
  rw [← phase_sum_eq_mass d H f]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hD)
    (by intros; positivity)

omit [NeZero d] in
/-- A short window occupies distinct phases of a later geometric row. -/
theorem row_window_mass_bound (e K H : ℕ) (hd : 12 ≤ d) (hde : d ≤ e)
    (hKe : K+1 ≤ e) :
    (∑ h ∈ Finset.range d, rate d^(H+h) *
      |rawApply (List.range' 2 K) (geometricRowTail e) (H+h)|) ≤
      (Real.exp 12/(rate e-1))*(rate d/rate e)^H := by
  have he : 12 ≤ e := hd.trans hde
  letI : NeZero e := ⟨by omega⟩
  have hp := rate_pos d
  have hq := rate_pos e
  have h2 := rate_ge_two e he
  have hr : 0 ≤ rate d/rate e := by positivity
  have hru : rate d/rate e ≤ 1 := (div_le_one hq).mpr (rate_mono d e (by omega) hde)
  let f := cyclicApply e (List.range' 2 K) (rowModel e)
  have hmodel (n : ℕ) : rate d^n *
      |rawApply (List.range' 2 K) (geometricRowTail e) n| =
      (rate d/rate e)^n * |f (n : ZMod e)| := by
    have hm := rawApply_model e (List.range' 2 K) (geometricRowTail e) (rowModel e)
      (geometricRowTail_model e (by omega)) n
    have ha := congrArg abs hm
    rw [abs_mul, abs_of_pos (pow_pos hq _)] at ha
    rw [← ha, div_pow]
    field_simp
  have hprod := weightedProduct_range_le_exp_twelve K e (by omega) hKe
  have hmass : mass f ≤ Real.exp 12/(rate e-1) := by
    have hm := cyclicApply_mass_upper e (List.range' 2 K) (rowModel e)
    rw [rowModel_mass e he] at hm
    calc
      _ ≤ _ := hm
      _ ≤ Real.exp 12*(1/(rate e-1)) :=
        mul_le_mul_of_nonneg_right hprod (div_nonneg (by norm_num) (by linarith))
      _ = _ := by ring
  calc
    _ = ∑ h ∈ Finset.range d, (rate d/rate e)^(H+h)*|f ((H+h : ℕ) : ZMod e)| := by
      apply Finset.sum_congr rfl
      intro h _
      exact hmodel _
    _ ≤ ∑ h ∈ Finset.range d, (rate d/rate e)^H*|f ((H+h : ℕ) : ZMod e)| := by
      apply Finset.sum_le_sum
      intro h _
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr hru (by omega)) (abs_nonneg _)
    _ = (rate d/rate e)^H*(∑ h ∈ Finset.range d, |f ((H+h : ℕ) : ZMod e)|) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (rate d/rate e)^H*mass f :=
      mul_le_mul_of_nonneg_left (phase_sum_le_mass e H d hde f) (pow_nonneg hr H)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hmass (pow_nonneg hr H)]

end
end LambertPhaseMassBounds

#print axioms LambertPhaseMassBounds.rowModel_mass
#print axioms LambertPhaseMassBounds.row_window_mass_bound
