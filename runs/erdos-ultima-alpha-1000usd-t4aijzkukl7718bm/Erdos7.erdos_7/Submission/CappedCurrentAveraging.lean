import FormalConjecturesUtil

/-! A positive correction for averaging current retention profiles across a
capped-mixture breakpoint. This is an auxiliary inequality, not a cover theorem. -/
namespace Erdos7CappedCurrentAveraging
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def cappedValue {J : Type*} [Fintype J]
    (h a : ℝ) (q d : J → ℝ) : ℝ := h*a+∑ j,min h (q j)*d j

lemma cap_zero_decomposition (h q : ℝ) (hq : 0 ≤ q) (hh : h=0 ∨ q ≤ h) :
    min h q+q*(if h=0 then 1 else 0)=q := by
  by_cases hzero : h=0
  · simp [hzero,min_eq_left hq]
  · have hqh : q ≤ h := hh.resolve_left hzero
    simp [hzero,min_eq_right hqh]

lemma cap_average_gap {I : Type*} [Fintype I]
    (w h : I → ℝ) (q : ℝ) (hq : 0 ≤ q) (hw : (∑ i,w i)=1)
    (hh : ∀ i,h i=0 ∨ q ≤ h i) :
    min (∑ i,w i*h i) q ≤ (∑ i,w i*min (h i) q)+
      q*(∑ i,w i*(if h i=0 then 1 else 0)) := by
  have he : (∑ i,w i*min (h i) q)+q*(∑ i,w i*(if h i=0 then 1 else 0))=q := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    calc
      _ = ∑ i,w i*(min (h i) q+q*(if h i=0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i,w i*q := by
        apply Finset.sum_congr rfl
        intro i _
        rw [cap_zero_decomposition (h i) q hq (hh i)]
      _ = q := by rw [← Finset.sum_mul,hw,one_mul]
  rw [he]
  exact min_le_right _ _

/-- All nonzero profiles lie above each cap. The sole correction is supported
on the zero-retention profiles; no convexity of the capped function is assumed. -/
theorem capped_average_bound {I J : Type*} [Fintype I] [Fintype J]
    (w h : I → ℝ) (a : ℝ) (q d : J → ℝ)
    (hw : (∑ i,w i)=1) (hq : ∀ j,0 ≤ q j) (hd : ∀ j,0 ≤ d j)
    (hh : ∀ i j,h i=0 ∨ q j ≤ h i) :
    cappedValue (∑ i,w i*h i) a q d ≤
      (∑ i,w i*cappedValue (h i) a q d)+
      (∑ i,w i*(if h i=0 then 1 else 0))*(∑ j,q j*d j) := by
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_right (cap_average_gap w h (q j) (hq j) hw
      (fun i => hh i j)) (hd j))
  unfold cappedValue
  calc
    _ ≤ (∑ i,w i*h i)*a+
      ∑ j,((∑ i,w i*min (h i) (q j))+
        q j*(∑ i,w i*(if h i=0 then 1 else 0)))*d j := add_le_add le_rfl hc
    _ = _ := by
      have hA : (∑ i,w i*h i)*a = ∑ i,w i*(h i*a) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hB : (∑ j,(∑ i,w i*min (h i) (q j))*d j) =
          ∑ i,w i*(∑ j,min (h i) (q j)*d j) := by
        simp_rw [Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hC (z : ℝ) : (∑ j,q j*z*d j)=z*(∑ j,q j*d j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib,hA,hB,hC]
      simp only [mul_add,Finset.sum_add_distrib,add_assoc]

/-- A positive upper bound for future increments may replace their exact
values in the correction. In particular, no subtraction of an upper test
bound is justified or used here. -/
theorem capped_average_bound_of_dominating {I J : Type*} [Fintype I] [Fintype J]
    (w h : I → ℝ) (a : ℝ) (q d D : J → ℝ)
    (hw0 : ∀ i,0 ≤ w i) (hw : (∑ i,w i)=1)
    (hq : ∀ j,0 ≤ q j) (hd : ∀ j,0 ≤ d j)
    (hD : ∀ j,d j ≤ D j) (hh : ∀ i j,h i=0 ∨ q j ≤ h i) :
    cappedValue (∑ i,w i*h i) a q d ≤
      (∑ i,w i*cappedValue (h i) a q d)+
      (∑ i,w i*(if h i=0 then 1 else 0))*(∑ j,q j*D j) := by
  have hh' := capped_average_bound w h a q d hw hq hd hh
  apply hh'.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hD j) (hq j))
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (by split_ifs <;> norm_num))

/-- Monotonicity bounds an increment by a difference of test values. The test
may be signed; dropping the lower endpoint instead would require positivity. -/
lemma monotone_increment_bound (φ : ℝ → ℝ) (hφ : Monotone φ)
    (lo u v hi : ℝ) (hu : lo ≤ u) (hv : v ≤ hi) :
    φ v-φ u ≤ φ hi-φ lo := sub_le_sub (hφ hv) (hφ hu)

/-- A correction that subtracts a baseline atom is safe for pointwise budget
transfer when that subtraction fits inside the original atom. The combined
measure is positive, so no exact-diagonal anchoring assumption is needed. -/
theorem positive_correction_transfer {Ω J : Type*} [Fintype Ω] [Fintype J]
    (ν : Ω → ℝ) (q : J → ℝ) (i : Ω) (f F : Ω → ℝ) (b B : J → ℝ)
    (hν : ∀ x,0 ≤ ν x) (hq : ∀ j,0 ≤ q j)
    (hfit : (∑ j,q j) ≤ ν i) (hf : ∀ x,f x ≤ F x) (hb : ∀ j,b j ≤ B j) :
    (∑ x,ν x*f x)+(∑ j,q j*(b j-f i)) ≤
      (∑ x,ν x*F x)+(∑ j,q j*(B j-F i)) := by
  have hs : ν i*(F i-f i) ≤ ∑ x,ν x*(F x-f x) :=
    Finset.single_le_sum (fun x _ => mul_nonneg (hν x) (sub_nonneg.mpr (hf x)))
      (Finset.mem_univ i)
  have hi : (∑ j,q j)*(F i-f i) ≤ ν i*(F i-f i) :=
    mul_le_mul_of_nonneg_right hfit (sub_nonneg.mpr (hf i))
  have hj : (∑ j,q j*b j) ≤ ∑ j,q j*B j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hb j) (hq j))
  simp_rw [mul_sub] at hs ⊢
  rw [Finset.sum_sub_distrib] at hs
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,← Finset.sum_mul]
  nlinarith

#print axioms positive_correction_transfer
#print axioms capped_average_bound
#print axioms capped_average_bound_of_dominating
end Erdos7CappedCurrentAveraging
