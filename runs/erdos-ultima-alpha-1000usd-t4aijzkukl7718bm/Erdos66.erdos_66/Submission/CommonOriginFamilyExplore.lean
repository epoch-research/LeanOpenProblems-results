import Submission.CyclicVarianceExplore
import Submission.ParabolaRepairExplore

/-! Exact multiplicity correction for a finite family whose members meet
only at the origin. This is a finite-group counting identity. -/
namespace Erdos66CommonOriginFamily
open Erdos66MixedEnergy Erdos66CyclicVariance Erdos66OriginRepair
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma conv_indicators (A B : Finset G) (z : G) :
    conv (indicator A) (indicator B) z = (pairCount A B z : ℝ) := by
  simp only [conv,indicator,pairCount,ite_mul,one_mul,zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> rfl

lemma conv_zero_left (f : G → ℝ) (z : G) :
    conv (fun x ↦ if x=0 then 1 else 0) f z = f z := by
  simp [conv,ite_mul]

lemma conv_zero_right (f : G → ℝ) (z : G) :
    conv f (fun x ↦ if x=0 then 1 else 0) z = f z := by
  simp [conv,mul_ite,sub_eq_zero]

lemma conv_add_zeroMass (f : G → ℝ) (c : ℝ) (z : G) :
    conv (fun x ↦ f x+c*(if x=0 then 1 else 0))
      (fun x ↦ f x+c*(if x=0 then 1 else 0)) z =
      conv f f z+2*c*f z+c^2*(if z=0 then 1 else 0) := by
  let δ : G → ℝ := fun x ↦ if x=0 then 1 else 0
  have he (x : G) : (f x+c*δ x)*(f (z-x)+c*δ (z-x)) =
      f x*f (z-x)+c*(δ x*f (z-x))+c*(f x*δ (z-x))+c^2*(δ x*δ (z-x)) := by ring
  change (∑ x, (f x+c*δ x)*(f (z-x)+c*δ (z-x))) = _
  simp_rw [he,Finset.sum_add_distrib,← Finset.mul_sum]
  change conv f f z+c*conv δ f z+c*conv f δ z+c^2*conv δ δ z = _
  rw [conv_zero_left,conv_zero_right,conv_zero_left]
  dsimp only [δ]
  ring

lemma conv_sum_indicators {ι : Type*} (S : Finset ι) (C : ι → Finset G) (z : G) :
    conv (fun x ↦ ∑ i∈S, indicator (C i) x)
      (fun x ↦ ∑ i∈S, indicator (C i) x) z =
      ∑ i∈S, ∑ j∈S, (pairCount (C i) (C j) z : ℝ) := by
  unfold conv
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact conv_indicators (C i) (C j) z

omit [Fintype G] in
lemma sum_indicators_common_origin {ι : Type*} (S : Finset ι) (C : ι → Finset G)
    (hS : S.Nonempty) (hzero : ∀ i∈S, (0 : G)∈C i)
    (hinter : ∀ i∈S, ∀ j∈S, i ≠ j → ∀ x∈C i, x∈C j → x=0) (x : G) :
    (∑ i∈S, indicator (C i) x) =
      indicator (S.biUnion C) x+((S.card : ℝ)-1)*(if x=0 then 1 else 0) := by
  by_cases hx : x=0
  · subst x
    have hz : (0 : G)∈S.biUnion C := by
      obtain ⟨i,hi⟩ := hS
      exact Finset.mem_biUnion.mpr ⟨i,hi,hzero i hi⟩
    calc
      _ = ∑ _i∈S, (1 : ℝ) := Finset.sum_congr rfl (fun i hi ↦ by simp [indicator,hzero i hi])
      _ = (S.card : ℝ) := by simp
      _ = _ := by simp [indicator,hz]
  · simp only [if_neg hx,mul_zero,add_zero]
    by_cases hm : x∈S.biUnion C
    · obtain ⟨i,hi,hxi⟩ := Finset.mem_biUnion.mp hm
      rw [Finset.sum_eq_single i]
      · simp [indicator,hxi,hm]
      · intro j hj hji
        have hnot : x∉C j := fun hxj ↦ hx (hinter i hi j hj hji.symm x hxi hxj)
        simp [indicator,hnot]
      · exact fun h ↦ (h hi).elim
    · have hall (i : ι) (hi : i∈S) : x∉C i := fun hxi ↦ hm (Finset.mem_biUnion.mpr ⟨i,hi,hxi⟩)
      rw [Finset.sum_eq_zero (fun i hi ↦ by simp [indicator,hall i hi])]
      simp [indicator,hm]

/-- The sole excess multiplicity is the common origin. -/
theorem common_origin_correction {ι : Type*} (S : Finset ι) (C : ι → Finset G)
    (hS : S.Nonempty) (hzero : ∀ i∈S, (0 : G)∈C i)
    (hinter : ∀ i∈S, ∀ j∈S, i ≠ j → ∀ x∈C i, x∈C j → x=0) (z : G) :
    (∑ i∈S, ∑ j∈S, (pairCount (C i) (C j) z : ℝ)) =
      (pairCount (S.biUnion C) (S.biUnion C) z : ℝ)+
        2*((S.card : ℝ)-1)*indicator (S.biUnion C) z+
        ((S.card : ℝ)-1)^2*(if z=0 then 1 else 0) := by
  rw [← conv_sum_indicators]
  have he : (fun x ↦ ∑ i∈S, indicator (C i) x) =
      fun x ↦ indicator (S.biUnion C) x+((S.card : ℝ)-1)*(if x=0 then 1 else 0) :=
    funext (sum_indicators_common_origin S C hS hzero hinter)
  rw [he,conv_add_zeroMass,conv_indicators]

end Erdos66CommonOriginFamily
