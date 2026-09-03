import Submission.TernaryTwoSharedComparison
import Submission.BackwardFamilyBudget

/-! Positive current mixtures of the shared-prefix comparison. All future
labels remain independent; only the reference measure is common. -/
namespace Erdos7TernaryTwoMixedComparison
open scoped BigOperators
open Erdos7TernaryTwoSharedPrefix Erdos7TernaryTwoSharedComparison
set_option maxHeartbeats 2500000
variable {J : Type*} [Fintype J]

noncomputable def actualWeight (w : Fin 10 → ℝ) (r : J → ℝ)
    (z : Fin 5 ⊕ (J × Fin 5)) : ℝ :=
  ∑ c,w c*Erdos7TernaryTwoSharedComparison.actualWeight c r z
noncomputable def refWeight (w : Fin 10 → ℝ) (r : J → ℝ)
    (z : Fin 3 ⊕ (J × Fin 3)) : ℝ :=
  ∑ c,w c*Erdos7TernaryTwoSharedComparison.refWeight c r z

lemma actual_nonneg (w : Fin 10 → ℝ) (r : J → ℝ)
    (hw : ∀ c,0≤w c) (hr : ∀ j,0≤r j) : ∀ z,0≤actualWeight w r z := by
  intro z
  exact Finset.sum_nonneg (fun c _ => mul_nonneg (hw c)
    (Erdos7TernaryTwoSharedComparison.actual_nonneg c r hr z))

lemma ref_nonneg (w : Fin 10 → ℝ) (r : J → ℝ)
    (hw : ∀ c,0≤w c) (hr : ∀ j,0≤r j) : ∀ z,0≤refWeight w r z := by
  intro z
  exact Finset.sum_nonneg (fun c _ => mul_nonneg (hw c)
    (Erdos7TernaryTwoSharedComparison.ref_nonneg c r hr z))

lemma mass_eq (w : Fin 10 → ℝ) (r : J → ℝ) :
    (∑ z,actualWeight w r z)=∑ z,refWeight w r z := by
  unfold actualWeight refWeight
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,Erdos7TernaryTwoSharedComparison.mass_eq]

lemma weightNum_cast (c : Fin 10) (x : Fin 5) :
    (weightNum c x : ℝ)=16-5*(count c x : ℝ) := by
  have h : 5*count c x≤16 := by have hh := (data.1 c x).2; omega
  rw [weightNum,Nat.cast_sub h]
  push_cast
  rfl

lemma first_weight (w : Fin 10 → ℝ) (r : J → ℝ) (hw : (∑ c,w c)=1) (x : Fin 5) :
    actualWeight w r (.inl x) =
      ((∑ c,w c*(1-(count c x : ℝ)/4))-1/5)/5 := by
  simp only [actualWeight,Erdos7TernaryTwoSharedComparison.actualWeight,Sum.elim_inl,weightNum_cast]
  simp_rw [mul_sub,← mul_div_assoc,Finset.sum_sub_distrib]
  rw [← Finset.sum_div,← Finset.sum_mul,hw]
  rw [← Finset.sum_div]
  have he : (∑ i,w i*(16-5*(count i x : ℝ)))=16-5*∑ i,w i*(count i x : ℝ) := by
    calc
      _ = ∑ i,(16*w i-5*(w i*(count i x : ℝ))) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hw]; ring
  rw [he]
  ring

/-- Simultaneous averaging of complete future sequences and current corners.
The former may be chosen separately for every eventual convex test. -/
theorem averaged_comparison {I : Type*} (S : Finset I) (v : I → ℝ)
    (hv : ∀ i∈S,0≤v i) (hv1 : (∑ i∈S,v i)=1)
    (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c)
    (a : I → ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ)
    (hr : ∀ j,0≤r j) (hd : ∀ j,2≤d j) (hmass : (∑ j,r j)=1/5)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ z,actualWeight w r z*φ (∑ i∈S,v i*(actualCount (a i) d z : ℝ))) ≤
      ∑ z,refWeight w r z*φ (refCount d z) := by
  simp only [actualWeight,refWeight,Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  simp only [mul_assoc,← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (Erdos7TernaryTwoSharedComparison.averaged_comparison S v hv hv1 c a r d hr hd hmass φ hφ hmφ) (hw c)

/-- Pointwise domination before averaging is permitted for signed monotone
convex tests, because the actual comparison weights are nonnegative. -/
theorem dominated_comparison {I : Type*} (S : Finset I) (v : I → ℝ)
    (hv : ∀ i∈S,0≤v i) (hv1 : (∑ i∈S,v i)=1)
    (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c)
    (a : I → ℕ → Fin 10) (r : J → ℝ) (d : J → ℕ)
    (hr : ∀ j,0≤r j) (hd : ∀ j,2≤d j) (hmass : (∑ j,r j)=1/5)
    (Y : Fin 5 ⊕ (J × Fin 5) → ℝ)
    (hY : ∀ z,Y z≤∑ i∈S,v i*(actualCount (a i) d z : ℝ))
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ z,actualWeight w r z*φ (Y z)) ≤ ∑ z,refWeight w r z*φ (refCount d z) := by
  apply (Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hmφ (hY z))
    (actual_nonneg w r hw hr z))).trans
  exact averaged_comparison S v hv hv1 w hw a r d hr hd hmass φ hφ hmφ

/-- A common positive reference measure excludes a family budget when its
cost is strictly below the actual mass. No common maximizing family is used. -/
theorem not_budget_of_common_reference {Ω α Z : Type} [Fintype Ω] [Fintype Z] [Nonempty α]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (r : Z → ℝ) (hr : ∀ z,0≤r z) (v : Z → ℝ) (hv : ∀ z,v z∈Set.Icc lo hi)
    (hcomp : ∀ a φ,ConvexOn ℝ Set.univ φ → Monotone φ →
      (∑ x,μ x*φ (X a x))≤∑ z,r z*φ (v z))
    (hstrict : (∑ z,r z*F (v z))<∑ x,μ x) :
    ¬ Erdos7BackwardFamilyBudget.HasBudget μ X F lo hi := by
  intro hb
  obtain ⟨I,inst,pick,φ,hφ,hdiag,hbudget⟩ :=
    Erdos7BackwardFamilyBudget.budget_normalize μ X F lo hi hb
  letI : Fintype I := inst
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    hcomp (pick i) (φ i) (hφ i).1 (hφ i).2)
  have hd := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (hdiag (v z) (hv z)) (hr z))
  simp only [Finset.mul_sum] at hbudget hd
  rw [Finset.sum_comm] at hbudget
  conv_rhs at hh => rw [Finset.sum_comm]
  exact (not_lt_of_ge (hbudget.trans (hh.trans hd))) hstrict

#print axioms dominated_comparison
#print axioms not_budget_of_common_reference
end Erdos7TernaryTwoMixedComparison
