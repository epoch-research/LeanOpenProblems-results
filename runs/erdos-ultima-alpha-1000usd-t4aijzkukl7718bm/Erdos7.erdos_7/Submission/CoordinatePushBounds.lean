import Submission.DeficitRectangleTower

/-! Pointwise density control for coordinate-kernel pushforwards. -/
namespace Erdos7CoordinatePushBounds
open scoped BigOperators
open Erdos7FiniteRetentionKernel
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]

def swapCoordinate (i : ι) : ((∀ j,A j) × A i) ≃ ((∀ j,A j) × A i) where
  toFun z := (Function.update z.1 i z.2,z.1 i)
  invFun z := (Function.update z.1 i z.2,z.1 i)
  left_inv z := by
    apply Prod.ext
    · simp only [Function.update_idem,Function.update_eq_self]
    · simp only [Function.update_self]
  right_inv z := by
    apply Prod.ext
    · simp only [Function.update_idem,Function.update_eq_self]
    · simp only [Function.update_self]

lemma swapCoordinate_apply (i : ι) (z : (∀ j,A j) × A i) :
    swapCoordinate A i z = (Function.update z.1 i z.2,z.1 i) := rfl

lemma push_update (i : ι) (ν : (∀ j,A j) → A i → ℝ) (x : ∀ j,A j) :
    push (fun z : (∀ j,A j) × A i => Function.update z.1 i z.2) (fun z => ν z.1 z.2) x =
      ∑ v : A i,ν (Function.update x i v) (x i) := by
  classical
  letI : DecidableEq (∀ j,A j) := Classical.decEq _
  dsimp only [push]
  apply ((swapCoordinate A i).sum_comp (fun z : (∀ j,A j) × A i =>
    if Function.update z.1 i z.2 = x then ν z.1 z.2 else 0)).symm.trans
  simp only [swapCoordinate_apply,Function.update_idem,Function.update_eq_self,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp

lemma push_uniform_bound (i : ι) (μ : (∀ j,A j) → ℝ) (D c : ℝ) (hc : 0 ≤ c)
    (hμ : ∀ x,μ x ≤ D) (ν : (∀ j,A j) → A i → ℝ)
    (hcap : ∀ x y,ν x y ≤ c*μ x*(1/(Fintype.card (A i):ℝ))) (x : ∀ j,A j) :
    push (fun z : (∀ j,A j) × A i => Function.update z.1 i z.2) (fun z => ν z.1 z.2) x ≤ c*D := by
  rw [push_update]
  have hn : (Fintype.card (A i):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  calc
    _ ≤ ∑ _v : A i,c*D*(1/(Fintype.card (A i):ℝ)) := by
      apply Finset.sum_le_sum
      intro v _
      exact (hcap _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hμ _) hc) (by positivity))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      field_simp

lemma mass_le_card_mul {Ω : Type} [Fintype Ω] (s : Finset Ω) (μ : Ω → ℝ) (D : ℝ)
    (hD : ∀ x,μ x ≤ D) (hs : ∀ x,x ∉ s → μ x = 0) :
    (∑ x,μ x) ≤ s.card*D := by
  classical
  calc
    _ = ∑ x∈s,μ x := (Finset.sum_subset (Finset.subset_univ s) (fun x _ hx => hs x hx)).symm
    _ ≤ ∑ _x∈s,D := Finset.sum_le_sum (fun x _ => hD x)
    _ = _ := by simp

#print axioms push_uniform_bound
end Erdos7CoordinatePushBounds
