import Submission.FiniteKernelCrossing

/-! Kernels obtained from uniform finite choices, with noninjective next-state
maps permitted. Repeated next states have their correct multiplicity. -/
namespace Erdos773.FiniteKernelChoices
open Finset FiniteKernelCrossing
set_option maxHeartbeats 2000000
noncomputable section
variable {σ β : Type*} [Fintype σ] [DecidableEq σ]

lemma weighted_fiber_sum (A : Finset β) (next : β → σ) (f : σ → ℝ) :
    (∑ y : σ, ((A.filter (fun a => next a = y)).card:ℝ)*f y) = ∑ a ∈ A, f (next a) := by
  classical
  simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    sum_mul,ite_mul,one_mul,zero_mul]
  rw [sum_comm]
  simp

/-- Uniform actions pushed through an arbitrary next-state map. -/
def ofChoices (A : σ → Finset β) (hne : ∀ x, (A x).Nonempty) (next : σ → β → σ) : Kernel σ where
  weight x y := by
    classical
    exact ((A x).filter (fun a => next x a = y)).card/(A x).card
  nonneg x y := by positivity
  total x := by
    classical
    have hp : (0:ℝ) < (A x).card := by exact_mod_cast card_pos.mpr (hne x)
    have hc : (∑ y : σ, (((A x).filter (fun a => next x a = y)).card:ℝ)) = (A x).card := by
      simpa only [mul_one,sum_const,nsmul_eq_mul,mul_one] using weighted_fiber_sum (A x) (next x) (fun _ => 1)
    rw [← sum_div,hc,div_self hp.ne']

lemma ofChoices_avg (A : σ → Finset β) (hne : ∀ x, (A x).Nonempty)
    (next : σ → β → σ) (f : σ → ℝ) (x : σ) :
    (ofChoices A hne next).avg f x = (∑ a ∈ A x, f (next x a))/(A x).card := by
  classical
  change (∑ y : σ, ((((A x).filter (fun a => next x a = y)).card:ℝ)/(A x).card)*f y) = _
  simp only [div_mul_eq_mul_div,← sum_div]
  rw [weighted_fiber_sum]

lemma ofChoices_support (A : σ → Finset β) (hne : ∀ x, (A x).Nonempty)
    (next : σ → β → σ) (x y : σ) :
    0 < (ofChoices A hne next).weight x y ↔ ∃ a ∈ A x, next x a = y := by
  classical
  have hp : (0:ℝ) < (A x).card := by exact_mod_cast card_pos.mpr (hne x)
  change 0 < ((((A x).filter (fun a => next x a = y)).card:ℝ)/(A x).card) ↔ _
  rw [div_pos_iff_of_pos_right hp,Nat.cast_pos,card_pos,filter_nonempty_iff]

#print axioms weighted_fiber_sum
#print axioms ofChoices_avg
#print axioms ofChoices_support
end
end Erdos773.FiniteKernelChoices
