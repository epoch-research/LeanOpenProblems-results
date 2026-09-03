import Submission.RectangleBudgetTower

/-! Ordinary family budgets transferred along a suffix of a rectangle tower. -/
namespace Erdos7CompleteFamilyModel.BudgetSchedule
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7BackwardFamilyBudget Erdos7FiniteRetentionKernel
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {A : Fin n → Type} [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
  [∀ i,DecidableEq (A i)] {E : Fin n → ℕ} {X : Pattern E → ∀ i,Finset (A i)}

/-- One suffix measure and avoidance invariant suffice to pull any terminal
family budget back to an already-processed block. -/
theorem exists_stage_from (S : BudgetSchedule A E X) (s t : ℕ) (hst : s≤t) (ht : t≤n)
    (μ₀ : (∀ i,A i) → ℝ) (hμ₀ : ∀ x,0≤μ₀ x) (havoid₀ : AvoidsBefore A E X s μ₀) :
    ∃ μ : (∀ i,A i) → ℝ,(∀ x,0≤μ x) ∧ AvoidsBefore A E X t μ ∧
      (HasBudget μ (count A X : Family E (exponent E) t → _) (S.potential t) 1 (capacity E t) →
       HasBudget μ₀ (count A X : Family E (exponent E) s → _) (S.potential s) 1 (capacity E s)) := by
  induction t,hst using Nat.le_induction with
  | base => exact ⟨μ₀,hμ₀,havoid₀,id⟩
  | succ t hst ih =>
    have htn : t<n := by omega
    let i : Fin n := ⟨t,htn⟩
    obtain ⟨μ,hμ,havoid,hback⟩ := ih (by omega)
    obtain ⟨ν,hν,hcap,hzero,hmass,hstep⟩ := exists_rectangle_budget_step A E X t htn μ hμ
      (S.density i) (S.density_nonneg i) (S.density_mass i)
      (S.q i) (S.cap i) (S.cut i) (S.q_pos i) (S.cap_nonneg i)
      (S.tail i) (S.tail_nonneg i) (S.tail_decreasing i) (S.tail_zero i)
      (S.current_mass i) (S.box_density i) (S.U i) (S.V i)
      (S.potential t) (S.potential (t+1))
      (S.convex_U i) (S.monotone_U i) (S.nonneg_V i) (S.sum_le_potential i) (S.dual i)
    let f : ((∀ i,A i) × A i) → (∀ i,A i) := fun z => Function.update z.1 i z.2
    let μ' := push f (fun z => ν z.1 z.2)
    refine ⟨μ',push_nonneg f _ (fun z => hν z.1 z.2),?_,?_⟩
    · exact push_avoidsBefore A E X t htn μ havoid ν hν (S.cap i) (S.density i) hcap hzero
    · exact hback ∘ hstep

/-- Under a full cover, every already-avoiding prefix measure has the stated
backward budget. This is the input contradicted by a strict block certificate. -/
theorem budget_of_full_cover (S : BudgetSchedule A E X)
    (hterminal : S.potential n=fun _ => 0)
    (s : ℕ) (hs : s≤n) (μ₀ : (∀ i,A i) → ℝ) (hμ₀ : ∀ x,0≤μ₀ x)
    (havoid₀ : AvoidsBefore A E X s μ₀)
    (hcover : ∀ x,∃ k : Pattern E,(∃ i,exponent E k i≠0) ∧
      indicator A n (exponent E k) (X k) x=1) :
    HasBudget μ₀ (count A X : Family E (exponent E) s → _) (S.potential s) 1 (capacity E s) := by
  obtain ⟨μ,hμ,havoid,hback⟩ := S.exists_stage_from s n hs le_rfl μ₀ hμ₀ havoid₀
  have hzero := full_cover_zero A E X μ havoid hcover
  have hmass : (∑ x,μ x)=0 := Finset.sum_eq_zero (fun x _ => hzero x)
  apply hback
  rw [hterminal]
  exact zero_mass_budget μ (count A X : Family E (exponent E) n → _) 1 (capacity E n) hmass

#print axioms budget_of_full_cover
end Erdos7CompleteFamilyModel.BudgetSchedule
