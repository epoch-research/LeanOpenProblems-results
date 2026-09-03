import Submission.DeficitRectangleStep
import Submission.RectangleBudgetTower

/-! Quantitative finite survival from certified scalar family budgets. -/
namespace Erdos7DeficitFamilyBudget
open scoped BigOperators
open Erdos7CappedRetentionRows Erdos7FiniteRetentionKernel Erdos7KernelFamilyCompression
open Erdos7CompleteFamilyModel
set_option maxHeartbeats 2500000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}
variable {A : Fin n → Type} [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
  [∀ i,DecidableEq (A i)]
variable {E : Fin n → ℕ} {X : Pattern E → ∀ i,Finset (A i)}

theorem exists_stage (S : BudgetSchedule A E X)
    (μ₀ : (∀ i,A i) → ℝ) (hμ₀ : ∀ x,0 ≤ μ₀ x)
    (t : ℕ) (ht : t ≤ n) :
    ∃ μ : (∀ i,A i) → ℝ,(∀ x,0 ≤ μ x) ∧ AvoidsBefore A E X t μ ∧
      (∀ δ : ℝ, HasBudget δ μ (count A X : Family E (exponent E) t → _)
          (S.potential t) 1 (capacity E t) →
        HasBudget δ μ₀ (count A X : Family E (exponent E) 0 → _)
          (S.potential 0) 1 (capacity E 0)) := by
  induction t with
  | zero =>
    refine ⟨μ₀,hμ₀,?_,fun _ => id⟩
    intro i hi
    omega
  | succ t ih =>
    have htn : t < n := by omega
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
    · exact fun δ => hback δ ∘ hstep δ


/-- The retained mass is at least one minus the initial scalar budget,
without taking a limit or assuming a positive infinite-horizon gap. -/
theorem exists_surviving_mass (S : BudgetSchedule A E X)
    (hterminal : S.potential n = fun _ => 0)
    (μ₀ : (∀ i,A i) → ℝ) (hμ₀ : ∀ x,0 ≤ μ₀ x) :
    ∃ μ : (∀ i,A i) → ℝ,(∀ x,0 ≤ μ x) ∧ AvoidsBefore A E X n μ ∧
      (∑ x,μ₀ x)*(1-S.potential 0 1) ≤ ∑ x,μ x := by
  obtain ⟨μ,hμ,havoid,hback⟩ := exists_stage S μ₀ hμ₀ n le_rfl
  refine ⟨μ,hμ,havoid,?_⟩
  have hb := terminal_budget μ (count A X : Family E (exponent E) n → _) 1 (capacity E n)
  rw [← hterminal] at hb
  have hstart := hback (∑ x,μ x) hb
  exact constant_count_bound _ μ₀ (count A X : Family E (exponent E) 0 → _)
    (S.potential 0) 1 (capacity E 0) 1 hμ₀ (by simp [capacity]) (count_initial A X) hstart

#print axioms exists_surviving_mass
end Erdos7DeficitFamilyBudget
