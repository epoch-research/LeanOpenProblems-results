import Submission.RectangleAvoidance

/-! A concrete finite coordinate tower driven by scalar family budgets. -/
namespace Erdos7CompleteFamilyModel
open scoped BigOperators
open Erdos7BackwardFamilyBudget Erdos7CappedRetentionRows
open Erdos7FiniteRetentionKernel Erdos7KernelFamilyCompression
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}
variable (A : Fin n → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
  [∀ i,DecidableEq (A i)]
variable (E : Fin n → ℕ) (X : Pattern E → ∀ i,Finset (A i))

/-- All scalar controls and their local certificates for a finite rectangle. -/
structure BudgetSchedule where
  density : ∀ i,A i → ℝ
  q : Fin n → ℝ
  cap : Fin n → ℝ
  cut : Fin n → ℝ
  tail : Fin n → ℕ → ℝ
  potential : ℕ → ℝ → ℝ
  U : Fin n → ℝ → ℝ
  V : Fin n → ℝ → ℝ
  density_nonneg : ∀ i y,0 ≤ density i y
  density_mass : ∀ i,(∑ y,density i y) = 1
  q_pos : ∀ i,0 < q i
  cap_nonneg : ∀ i,0 ≤ cap i
  tail_nonneg : ∀ i j,j < E i → 0 ≤ tail i j
  tail_decreasing : ∀ i j,tail i (j+1) ≤ tail i j
  tail_zero : ∀ i,tail i (E i) = 0
  current_mass : ∀ i,(∑ a : Fin (E i),q i*tail i a.val) ≤ 1
  box_density : ∀ i k,exponent E k i ≠ 0 →
    (∑ y,if y ∈ X k i then density i y else 0) ≤ tail i (exponent E k i-1)
  convex_U : ∀ i,ConvexOn ℝ Set.univ (U i)
  monotone_U : ∀ i,Monotone (U i)
  nonneg_V : ∀ i u,u ∈ Set.Icc (1:ℝ) (capacity E i.val) → 0 ≤ V i u
  sum_le_potential : ∀ i u,u ∈ Set.Icc (1:ℝ) (capacity E i.val) →
    U i u+V i u ≤ potential i.val u
  dual : ∀ i k,k ∈ Set.Icc (1:ℝ) (capacity E i.val) →
    ∀ u,u ∈ Set.Icc (1:ℝ) (capacity E i.val) →
      1-retained (q i) (cap i) (cut i) k +
        (∑ d : Option (Fin (E i)),
          coefficient (retained (q i) (cap i) (cut i) k)
            (fun j => cap i*tail i j) (E i) d * potential (i.val+1) (multiplier d*u)) ≤
      U i k+V i u

namespace BudgetSchedule
variable {A E X}

/-- The existential induction keeps the measure, avoidance, and composed
backward budget implication together. -/
theorem exists_stage (S : BudgetSchedule A E X)
    (μ₀ : (∀ i,A i) → ℝ) (hμ₀ : ∀ x,0 ≤ μ₀ x)
    (t : ℕ) (ht : t ≤ n) :
    ∃ μ : (∀ i,A i) → ℝ,(∀ x,0 ≤ μ x) ∧ AvoidsBefore A E X t μ ∧
      (HasBudget μ (count A X : Family E (exponent E) t → _)
          (S.potential t) 1 (capacity E t) →
        HasBudget μ₀ (count A X : Family E (exponent E) 0 → _)
          (S.potential 0) 1 (capacity E 0)) := by
  induction t with
  | zero =>
    refine ⟨μ₀,hμ₀,?_,id⟩
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
    · exact hback ∘ hstep

/-- A strict initial budget rules out a full covering by the nonzero patterns. -/
theorem not_full_cover (S : BudgetSchedule A E X)
    (hterminal : S.potential n = fun _ => 0) (hroot : S.potential 0 1 < 1) :
    ¬ (∀ x,∃ k : Pattern E,(∃ i,exponent E k i ≠ 0) ∧
      indicator A n (exponent E k) (X k) x = 1) := by
  intro hcover
  let μ₀ : (∀ i,A i) → ℝ := fun _ => 1
  obtain ⟨μ,hμ,havoid,hback⟩ := S.exists_stage μ₀ (fun _ => by norm_num [μ₀]) n le_rfl
  have hzero := full_cover_zero A E X μ havoid hcover
  have hmass : (∑ x,μ x) = 0 := Finset.sum_eq_zero (fun x _ => hzero x)
  have hbudget := zero_mass_budget μ (count A X : Family E (exponent E) n → _)
    1 (capacity E n) hmass
  rw [← hterminal] at hbudget
  have hstart := hback hbudget
  apply not_budget_constant_count μ₀ (count A X : Family E (exponent E) 0 → _)
    (S.potential 0) 1 (capacity E 0) 1 (fun _ => by norm_num [μ₀]) ?_
    (by simp [capacity]) (count_initial A X) hroot hstart
  simp only [μ₀,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact Nat.cast_pos.mpr Fintype.card_pos

end BudgetSchedule
#print axioms BudgetSchedule.not_full_cover
end Erdos7CompleteFamilyModel
