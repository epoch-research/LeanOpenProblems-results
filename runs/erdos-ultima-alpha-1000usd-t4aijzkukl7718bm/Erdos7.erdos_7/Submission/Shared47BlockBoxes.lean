import Submission.Shared47ScheduleChecked
import Submission.Shared47Root
import Submission.RectangleBudgetSuffix
import Submission.TernaryTwoCurrentWeights
import Submission.TernaryTwoFamilyGroups

/-! The certified shared-prefix block and suffix exclude complete rectangle
covers with the stated actual ternary section geometry. -/
namespace Erdos7Shared47BlockBoxes
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7FiniteRetentionKernel
open Erdos7TernaryTwoCoherentMixture Erdos7TernaryTwoFamilySlices
open Erdos7TernaryTwoFamilyGroups
set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable (A : Fin 14 → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)] [∀ i,DecidableEq (A i)]
variable (E : Fin 14 → ℕ) (X : Pattern E → ∀ i,Finset (A i))

/-- Arbitrary finite suffix exponents are allowed. The only geometric input
at the first coordinate is a five-point avoiding embedding with branch/point
section bounds; no irredundance or nonempty completion is assumed. -/
theorem not_full_cover (D : ℕ) (hE0 : E 0=2) (hE1 : E 1=D+1)
    (ξ : Fin 5 → ∀ i,A i) (havoid0 : ∀ x,¬coveredAt A E X 0 (ξ x))
    (hbranch : ∀ k,exponent E k 0=1 → ∃ q : Fin 2,∀ x,
      indicator A 1 (exponent E k) (X k) (ξ x)≤(if branch x=q then (1:ℝ) else 0))
    (hpoint : ∀ k,exponent E k 0=2 → ∃ y : Fin 5,∀ x,
      indicator A 1 (exponent E k) (X k) (ξ x)≤(if x=y then (1:ℝ) else 0))
    (ρ : ∀ i,A i → ℝ) (hρ : ∀ i y,0≤ρ i y) (hρmass : ∀ i,(∑ y,ρ i y)=1)
    (hd5 : ∀ k,exponent E k 1≠0 →
      (∑ y,if y∈X k 1 then ρ 1 y else 0)≤1/(5:ℝ)^(exponent E k 1))
    (hd : ∀ j : Fin 12,∀ k,exponent E k (j.natAdd 2)≠0 →
      (∑ y,if y∈X k (j.natAdd 2) then ρ (j.natAdd 2) y else 0)≤
        1/((Erdos7Shared47Schedule.later j).p:ℝ)^(exponent E k (j.natAdd 2))) :
    ¬ (∀ x,∃ k : Pattern E,(∃ i,exponent E k i≠0) ∧
      indicator A 14 (exponent E k) (X k) x=1) := by
  intro hcover
  obtain ⟨w,ν,hw,hm,hν,hcap,hzero,hmass⟩ := Erdos7TernaryTwoCurrentWeights.exists_kernel
    E A X ξ hE0 hbranch hpoint (ρ 1) (hρ 1) (hρmass 1) hd5
  let f : Fin 5 × A 1 → ∀ i,A i := fun z => Function.update (ξ z.1) 1 z.2
  let μ : (∀ i,A i) → ℝ := push f (fun z => ν z.1 z.2)
  have hμ : ∀ x,0≤μ x := push_nonneg f _ (fun z => hν z.1 z.2)
  have havoid : AvoidsBefore A E X 2 μ := by
    intro i hi z hz
    apply push_zero_of_fibers
    intro xy hxy
    have hc : coveredAt A E X i (Function.update (ξ xy.1) 1 xy.2) := by
      change coveredAt A E X i (f xy)
      rwa [hxy]
    by_cases hi0 : i=0
    · subst i
      exact False.elim (havoid0 xy.1 ((coveredAt_later_update A E X 0 1 (by decide) (ξ xy.1) xy.2).mp hc))
    · have hi1 : i=1 := by apply Fin.ext; have hh : i.val≠0 := fun h => hi0 (Fin.ext h); omega
      subst i
      exact hzero xy.1 xy.2 ((coveredAt_current_update A E X 1 (ξ xy.1) xy.2).mp hc)
  let S := Erdos7Shared47Schedule.schedule A E X Erdos7Shared47Schedule.later_valid ρ hρ hρmass hd
  have ht : S.potential 14=fun _ => 0 := Erdos7Shared47Schedule.potential_terminal
  have hb := S.budget_of_full_cover ht 2 (by omega) μ hμ havoid hcover
  have hbp := budget_of_push f (fun z => ν z.1 z.2)
    (count A X : Family E (exponent E) 2 → _) (S.potential 2) 1 (capacity E 2) hb
  have hcapacity : (capacity E 2:ℝ)=3*((D:ℝ)+2) := by
    norm_num [capacity,hE0,hE1]
    ring
  have hcount : (fun b : Family E (exponent E) 2 => fun z : Fin 5 × A 1 => count A X b (f z))=
      (fun b z => slice A X ξ b 0 z.1+∑ j∈Finset.range (D+1),group A X ξ b j z.1 z.2) := by
    funext b z
    simpa only [f,hE1] using count_decomposition A X ξ b (exponent_bound E) z.1 z.2
  rw [hcount,hcapacity] at hbp
  change Erdos7BackwardFamilyBudget.HasBudget (fun z : Fin 5 × A 1 => ν z.1 z.2)
    (fun b z => slice A X ξ b 0 z.1+∑ j∈Finset.range (D+1),group A X ξ b j z.1 z.2)
    (Erdos7Shared47Real.evalR Erdos7Shared47Rows.stage7.F) 1 (3*((D:ℝ)+2)) at hbp
  apply Erdos7Shared47Root.block_not_budget w hw hm D ν hν hmass
    (fun b j x => slice A X ξ b j x) (fun b j x y => group A X ξ b j x y)
    (fun b j hj x => slice_nonneg A X ξ b (j+1) x)
    (fun b j hj x y => group_nonneg A X ξ b j x y)
    (fun b j hj x y => group_le_slice A X ξ b j x y) ?_ ?_ hbp
  · intro b j hj x
    simpa only [Erdos7TernaryTwoBlockCompression.tail,if_pos hj] using group_marginal A X ξ b j x ν (ρ 1) hcap hd5
  · intro b j hj
    exact slice_profile A X ξ b (exponent_bound E) hE0 hbranch hpoint j (by omega)

#print axioms not_full_cover
end Erdos7Shared47BlockBoxes
