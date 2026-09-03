import Submission.DeficitRectangleTower

/-! Common-law prefix estimates and budget towers started after a finite block.
These are generic tools; no unrestricted numerical certificate is asserted. -/
namespace Erdos7DeficitFamilyBudget
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7FiniteRetentionKernel
set_option maxHeartbeats 2500000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- Every family may have a different extremizer. A single law that dominates
all convex monotone tests of each family still pays every family budget. -/
theorem common_law_bound {Ω α Ξ : Type} [Fintype Ω] [Fintype Ξ] [Nonempty α]
    (δ : ℝ) (μ : Ω → ℝ) (hμ : ∀ x,0 ≤ μ x) (X : α → Ω → ℝ)
    (F : ℝ → ℝ) (lo hi : ℝ) (ν : Ξ → ℝ) (hν : ∀ z,0 ≤ ν z)
    (Z : Ξ → ℝ) (hZ : ∀ z,Z z ∈ Set.Icc lo hi)
    (hcomp : ∀ a (φ : ℝ → ℝ),ConvexOn ℝ Set.univ φ → Monotone φ →
      (∑ x,μ x*φ (X a x)) ≤ (∑ x,μ x)*(∑ z,ν z*φ (Z z)))
    (hb : HasBudget δ μ X F lo hi) :
    (∑ x,μ x)*(1-∑ z,ν z*F (Z z)) ≤ δ := by
  obtain ⟨ι,inst,pick,φ,hφ,hdiag,hbudget⟩ := budget_normalize δ μ X F lo hi hb
  letI : Fintype ι := inst
  have hm : 0 ≤ ∑ x,μ x := Finset.sum_nonneg (fun x _ => hμ x)
  have htest (i : ι) := hcomp (pick i) (φ i) (hφ i).1 (hφ i).2
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => htest i)
  have he₁ : (∑ x,μ x*(∑ i,φ i (X (pick i) x))) =
      ∑ i,∑ x,μ x*φ i (X (pick i) x) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  have he₂ : (∑ i,(∑ x,μ x)*(∑ z,ν z*φ i (Z z))) =
      (∑ x,μ x)*(∑ z,ν z*(∑ i,φ i (Z z))) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  have hd : (∑ z,ν z*(∑ i,φ i (Z z))) ≤ ∑ z,ν z*F (Z z) :=
    Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hdiag (Z z) (hZ z)) (hν z))
  rw [he₂] at ht
  rw [he₁] at hbudget
  have hh := mul_le_mul_of_nonneg_left hd hm
  nlinarith

section Suffix
variable {n : ℕ}
variable {A : Fin n → Type} [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
  [∀ i,DecidableEq (A i)]
variable {E : Fin n → ℕ} {X : Pattern E → ∀ i,Finset (A i)}

/-- Start with any already-avoiding prefix measure. The same suffix kernels
transfer budgets for every deficit, rather than choosing kernels after seeing
what deficit is needed. -/
theorem exists_stage_from (S : BudgetSchedule A E X)
    (s t : ℕ) (hst : s ≤ t) (ht : t ≤ n)
    (μ₀ : (∀ i,A i) → ℝ) (hμ₀ : ∀ x,0 ≤ μ₀ x)
    (havoid₀ : AvoidsBefore A E X s μ₀) :
    ∃ μ : (∀ i,A i) → ℝ,(∀ x,0 ≤ μ x) ∧ AvoidsBefore A E X t μ ∧
      (∀ δ : ℝ, HasBudget δ μ (count A X : Family E (exponent E) t → _)
          (S.potential t) 1 (capacity E t) →
        HasBudget δ μ₀ (count A X : Family E (exponent E) s → _)
          (S.potential s) 1 (capacity E s)) := by
  induction t, hst using Nat.le_induction with
  | base => exact ⟨μ₀,hμ₀,havoid₀,fun _ => id⟩
  | succ t hst ih =>
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

/-- An exact common-law bound at an intermediate stage is enough for the
entire remaining finite tower. -/
theorem exists_surviving_mass_from_law {Ξ : Type} [Fintype Ξ]
    (S : BudgetSchedule A E X) (s : ℕ) (hs : s ≤ n)
    (hterminal : S.potential n = fun _ => 0)
    (μ₀ : (∀ i,A i) → ℝ) (hμ₀ : ∀ x,0 ≤ μ₀ x)
    (havoid₀ : AvoidsBefore A E X s μ₀)
    [Nonempty (Family E (exponent E) s)]
    (ν : Ξ → ℝ) (hν : ∀ z,0 ≤ ν z) (Z : Ξ → ℝ)
    (hZ : ∀ z,Z z ∈ Set.Icc (1:ℝ) (capacity E s))
    (hcomp : ∀ b : Family E (exponent E) s,∀ φ : ℝ → ℝ,
      ConvexOn ℝ Set.univ φ → Monotone φ →
      (∑ x,μ₀ x*φ (count A X b x)) ≤ (∑ x,μ₀ x)*(∑ z,ν z*φ (Z z))) :
    ∃ μ : (∀ i,A i) → ℝ,(∀ x,0 ≤ μ x) ∧ AvoidsBefore A E X n μ ∧
      (∑ x,μ₀ x)*(1-∑ z,ν z*S.potential s (Z z)) ≤ ∑ x,μ x := by
  obtain ⟨μ,hμ,havoid,hback⟩ := exists_stage_from S s n hs le_rfl μ₀ hμ₀ havoid₀
  refine ⟨μ,hμ,havoid,?_⟩
  have hb := terminal_budget μ (count A X : Family E (exponent E) n → _) 1 (capacity E n)
  rw [← hterminal] at hb
  exact common_law_bound (∑ x,μ x) μ₀ hμ₀ (count A X) (S.potential s)
    1 (capacity E s) ν hν Z hZ hcomp (hback _ hb)
end Suffix

#print axioms common_law_bound
#print axioms exists_stage_from
#print axioms exists_surviving_mass_from_law
end Erdos7DeficitFamilyBudget
