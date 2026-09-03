import Submission.RectangleBudgetStep

/-! Preservation of actual box avoidance by coordinate retention kernels. -/
namespace Erdos7CompleteFamilyModel
open scoped BigOperators
open Erdos7FiniteRetentionKernel
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

lemma project_eq_of_prefix (e : Fin n → ℕ) (t : ℕ)
    (he : ∀ j,t ≤ j.val → e j = 0) : project t e = e := by
  funext j
  by_cases hj : j.val < t
  · simp [project,hj]
  · simp [project,hj,he j (Nat.le_of_not_gt hj)]

lemma project_full (e : Fin n → ℕ) : project n e = e := by
  funext j; simp [project,j.isLt]

lemma push_zero_of_fibers {Ω Ξ : Type} [Fintype Ω]
    (f : Ω → Ξ) (ν : Ω → ℝ) (z : Ξ) (hz : ∀ x,f x = z → ν x = 0) :
    push f ν z = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with h
  · exact hz x h
  · rfl

section Avoidance
variable (A : Fin n → Type) [∀ i,Fintype (A i)] [∀ i,Nonempty (A i)]
  [∀ i,DecidableEq (A i)]
variable (E : Fin n → ℕ) (X : Pattern E → ∀ i,Finset (A i))

def coveredAt (i : Fin n) (x : ∀ i,A i) : Prop :=
  currentBad A E X i.val i.isLt x (x i)

def AvoidsBefore (t : ℕ) (μ : (∀ i,A i) → ℝ) : Prop :=
  ∀ i : Fin n,i.val < t → ∀ x,coveredAt A E X i x → μ x = 0

lemma coveredAt_current_update (i : Fin n) (x : ∀ i,A i) (y : A i) :
    coveredAt A E X i (Function.update x i y) ↔ currentBad A E X i.val i.isLt x y := by
  dsimp only [coveredAt,currentBad]
  simp only [Function.update_self,indicator_update A i.val _ _ i le_rfl]

lemma coveredAt_later_update (i j : Fin n) (hij : i.val < j.val)
    (x : ∀ i,A i) (y : A j) :
    coveredAt A E X i (Function.update x j y) ↔ coveredAt A E X i x := by
  have hne : i ≠ j := by intro he; subst j; omega
  dsimp only [coveredAt,currentBad]
  simp only [Function.update_of_ne hne,indicator_update A i.val _ _ j hij.le]

/-- No old forbidden box is resurrected, and the current forbidden boxes are
zero in the actual pushforward measure. -/
lemma push_avoidsBefore (t : ℕ) (ht : t < n)
    (μ : (∀ i,A i) → ℝ) (havoid : AvoidsBefore A E X t μ)
    (ν : (∀ i,A i) → A ⟨t,ht⟩ → ℝ) (hν : ∀ x y,0 ≤ ν x y)
    (c : ℝ) (ρ : A ⟨t,ht⟩ → ℝ) (hcap : ∀ x y,ν x y ≤ c*μ x*ρ y)
    (hzero : ∀ x y,currentBad A E X t ht x y → ν x y = 0) :
    AvoidsBefore A E X (t+1)
      (push (fun z : (∀ i,A i) × A ⟨t,ht⟩ => Function.update z.1 ⟨t,ht⟩ z.2)
        (fun z => ν z.1 z.2)) := by
  intro i hi z hz
  apply push_zero_of_fibers
  intro xy hxy
  have hz' : coveredAt A E X i (Function.update xy.1 ⟨t,ht⟩ xy.2) := by
    rwa [hxy]
  by_cases hit : i.val = t
  · have hei : i = ⟨t,ht⟩ := Fin.ext hit
    subst i
    exact hzero xy.1 xy.2 ((coveredAt_current_update A E X ⟨t,ht⟩ xy.1 xy.2).mp hz')
  · have hi' : i.val < t := by omega
    have hcovered := (coveredAt_later_update A E X i ⟨t,ht⟩ hi' xy.1 xy.2).mp hz'
    have hm := havoid i hi' xy.1 hcovered
    apply le_antisymm _ (hν xy.1 xy.2)
    simpa only [hm,mul_zero,zero_mul] using hcap xy.1 xy.2

/-- A full box with a nonzero pattern belongs to its last active layer. -/
lemma full_box_has_layer (k : Pattern E) (hk : ∃ i,exponent E k i ≠ 0)
    (x : ∀ i,A i) (hx : indicator A n (exponent E k) (X k) x = 1) :
    ∃ i : Fin n,coveredAt A E X i x := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => exponent E k i ≠ 0)
  have hS : S.Nonempty := by obtain ⟨i,hi⟩ := hk; exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  let i := S.max' hS
  have hiS : i ∈ S := Finset.max'_mem S hS
  have hei : exponent E k i ≠ 0 := (Finset.mem_filter.mp hiS).2
  have htail : ∀ j,i.val+1 ≤ j.val → exponent E k j = 0 := by
    intro j hj
    by_contra he
    have hjs : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
    have hle : j ≤ i := Finset.le_max' S j hjs
    have hv : j.val ≤ i.val := hle
    omega
  have hstepcount : indicator A (i.val+1) (exponent E k) (X k) x = 1 := by
    simpa only [indicator,project_eq_of_prefix _ _ htail,project_full] using hx
  have hstep := indicator_step A i.val i.isLt (exponent E k) (X k) x (x i)
  simp only [Function.update_eq_self] at hstep
  have hboth : indicator A i.val (exponent E k) (X k) x = 1 ∧ x i ∈ X k i := by
    rw [hstepcount] at hstep
    by_cases hmem : x i ∈ X k i
    · refine ⟨?_,hmem⟩
      have hh : (1:ℝ) = indicator A i.val (exponent E k) (X k) x := by
        simpa only [hei,false_or,if_pos hmem] using hstep
      exact hh.symm
    · have hh : (1:ℝ) = 0 := by simpa only [hei,false_or,if_neg hmem] using hstep
      norm_num at hh
  let a : Fin (E i) := ⟨exponent E k i-1,by have := exponent_bound E k i; omega⟩
  refine ⟨i,a,k,?_,hboth⟩
  apply (currentFamily_labels E i.val i.isLt a k).mpr
  exact ⟨by change exponent E k i = (exponent E k i-1)+1; omega,htail⟩

lemma full_cover_zero (μ : (∀ i,A i) → ℝ) (havoid : AvoidsBefore A E X n μ)
    (hcover : ∀ x,∃ k : Pattern E,(∃ i,exponent E k i ≠ 0) ∧
      indicator A n (exponent E k) (X k) x = 1) : ∀ x,μ x = 0 := by
  intro x
  obtain ⟨k,hk,hx⟩ := hcover x
  obtain ⟨i,hi⟩ := full_box_has_layer A E X k hk x hx
  exact havoid i i.isLt x hi

end Avoidance
#print axioms push_avoidsBefore
#print axioms full_cover_zero
end Erdos7CompleteFamilyModel
