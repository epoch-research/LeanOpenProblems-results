import Submission.ConvexBudgetMinimax

/-! Compact feasible finite kernels and the anchored-budget minimax criterion.
This supplies a conditional kernel construction, not an odd-cover obstruction. -/
namespace Erdos7KernelBudgetMinimax
open scoped BigOperators
open Set Erdos7ConvexBudgetMinimax Erdos7BackwardFamilyBudget
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- A kernel has pointwise bounds, vanishes on the bad set, and satisfies
prescribed lower/upper row masses. The entries are the actual measure weights. -/
def KernelSet {Ω A : Type*} [Fintype A]
    (B : Ω × A → ℝ) (bad : Set (Ω × A)) (L U : Ω → ℝ) : Set (Ω × A → ℝ) :=
  {ν | ν ∈ Set.Icc 0 B ∧
    (∀ z ∈ bad, ν z = 0) ∧
    (∀ x, (∑ y, ν (x,y)) ∈ Set.Icc (L x) (U x))}

lemma row_continuous {Ω A : Type*} [Fintype A] (x : Ω) :
    Continuous (fun ν : Ω × A → ℝ => ∑ y, ν (x,y)) := by
  exact continuous_finset_sum _ (fun y _ => continuous_apply (x,y))

lemma kernelSet_closed {Ω A : Type*} [Fintype A]
    (B : Ω × A → ℝ) (bad : Set (Ω × A)) (L U : Ω → ℝ) :
    IsClosed (KernelSet B bad L U) := by
  have he : KernelSet B bad L U =
      Set.Icc 0 B ∩ (⋂ z ∈ bad, {ν | ν z = 0}) ∩
        (⋂ x, {ν | (∑ y, ν (x,y)) ∈ Set.Icc (L x) (U x)}) := by
    ext ν
    simp only [KernelSet,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
    tauto
  rw [he]
  refine (isClosed_Icc.inter ?_).inter ?_
  · exact isClosed_iInter (fun z => isClosed_iInter (fun _ =>
      isClosed_eq (continuous_apply z) continuous_const))
  · exact isClosed_iInter (fun x => isClosed_Icc.preimage (row_continuous x))

lemma kernelSet_compact {Ω A : Type*} [Fintype Ω] [Fintype A]
    (B : Ω × A → ℝ) (bad : Set (Ω × A)) (L U : Ω → ℝ) :
    IsCompact (KernelSet B bad L U) := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc 0 B) isCompact_Icc
    (kernelSet_closed B bad L U)
  exact fun _ h => h.1

lemma kernelSet_convex {Ω A : Type*} [Fintype A]
    (B : Ω × A → ℝ) (bad : Set (Ω × A)) (L U : Ω → ℝ) :
    Convex ℝ (KernelSet B bad L U) := by
  intro ν hν κ hκ a b ha hb hab
  refine ⟨convex_Icc (0 : Ω × A → ℝ) B hν.1 hκ.1 ha hb hab,?_,?_⟩
  · intro z hz
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hν.2.1 z hz,hκ.2.1 z hz,
      mul_zero,add_zero]
  · intro x
    have he : (∑ y, (a • ν+b • κ) (x,y)) = a*(∑ y,ν (x,y))+b*(∑ y,κ (x,y)) := by
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
        ← Finset.mul_sum]
    rw [he]
    simpa only [smul_eq_mul] using
      (convex_Icc (L x) (U x) (hν.2.2 x) (hκ.2.2 x) ha hb hab)

/-- A fully finite, actual-kernel application of the test-dependent criterion.
The input ν0 certifies feasibility; no numerical optimization is trusted.
The response estimate for all entire test profiles is still a hypothesis. -/
theorem exists_kernel_no_budget {Ω A T : Type}
    [Fintype Ω] [Fintype A] [Fintype T]
    (B : Ω × A → ℝ) (bad : Set (Ω × A)) (L U : Ω → ℝ)
    (ν0 : Ω × A → ℝ) (hν0 : ν0 ∈ KernelSet B bad L U)
    (F : ℝ → ℝ) (lo hi : ℝ) (X : T → Ω × A → ℝ)
    (hlh : lo ≤ hi) (hX : ∀ t z, X t z ∈ Set.Icc lo hi)
    (hF : MonotoneOn F (Set.Icc lo hi))
    (ε : ℝ) (hε : 0 < ε)
    (hresponse : ∀ φ, ValidTest F lo hi φ →
      ∃ ν ∈ KernelSet B bad L U, payoff F lo X φ ν ≤ -ε) :
    ∃ ν ∈ KernelSet B bad L U, ¬ HasBudget ν X F lo hi := by
  exact exists_no_budget F lo hi X (KernelSet B bad L U) ⟨ν0,hν0⟩
    (kernelSet_convex B bad L U) (kernelSet_compact B bad L U)
    (fun ν hν z => hν.1.1 z) hlh hX hF ε hε hresponse

#print axioms kernelSet_closed
#print axioms kernelSet_compact
#print axioms kernelSet_convex
#print axioms exists_kernel_no_budget
end Erdos7KernelBudgetMinimax
