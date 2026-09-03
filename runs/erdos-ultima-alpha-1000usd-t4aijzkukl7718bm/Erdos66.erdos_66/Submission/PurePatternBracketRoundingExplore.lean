import Submission.ExactBracketPatternCompactnessExplore
import Submission.ExactBracketPatternCostsExplore

/-! Countably many nonnegative polynomial constraints with exact brackets,
without requiring any representation-cost family. -/
namespace Erdos66PurePatternBracketRounding
open Erdos66NaturalPositivePattern Erdos66ExactBracketPatternCompactness
  Erdos66ExactBracketPatternCosts Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli
  Erdos66ClampedPrefixContinuation Erdos66OrderedPipagePrefix
open scoped Classical
set_option maxHeartbeats 2500000

 theorem exists_pattern_rounding (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (P : ℕ → Pattern) (hP : ∀ S : Finset ℕ, (∑ j∈S, (P j).eval p) ≤ 1) :
    ∃ A : Set ℕ, (∀ L, PrefixBrackets p A L) ∧
      ∀ S : Finset ℕ, (∑ j∈S, (P j).value (fun i ↦ decide (i∈A))) ≤ 1 := by
  have hfinite (L : ℕ) : ∃ A : Set ℕ, PrefixBrackets p A L ∧
      (∑ j∈Finset.range L, (P j).value (fun i ↦ decide (i∈A))) ≤ 1 ∧
      (∀ j ≤ L, ∀ K ≤ L, (∑ _n∈Finset.range K, (0 : ℝ)) ≤ 1) := by
    let C := max L ((Finset.range L).sup (fun j ↦ (P j).bound))
    have hLC : L ≤ C := le_max_left _ _
    obtain ⟨ω,hbr,hcost⟩ := exists_pattern_selection C (Finset.range L) P
      (fun j hj ↦ (Finset.le_sup (f := fun j ↦ (P j).bound) hj).trans (le_max_right _ _))
      (∅ : Finset ℕ) (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) (by simp) p hp
    simp only [Finset.sum_empty,add_zero] at hcost
    refine ⟨selected C ω,fun k hk ↦ selected_prefix_brackets C p ω hbr k (by omega),
      hcost.trans (hP (Finset.range L)),?_⟩
    intro _ _ _ _
    simp
  obtain ⟨A,hbr,hpat,_⟩ := exists_summable_costs_with_patterns p P (fun _ _ _ ↦ 0)
    (fun _ _ ↦ continuous_const) (fun _ _ _ ↦ le_rfl) hfinite
  exact ⟨A,hbr,hpat⟩

 theorem exists_indexed_pattern_rounding {α : Type*} [Denumerable α]
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (P : α → Pattern) (hP : ∀ S : Finset α, (∑ j∈S, (P j).eval p) ≤ 1) :
    ∃ A : Set ℕ, (∀ L, PrefixBrackets p A L) ∧
      ∀ S : Finset α, (∑ j∈S, (P j).value (fun i ↦ decide (i∈A))) ≤ 1 := by
  let e := Denumerable.eqv α
  obtain ⟨A,hbr,hpat⟩ := exists_pattern_rounding p hp (fun n ↦ P (e.symm n)) (by
    intro S
    have hh := hP (S.image e.symm)
    rwa [Finset.sum_image e.symm.injective.injOn] at hh)
  refine ⟨A,hbr,?_⟩
  intro S
  have hh := hpat (S.image e)
  rw [Finset.sum_image e.injective.injOn] at hh
  simpa only [Equiv.symm_apply_apply] using hh

end Erdos66PurePatternBracketRounding
