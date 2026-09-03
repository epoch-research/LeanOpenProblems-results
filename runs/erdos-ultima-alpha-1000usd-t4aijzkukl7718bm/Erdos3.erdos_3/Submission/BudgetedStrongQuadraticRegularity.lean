import Submission.SummableStageBudgets
import Submission.StrongQuadraticRegularity

/-! Unconditional strong U3 regularity with a proved weighted localization
budget. Stage tolerances are chosen before running the decomposition and do
not depend on the eventual coarse complexity. -/
namespace Erdos3BudgetedStrongQuadraticRegularity
open Finset Erdos3SummableStageBudgets Erdos3BudgetedStrongRegularity
  Erdos3AdaptiveStrongRegularity Erdos3StrongQuadraticRegularity
  Erdos3BoundedFeatureClasses Erdos3ProjectedWeakRegularity Erdos3ClippedWeakRegularity
  Erdos3StableQuadraticRegularity Erdos3WeakQuadraticRegularity
  Erdos3NormalizedQuadraticInverse Erdos3FiniteUniformity
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The sum over all coarse features of weight/stability-tolerance is <=tau/2.
The strict provenance indices remain below the current fine-accuracy index m. -/
theorem budgeted_strong_U3_regularity (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδ1 : ∀ j, δ j ≤ 1)
    {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    let ρ := fun j ↦ gainWeight (δ j)
    let z := stageTolerance ρ τ
    ∃ m : ℕ, ∃ t : List (TaggedTest G), ∃ g g' : G → ℝ,
      m ≤ complexityBudget (blockSize f ρ) (⌈(𝔼 x : G, f x)/ε^2⌉₊+1) ∧ t.length ≤ m ∧
      (∀ p ∈ t, p.1 < m ∧ IsStableQuadraticAverageTest (normalizedRank (δ p.1)) (z p.1) p.2) ∧
      tagCost (fun j ↦ (ρ j : ℝ)/(z j : ℝ)) t ≤ τ/2 ∧
      IsFeatureMinimizer f (taggedFeatures ρ t) g ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ (∀ x, 0 ≤ g' x ∧ g' x ≤ 1) ∧
      uniformityPower 2 (fun x ↦ ((f x-g' x : ℝ) : ℂ)) ≤ δ m ∧ squaredError g g' ≤ ε^2 := by
  dsimp only
  let ρ : ℕ → NNReal := fun j ↦ gainWeight (δ j)
  let z := stageTolerance ρ τ
  let T : ℕ → Set (G → ℝ) := fun j ↦ {ψ | IsStableQuadraticAverageTest (normalizedRank (δ j)) (z j) ψ}
  let Good : ℕ → (G → ℝ) → Prop := fun j r ↦ uniformityPower 2 (fun x ↦ (r x : ℂ)) ≤ δ j
  have hρ (j : ℕ) : 0 < (ρ j : ℝ) := by
    rw [show (ρ j : ℝ) = regularityGain (δ j) from gainWeight_coe (hδ j)]
    exact regularityGain_pos (hδ j)
  have hT (j : ℕ) (ψ : G → ℝ) (hψ : ψ ∈ T j) (x : G) : |ψ x| ≤ 1 :=
    stableQuadraticAverageTest_bound _ _ ψ hψ x
  have hdetect (j : ℕ) (r : G → ℝ) (hr : ∀ x, |r x| ≤ 1) (hnot : ¬ Good j r) :
      ∃ ψ ∈ T j, (ρ j : ℝ) ≤ 𝔼 x : G, r x*ψ x := by
    obtain ⟨ψ,hψ,hcorr⟩ := large_U3_stable_real_detector h2 r hr (hδ j)
      (le_of_lt (lt_of_not_ge hnot)) (stageTolerance_pos ρ τ j)
    refine ⟨ψ,hψ,?_⟩
    rw [show (ρ j : ℝ) = regularityGain (δ j) from gainWeight_coe (hδ j)]
    exact (regularityGain_le (hδ j) (hδ1 j)).trans hcorr
  have hN : (𝔼 x : G, f x)/ε^2 < ((⌈(𝔼 x : G, f x)/ε^2⌉₊+1 : ℕ) : ℝ) := by
    apply (Nat.le_ceil _).trans_lt
    rw [Nat.cast_add,Nat.cast_one]
    linarith
  obtain ⟨m,t,g,g',hm,hlen,htag,hcost,hmin,hg',hU,hclose⟩ :=
    budgeted_strong_regularity T Good ρ hρ hT hdetect f hf
      (fun j ↦ (ρ j : ℝ)/(z j : ℝ)) (fun _ ↦ by positivity) hε hN
  exact ⟨m,t,g,g',hm,hlen,htag,
    hcost.trans (prefix_stage_budget f (fun x ↦ (hf x).2) ρ hτ m),hmin,hmin.1.1,hg',hU,hclose⟩

#print axioms budgeted_strong_U3_regularity
end Erdos3BudgetedStrongQuadraticRegularity
