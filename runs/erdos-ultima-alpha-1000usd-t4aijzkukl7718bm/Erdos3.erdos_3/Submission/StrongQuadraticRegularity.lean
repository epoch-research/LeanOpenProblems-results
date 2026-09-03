import Submission.AdaptiveStrongRegularity
import Submission.StableQuadraticRegularity

/-! An unconditional bounded strong U3 decomposition. The fine residual may
have an arbitrarily prescribed accuracy depending on the COARSE complexity;
the coarse/fine difference has a separately prescribed L2 bound. -/
namespace Erdos3StrongQuadraticRegularity
open Finset Erdos3AdaptiveStrongRegularity Erdos3ProjectedWeakRegularity
  Erdos3BoundedFeatureClasses Erdos3ClippedWeakRegularity
  Erdos3StableQuadraticRegularity Erdos3WeakQuadraticRegularity
  Erdos3NormalizedQuadraticInverse Erdos3FiniteUniformity
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

noncomputable def gainWeight (δ : ℝ) : NNReal := (regularityGain δ).toNNReal

lemma gainWeight_coe {δ : ℝ} (hδ : 0 < δ) : (gainWeight δ : ℝ) = regularityGain δ :=
  Real.coe_toNNReal _ (regularityGain_pos hδ).le

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The accuracy function delta and the stability function z are arbitrary
positive functions of the coarse complexity bound. Fine accuracy is not
required to be comparable to the coarse factor's complexity. -/
theorem strong_U3_regularity (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (δ : ℕ → ℝ) (hδ : ∀ m, 0 < δ m) (hδ1 : ∀ m, δ m ≤ 1)
    (z : ℕ → ℕ) (hz : ∀ m, 0 < z m) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ l : List (Feature G), ∃ g g' : G → ℝ,
      m ≤ complexityBudget (blockSize f (fun j ↦ gainWeight (δ j)))
        (⌈(𝔼 x : G, f x)/ε^2⌉₊+1) ∧ l.length ≤ m ∧
      (∀ p ∈ l, ∃ j < m, (p.1 : ℝ) = regularityGain (δ j) ∧
        IsStableQuadraticAverageTest (normalizedRank (δ j)) (z j) p.2) ∧
      IsFeatureMinimizer f l g ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ (∀ x, 0 ≤ g' x ∧ g' x ≤ 1) ∧
      uniformityPower 2 (fun x ↦ ((f x-g' x : ℝ) : ℂ)) ≤ δ m ∧
      squaredError g g' ≤ ε^2 := by
  let T : ℕ → Set (G → ℝ) := fun j ↦ {ψ | IsStableQuadraticAverageTest (normalizedRank (δ j)) (z j) ψ}
  let Good : ℕ → (G → ℝ) → Prop := fun j r ↦
    uniformityPower 2 (fun x ↦ (r x : ℂ)) ≤ δ j
  let ρ : ℕ → NNReal := fun j ↦ gainWeight (δ j)
  have hρ (j : ℕ) : 0 < (ρ j : ℝ) := by
    rw [show (ρ j : ℝ) = regularityGain (δ j) from gainWeight_coe (hδ j)]
    exact regularityGain_pos (hδ j)
  have hT (j : ℕ) (ψ : G → ℝ) (hψ : ψ ∈ T j) (x : G) : |ψ x| ≤ 1 :=
    stableQuadraticAverageTest_bound _ _ ψ hψ x
  have hdetect (j : ℕ) (r : G → ℝ) (hr : ∀ x, |r x| ≤ 1) (hnot : ¬ Good j r) :
      ∃ ψ ∈ T j, (ρ j : ℝ) ≤ 𝔼 x : G, r x*ψ x := by
    obtain ⟨ψ,hψ,hcorr⟩ := large_U3_stable_real_detector h2 r hr (hδ j)
      (le_of_lt (lt_of_not_ge hnot)) (hz j)
    refine ⟨ψ,hψ,?_⟩
    rw [show (ρ j : ℝ) = regularityGain (δ j) from gainWeight_coe (hδ j)]
    exact (regularityGain_le (hδ j) (hδ1 j)).trans hcorr
  obtain ⟨m,l,g,g',hm,hlen,hcert,hmin,hg',hU,hclose⟩ :=
    adaptive_strong_regularity_explicit T Good ρ hρ hT hdetect f hf hε
  refine ⟨m,l,g,g',hm,hlen,?_,hmin,hmin.1.1,hg',hU,hclose⟩
  intro p hp
  obtain ⟨j,hj,hweight,hψ⟩ := hcert p hp
  refine ⟨j,hj,?_,hψ⟩
  rw [hweight]
  exact gainWeight_coe (hδ j)

#print axioms strong_U3_regularity
end Erdos3StrongQuadraticRegularity
