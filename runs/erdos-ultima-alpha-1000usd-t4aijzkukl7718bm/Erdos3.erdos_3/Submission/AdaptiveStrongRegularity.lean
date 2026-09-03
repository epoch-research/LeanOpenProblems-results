import Submission.ProjectedWeakRegularity

/-! Coarse/fine strong regularity from bounded correlation detectors. Fine
accuracy may depend arbitrarily on the preceding complexity bound. The small
L2 error is obtained by an energy pigeonhole, not by assuming the two weak
approximants are close. -/
namespace Erdos3AdaptiveStrongRegularity
open Finset Erdos3ClippedWeakRegularity Erdos3ConvexLeastSquares
  Erdos3BoundedFeatureClasses Erdos3ProjectedWeakRegularity
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

noncomputable def complexityBudget (B : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => complexityBudget B n+B (complexityBudget B n)

lemma complexityBudget_mono (B : ℕ → ℕ) : Monotone (complexityBudget B) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Nat.le_add_right _ _

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def blockSize (f : X → ℝ) (ρ : ℕ → NNReal) (m : ℕ) : ℕ :=
  ⌈(𝔼 x : X, f x)/(ρ m : ℝ)^2⌉₊+1

def FeatureCertificate (T : ℕ → Set (X → ℝ)) (ρ : ℕ → NNReal)
    (m : ℕ) (l : List (Feature X)) : Prop :=
  ∀ p ∈ l, ∃ j < m, p.1 = ρ j ∧ p.2 ∈ T j

/-- The structured approximation has complexity m; the fine residual satisfies
Good(m), however small that accuracy is. The intervening error has L2 norm at
most epsilon. Only the coarse complexity is fed to Good. -/
theorem adaptive_strong_regularity (T : ℕ → Set (X → ℝ))
    (Good : ℕ → (X → ℝ) → Prop) (ρ : ℕ → NNReal)
    (hρ : ∀ m, 0 < (ρ m : ℝ))
    (hT : ∀ m ψ, ψ ∈ T m → ∀ x, |ψ x| ≤ 1)
    (hdetect : ∀ m, ∀ r : X → ℝ, (∀ x, |r x| ≤ 1) → ¬ Good m r →
      ∃ ψ ∈ T m, (ρ m : ℝ) ≤ 𝔼 x : X, r x*ψ x)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : (𝔼 x : X, f x)/ε^2 < (N : ℝ)) :
    ∃ m : ℕ, ∃ l : List (Feature X), ∃ g g' : X → ℝ,
      m ≤ complexityBudget (blockSize f ρ) N ∧ l.length ≤ m ∧
      FeatureCertificate T ρ m l ∧ IsFeatureMinimizer f l g ∧
      (∀ x, 0 ≤ g' x ∧ g' x ≤ 1) ∧
      Good m (fun x ↦ f x-g' x) ∧ squaredError g g' ≤ ε^2 := by
  let M : ℕ → ℕ := complexityBudget (blockSize f ρ)
  let State (n : ℕ) := {p : List (Feature X) × (X → ℝ) //
    IsFeatureMinimizer f p.1 p.2 ∧ p.1.length ≤ M n ∧ FeatureCertificate T ρ (M n) p.1}
  obtain ⟨g₀,hg₀,hmin₀⟩ := exists_feature_minimizer f ([] : List (Feature X))
  let s₀ : State 0 := ⟨([],g₀),⟨hg₀,hmin₀⟩,le_refl 0,by simp [FeatureCertificate]⟩
  have hnext (n : ℕ) (s : State n) : ∃ s' : State (n+1),
      Good (M n) (fun x ↦ f x-s'.val.2 x) ∧
      squaredError s.val.2 s'.val.2 ≤ squaredError f s.val.2-squaredError f s'.val.2 := by
    obtain ⟨u,g,hlen,hu,hmin,hgood,hclose⟩ := projected_weak_refinement
      (T (M n)) (Good (M n)) f hf (ρ (M n)) (hρ (M n))
      (hT (M n)) (hdetect (M n)) s.val.1 s.val.2 s.property.1
    have hMM : M n ≤ M (n+1) := complexityBudget_mono _ (Nat.le_succ n)
    have hMMlt : M n < M (n+1) := by
      change M n < M n+blockSize f ρ (M n)
      unfold blockSize
      omega
    have hlen' : (extendFeatures (ρ (M n)) u s.val.1).length ≤ M (n+1) := by
      change _ ≤ M n+blockSize f ρ (M n)
      simp only [extendFeatures,List.length_append,List.length_map]
      have hs := s.property.2.1
      change u.length ≤ blockSize f ρ (M n) at hlen
      omega
    have hcert : FeatureCertificate T ρ (M (n+1)) (extendFeatures (ρ (M n)) u s.val.1) := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp hp
        exact ⟨M n,hMMlt,rfl,hu ψ hψ⟩
      · obtain ⟨j,hj,hweight,hψ⟩ := s.property.2.2 p hp
        exact ⟨j,hj.trans_le hMM,hweight,hψ⟩
    exact ⟨⟨(extendFeatures (ρ (M n)) u s.val.1,g),hmin,hlen',hcert⟩,hgood,hclose⟩
  choose next hnextGood hnextClose using hnext
  let state : (n : ℕ) → State n := fun n ↦ Nat.rec s₀ (fun n s ↦ next n s) n
  let g : ℕ → X → ℝ := fun n ↦ (state n).val.2
  have hstep (n : ℕ) : squaredError (g n) (g (n+1)) ≤ squaredError f (g n)-squaredError f (g (n+1)) :=
    hnextClose n (state n)
  have hinit : squaredError f (g 0) ≤ squaredError f 0 := hmin₀ 0 (featureClass_zero [])
  obtain ⟨i,hi,hsmall⟩ := exists_small_nested_step f g hf hinit hε hN (fun n _ ↦ hstep n)
  refine ⟨M i,(state i).val.1,g i,g (i+1),complexityBudget_mono _ hi.le,
    (state i).property.2.1,(state i).property.2.2,(state i).property.1,?_,?_,hsmall⟩
  · exact (state (i+1)).property.1.1.1
  · exact hnextGood i (state i)

/-- A fixed explicit number of outer stages suffices. Its bound is independent
of the requested fine-accuracy function. -/
theorem adaptive_strong_regularity_explicit (T : ℕ → Set (X → ℝ))
    (Good : ℕ → (X → ℝ) → Prop) (ρ : ℕ → NNReal)
    (hρ : ∀ m, 0 < (ρ m : ℝ))
    (hT : ∀ m ψ, ψ ∈ T m → ∀ x, |ψ x| ≤ 1)
    (hdetect : ∀ m, ∀ r : X → ℝ, (∀ x, |r x| ≤ 1) → ¬ Good m r →
      ∃ ψ ∈ T m, (ρ m : ℝ) ≤ 𝔼 x : X, r x*ψ x)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ l : List (Feature X), ∃ g g' : X → ℝ,
      m ≤ complexityBudget (blockSize f ρ) (⌈(𝔼 x : X, f x)/ε^2⌉₊+1) ∧ l.length ≤ m ∧
      FeatureCertificate T ρ m l ∧ IsFeatureMinimizer f l g ∧
      (∀ x, 0 ≤ g' x ∧ g' x ≤ 1) ∧
      Good m (fun x ↦ f x-g' x) ∧ squaredError g g' ≤ ε^2 := by
  apply adaptive_strong_regularity T Good ρ hρ hT hdetect f hf hε
  apply (Nat.le_ceil _).trans_lt
  rw [Nat.cast_add,Nat.cast_one]
  linarith

#print axioms adaptive_strong_regularity
#print axioms adaptive_strong_regularity_explicit
end Erdos3AdaptiveStrongRegularity
