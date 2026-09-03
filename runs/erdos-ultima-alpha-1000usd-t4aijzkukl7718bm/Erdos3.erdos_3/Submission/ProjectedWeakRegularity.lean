import Submission.BoundedFeatureClasses

/-! Weak regularity by least-squares projections onto nested bounded feature
classes. It can refine an existing approximation and retains Pythagorean
control, which will permit a coarse/fine energy pigeonhole argument. -/
namespace Erdos3ProjectedWeakRegularity
open Finset Erdos3ClippedWeakRegularity Erdos3ConvexLeastSquares Erdos3BoundedFeatureClasses
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

variable {X : Type*} [Fintype X] [Nonempty X]

def IsFeatureMinimizer (f : X → ℝ) (l : List (Feature X)) (g : X → ℝ) : Prop :=
  g ∈ featureClass l ∧ ∀ h ∈ featureClass l, squaredError f g ≤ squaredError f h

noncomputable def extendFeatures (ρ : NNReal) (u : List (X → ℝ)) (l : List (Feature X)) :
    List (Feature X) := u.map (fun ψ ↦ (ρ,ψ))++l

lemma feature_residual_bound (f g : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {l : List (Feature X)} (hg : g ∈ featureClass l) (x : X) : |f x-g x| ≤ 1 :=
  abs_le.mpr ⟨by linarith [(hf x).1,(hg.1 x).2],by linarith [(hf x).2,(hg.1 x).1]⟩

lemma projected_regularize_or_energy (T : Set (X → ℝ)) (Good : (X → ℝ) → Prop)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (ρ : NNReal)
    (hT : ∀ ψ ∈ T, ∀ x, |ψ x| ≤ 1)
    (hdetect : ∀ r : X → ℝ, (∀ x, |r x| ≤ 1) → ¬ Good r →
      ∃ ψ ∈ T, (ρ : ℝ) ≤ 𝔼 x : X, r x*ψ x)
    (l₀ : List (Feature X)) (g₀ : X → ℝ) (hg₀ : IsFeatureMinimizer f l₀ g₀) (N : ℕ) :
    (∃ u : List (X → ℝ), ∃ g : X → ℝ, u.length ≤ N ∧ (∀ ψ ∈ u, ψ ∈ T) ∧
      IsFeatureMinimizer f (extendFeatures ρ u l₀) g ∧ Good (fun x ↦ f x-g x)) ∨
    (∃ u : List (X → ℝ), ∃ g : X → ℝ, u.length = N ∧ (∀ ψ ∈ u, ψ ∈ T) ∧
      IsFeatureMinimizer f (extendFeatures ρ u l₀) g ∧
      squaredError f g+(N : ℝ)*(ρ : ℝ)^2 ≤ squaredError f g₀) := by
  induction N with
  | zero =>
    right
    refine ⟨[],g₀,rfl,by simp,hg₀,?_⟩
    simp
  | succ N ih =>
    rcases ih with ⟨u,g,hlen,hu,hmin,hgood⟩ | ⟨u,g,hlen,hu,hmin,henergy⟩
    · exact Or.inl ⟨u,g,by omega,hu,hmin,hgood⟩
    · by_cases hgood : Good (fun x ↦ f x-g x)
      · exact Or.inl ⟨u,g,by omega,hu,hmin,hgood⟩
      · obtain ⟨ψ,hψ,hcorr⟩ := hdetect _ (feature_residual_bound f g hf hmin.1) hgood
        obtain ⟨g',hg',hmin',hdrop,_⟩ := projected_test_step f hf
          (extendFeatures ρ u l₀) g hmin.1 ψ (hT ψ hψ) ρ hcorr
        right
        refine ⟨ψ::u,g',by simp [hlen],?_,⟨hg',hmin'⟩,?_⟩
        · intro φ hφ
          rcases List.mem_cons.mp hφ with rfl | hφ
          · exact hψ
          · exact hu φ hφ
        · rw [Nat.cast_add,Nat.cast_one]
          linarith

/-- Refinement reaches any supplied residual predicate using polynomially many
new detecting tests. The existing features are preserved as a suffix. -/
theorem projected_weak_refinement (T : Set (X → ℝ)) (Good : (X → ℝ) → Prop)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (ρ : NNReal) (hρ : 0 < (ρ : ℝ))
    (hT : ∀ ψ ∈ T, ∀ x, |ψ x| ≤ 1)
    (hdetect : ∀ r : X → ℝ, (∀ x, |r x| ≤ 1) → ¬ Good r →
      ∃ ψ ∈ T, (ρ : ℝ) ≤ 𝔼 x : X, r x*ψ x)
    (l₀ : List (Feature X)) (g₀ : X → ℝ) (hg₀ : IsFeatureMinimizer f l₀ g₀) :
    ∃ u : List (X → ℝ), ∃ g : X → ℝ,
      u.length ≤ ⌈(𝔼 x : X, f x)/(ρ : ℝ)^2⌉₊+1 ∧ (∀ ψ ∈ u, ψ ∈ T) ∧
      IsFeatureMinimizer f (extendFeatures ρ u l₀) g ∧ Good (fun x ↦ f x-g x) ∧
      squaredError g₀ g ≤ squaredError f g₀-squaredError f g := by
  let N := ⌈(𝔼 x : X, f x)/(ρ : ℝ)^2⌉₊+1
  have hgood : ∃ u : List (X → ℝ), ∃ g : X → ℝ,
      u.length ≤ N ∧ (∀ ψ ∈ u, ψ ∈ T) ∧
      IsFeatureMinimizer f (extendFeatures ρ u l₀) g ∧ Good (fun x ↦ f x-g x) := by
    rcases projected_regularize_or_energy T Good f hf ρ hT hdetect l₀ g₀ hg₀ N with
      h | ⟨u,g,_,_,_,he⟩
    · exact h
    · have hN : (𝔼 x : X, f x)/(ρ : ℝ)^2 < (N : ℝ) := by
        apply (Nat.le_ceil _).trans_lt
        dsimp only [N]
        rw [Nat.cast_add,Nat.cast_one]
        linarith
      have hh := (div_lt_iff₀ (sq_pos_of_pos hρ)).mp hN
      have h0 := squaredError_nonneg f g
      have hf0 := (hg₀.2 0 (featureClass_zero l₀)).trans (squaredError_zero_le_mean f hf)
      exfalso
      linarith
  obtain ⟨u,g,hlen,hu,hmin,hgood⟩ := hgood
  refine ⟨u,g,hlen,hu,hmin,hgood,?_⟩
  exact nested_minimizers_close f g₀ g (featureClass_append l₀ _) (featureClass_convex _)
    hg₀.1 hmin.1 hmin.2

#print axioms projected_weak_refinement
end Erdos3ProjectedWeakRegularity
