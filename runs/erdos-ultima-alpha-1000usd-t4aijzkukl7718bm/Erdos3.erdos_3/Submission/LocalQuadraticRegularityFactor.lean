import Submission.CommonQuadraticWindow
import Submission.SampledClippedFactor

/-! Local polynomial-factor representation of the bounded weak-U3 approximant.
The global U3 residual and the local mean-square approximation are distinct
conclusions; no unproved transfer of uniformity to a small window is used. -/
namespace Erdos3LocalQuadraticRegularityFactor
open Finset Erdos3FiniteBohr Erdos3RelativeStableBohr Erdos3CommonQuadraticWindow
  Erdos3StableQuadraticRegularity Erdos3ClippedWeakRegularity
  Erdos3SampledClippedFactor Erdos3ClippedSumPerturbation
  Erdos3SampledQuadraticAverage Erdos3LocalQuadraticInverse
  Erdos3QuadraticAverageDetectors Erdos3WeakQuadraticRegularity
  Erdos3FiniteUniformity Erdos3NormalizedQuadraticInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A list of stable tests can be represented on one common window by a bounded
Lipschitz factor of T*M unit locally quadratic phases, with explicit error. -/
theorem stable_test_list_local_factor_on_subwindows (l : List (G → ℝ)) {R z : ℕ} (hz : 0 < z)
    (hl : ∀ ψ ∈ l, IsStableQuadraticAverageTest R z ψ)
    (ρ : ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ C : Finset (AddChar G ℂ), C.card ≤ l.length*R ∧
      Fintype.card G ≤ (256*windowDenominator R z+1)^(2*(l.length*R))*
        (bohr C (commonWidth R z)).card ∧
      ∀ W : Finset G, W.Nonempty → W ⊆ bohr C (commonWidth R z) →
      ∀ a : G, ∃ Φ : (Fin l.length × Fin M → ℂ) → ℝ,
        ∃ Q : (Fin l.length × Fin M) → G → ℂ,
          (∀ v, 0 ≤ Φ v ∧ Φ v ≤ 1) ∧
          LipschitzWith (⟨|ρ|,abs_nonneg ρ⟩*(l.length : NNReal)) Φ ∧
          (∀ p t, ‖Q p t‖ = 1) ∧
          (∀ p, IsLocallyQuadratic (W : Set G) (Q p)) ∧
          (𝔼 t : W,
            (clippedSum ρ l (a+t)-Φ (fun p ↦ Q p t))^2) ≤
            ρ^2*(l.length : ℝ)^2*(2/(z : ℝ)^2+2/(M : ℝ)) := by
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  have htests (i : Fin l.length) : IsStableQuadraticAverageTest R z (l.get i) :=
    hl _ (List.get_mem _ _)
  choose D r q b hD hr hrmax hstable hq hquad hb hψ using htests
  let C := commonCharacters D
  refine ⟨C,?_,?_,?_⟩
  · simpa only [Fintype.card_fin] using commonCharacters_card D hD
  · simpa only [Fintype.card_fin] using common_window_card_bound D hD hz
  intro W hW hWsub a
  have hsub (i : Fin l.length) : W ⊆ bohr (D i) (relativeWidth (D i) z (r i)) :=
    hWsub.trans (common_window_subset D r hD hz hr i)
  have hs (i : Fin l.length) := stable_average_local_factor (D i)
    (show 0 < r i by linarith [hr i]) (hrmax i) hz (hstable i) W hW (hsub i)
    (q i) (hq i) (hquad i) (b i) (hb i) a hM
  choose c Q hc hunit hquadW he using hs
  let L : List (Fin l.length) := List.ofFn (fun i ↦ i)
  have hL : L.length = l.length := List.length_ofFn
  have hlmap : L.map l.get = l := by
    dsimp only [L]
    rw [List.map_ofFn]
    exact List.ofFn_get l
  refine ⟨clippedFactor L ρ c,fun p ↦ Q p.1 p.2,
    clippedFactor_bounds L ρ c,?_,fun p t ↦ hunit p.1 p.2 t,
    fun p ↦ hquadW p.1 p.2,?_⟩
  · simpa only [hL] using clippedFactor_lipschitz L ρ c hc
  have herr := clippedSum_mean_sq_sub L ρ
    (fun i (t : W) ↦ l.get i (a+t))
    (fun i (t : W) ↦ 𝔼 j : Fin M, (c i j*conj (Q i j t)).re)
    (ε := 2/(z : ℝ)^2+2/(M : ℝ)) (fun i _ ↦ by dsimp only; rw [hψ i]; exact he i)
  have he₁ (t : W) :
      clippedSum ρ (L.map (fun i (t : W) ↦ l.get i (a+t))) t = clippedSum ρ l (a+t) := by
    have hh := clippedSum_comp (L.map l.get) ρ (fun t : W ↦ a+(t : G)) t
    rw [List.map_map] at hh
    rw [hlmap] at hh
    exact hh
  have he₂ (t : W) :
      clippedSum ρ (L.map (fun i (t : W) ↦ 𝔼 j : Fin M, (c i j*conj (Q i j t)).re)) t =
        clippedFactor L ρ c (fun p ↦ Q p.1 p.2 t) :=
    (clippedFactor_evaluate L ρ c (fun p (t : W) ↦ Q p.1 p.2 t) t).symm
  simp only [he₁,he₂,hL] at herr
  exact herr

theorem stable_test_list_local_factor (l : List (G → ℝ)) {R z : ℕ} (hz : 0 < z)
    (hl : ∀ ψ ∈ l, IsStableQuadraticAverageTest R z ψ)
    (ρ : ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ C : Finset (AddChar G ℂ), C.card ≤ l.length*R ∧
      Fintype.card G ≤ (256*windowDenominator R z+1)^(2*(l.length*R))*
        (bohr C (commonWidth R z)).card ∧
      ∀ a : G, ∃ Φ : (Fin l.length × Fin M → ℂ) → ℝ,
        ∃ Q : (Fin l.length × Fin M) → G → ℂ,
          (∀ v, 0 ≤ Φ v ∧ Φ v ≤ 1) ∧
          LipschitzWith (⟨|ρ|,abs_nonneg ρ⟩*(l.length : NNReal)) Φ ∧
          (∀ p t, ‖Q p t‖ = 1) ∧
          (∀ p, IsLocallyQuadratic (bohr C (commonWidth R z) : Set G) (Q p)) ∧
          (𝔼 t : bohr C (commonWidth R z),
            (clippedSum ρ l (a+t)-Φ (fun p ↦ Q p t))^2) ≤
            ρ^2*(l.length : ℝ)^2*(2/(z : ℝ)^2+2/(M : ℝ)) := by
  obtain ⟨C,hC,hcard,hlocal⟩ := stable_test_list_local_factor_on_subwindows l hz hl ρ hM
  exact ⟨C,hC,hcard,hlocal (bohr C (commonWidth R z))
    ⟨0,bohr_zero C (commonWidth_pos R hz).le⟩ (Subset.refl _)⟩

/-- Unconditional weak U3 regularity together with finite local quadratic
factor representations of the bounded approximant at every base point. -/
theorem weak_U3_local_factor (h2 : Function.Bijective (fun x : G ↦ x+x))
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {z : ℕ} (hz : 0 < z)
    {M : ℕ} (hM : 0 < M) :
    ∃ T : ℕ, ∃ g : G → ℝ, ∃ C : Finset (AddChar G ℂ),
      T ≤ ⌈(𝔼 x : G, f x)/(regularityGain δ)^2⌉₊+1 ∧
      C.card ≤ T*normalizedRank δ ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      uniformityPower 2 (fun x ↦ ((f x-g x : ℝ) : ℂ)) ≤ δ ∧
      Fintype.card G ≤ (256*windowDenominator (normalizedRank δ) z+1)^(2*(T*normalizedRank δ))*
        (bohr C (commonWidth (normalizedRank δ) z)).card ∧
      ∀ a : G, ∃ Φ : (Fin T × Fin M → ℂ) → ℝ,
        ∃ Q : (Fin T × Fin M) → G → ℂ,
          (∀ v, 0 ≤ Φ v ∧ Φ v ≤ 1) ∧
          LipschitzWith (⟨|regularityGain δ|,abs_nonneg _⟩*(T : NNReal)) Φ ∧
          (∀ p t, ‖Q p t‖ = 1) ∧
          (∀ p, IsLocallyQuadratic (bohr C (commonWidth (normalizedRank δ) z) : Set G) (Q p)) ∧
          (𝔼 t : bohr C (commonWidth (normalizedRank δ) z),
            (g (a+t)-Φ (fun p ↦ Q p t))^2) ≤
            (regularityGain δ)^2*(T : ℝ)^2*(2/(z : ℝ)^2+2/(M : ℝ)) := by
  obtain ⟨l,hlen,hl,hU⟩ := stable_weak_U3_regularity h2 f hf hδ hδ1 hz
  obtain ⟨C,hC,hcard,hlocal⟩ := stable_test_list_local_factor l hz hl (regularityGain δ) hM
  exact ⟨l.length,clippedSum (regularityGain δ) l,C,hlen,hC,
    clippedSum_bounds _ _,hU,hcard,hlocal⟩

#print axioms stable_test_list_local_factor_on_subwindows
#print axioms stable_test_list_local_factor
#print axioms weak_U3_local_factor
end Erdos3LocalQuadraticRegularityFactor
