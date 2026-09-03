import Submission.VariableSampleCoordinates
import Submission.CommonQuadraticWindow

/-! Local quadratic-factor representation for weighted features with different
stability tolerances and different sample counts. All errors retain their
individual weights; the same common window works for every base point. -/
namespace Erdos3WeightedLocalQuadraticFactor
open Finset Erdos3VariableSampleCoordinates Erdos3WeightedFeatureErrors
  Erdos3FeatureLipschitzEnvelope Erdos3CommonQuadraticWindow
  Erdos3RelativeStableBohr Erdos3FiniteBohr Erdos3StableQuadraticRegularity
  Erdos3SampledQuadraticAverage Erdos3LocalQuadraticInverse
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000

lemma windowDenominator_mono_tolerance (R : ℕ) {z Z : ℕ} (hz : z ≤ Z) :
    windowDenominator R z ≤ windowDenominator R Z := by
  unfold windowDenominator
  gcongr

lemma commonWidth_antitone_tolerance (R : ℕ) {z Z : ℕ} (hz : 0 < z) (hzZ : z ≤ Z) :
    commonWidth R Z ≤ commonWidth R z := by
  unfold commonWidth
  apply div_le_div_of_nonneg_left (by norm_num)
    (by exact_mod_cast windowDenominator_pos R hz)
  exact_mod_cast windowDenominator_mono_tolerance R hzZ

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {I : Type*} [Fintype I]

lemma mixed_window_subset (D : I → Finset (AddChar G ℂ)) (r : I → ℝ)
    (z : I → ℕ) {R Z : ℕ} (hD : ∀ i, (D i).card ≤ R)
    (hz : ∀ i, 0 < z i) (hzZ : ∀ i, z i ≤ Z) (hr : ∀ i, 1/64 ≤ r i) (i : I) :
    bohr (commonCharacters D) (commonWidth R Z) ⊆ bohr (D i) (relativeWidth (D i) (z i) (r i)) := by
  intro x hx
  apply mem_bohr.mpr
  intro χ hχ
  have hm : χ ∈ commonCharacters D := mem_biUnion.mpr ⟨i,mem_univ _,hχ⟩
  exact (mem_bohr.mp hx χ hm).trans
    ((commonWidth_antitone_tolerance R (hz i) (hzZ i)).trans
      (commonWidth_le_relative (D i) (hD i) (hz i) (hr i)))

/-- The local phase count is sum_i M_i, the Lipschitz constant is sum_i w_i,
and the normalized mean-square error is (sum_i w_i*epsilon_i)^2. -/
theorem weighted_stable_factor_local (ψ : I → G → ℝ) (R₀ z M : I → ℕ)
    (hz : ∀ i, 0 < z i) (hM : ∀ i, 0 < M i)
    (hψ : ∀ i, IsStableQuadraticAverageTest (R₀ i) (z i) (ψ i))
    {R Z : ℕ} (hR : ∀ i, R₀ i ≤ R) (hZ : 0 < Z) (hzZ : ∀ i, z i ≤ Z)
    (w : I → NNReal) (Φ : (I → ℝ) → ℝ)
    (hΦ : ∀ v, 0 ≤ Φ v ∧ Φ v ≤ 1)
    (hΦlip : ∀ v u, |Φ v-Φ u| ≤ weightedDistance w v u)
    (ε : I → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (hbudget : ∀ i, 2/(z i : ℝ)^2+2/(M i : ℝ) ≤ (ε i)^2) :
    ∃ C : Finset (AddChar G ℂ), C.card ≤ Fintype.card I*R ∧
      Fintype.card G ≤ (256*windowDenominator R Z+1)^(2*(Fintype.card I*R))*
        (bohr C (commonWidth R Z)).card ∧
      ∀ W : Finset G, W.Nonempty → W ⊆ bohr C (commonWidth R Z) →
      ∀ a : G, ∃ H : ((Σ i : I, Fin (M i)) → ℂ) → ℝ,
        ∃ Q : (Σ i : I, Fin (M i)) → G → ℂ,
          (∀ v, 0 ≤ H v ∧ H v ≤ 1) ∧ LipschitzWith (∑ i : I, w i) H ∧
          (∀ p t, ‖Q p t‖ = 1) ∧ (∀ p, IsLocallyQuadratic (W : Set G) (Q p)) ∧
          (𝔼 t : W, (Φ (fun i ↦ ψ i (a+t))-H (fun p ↦ Q p t))^2) ≤
            (∑ i : I, (w i : ℝ)*ε i)^2 := by
  choose D r q b hD hr hrmax hstable hq hquad hb heq using hψ
  have hDR (i : I) : (D i).card ≤ R := (hD i).trans (hR i)
  let C := commonCharacters D
  refine ⟨C,commonCharacters_card D hDR,common_window_card_bound D hDR hZ,?_⟩
  intro W hW hWsub a
  have hsub (i : I) : W ⊆ bohr (D i) (relativeWidth (D i) (z i) (r i)) :=
    hWsub.trans (mixed_window_subset D r z hDR hz hzZ hr i)
  have hs (i : I) := stable_average_local_factor (D i)
    (show 0 < r i by linarith [hr i]) (hrmax i) (hz i) (hstable i) W hW (hsub i)
    (q i) (hq i) (hquad i) (b i) (hb i) a (hM i)
  choose c Q hc hunit hpoly herr using hs
  refine ⟨sampledFactor M c Φ,fun p ↦ Q p.1 p.2,
    sampledFactor_bounds M c Φ hΦ,sampledFactor_lipschitz M hM c hc w Φ hΦlip,
    fun p t ↦ hunit p.1 p.2 t,fun p ↦ hpoly p.1 p.2,?_⟩
  have he (i : I) :
      (𝔼 t : W, (ψ i (a+t)-(𝔼 j : Fin (M i), (c i j*conj (Q i j t)).re))^2) ≤ (ε i)^2 := by
    rw [heq i]
    exact (herr i).trans (hbudget i)
  exact weighted_factor_mean_square w Φ hΦlip (fun i (t : W) ↦ ψ i (a+t))
    (fun i (t : W) ↦ 𝔼 j : Fin (M i), (c i j*conj (Q i j t)).re) ε hε he

#print axioms mixed_window_subset
#print axioms weighted_stable_factor_local
end Erdos3WeightedLocalQuadraticFactor
