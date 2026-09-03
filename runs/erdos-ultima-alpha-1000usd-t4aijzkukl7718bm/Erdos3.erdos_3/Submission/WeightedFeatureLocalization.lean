import Submission.WeightedLocalQuadraticFactor
import Submission.StableLocalQuadraticFactor

/-! Local phase factors for the bounded convex feature classes used in strong
regularity. Taking z_i^2 samples in coordinate i gives error <=2/z_i. Thus a
weighted stability budget, rather than the final feature count, controls the
local mean-square approximation. -/
namespace Erdos3WeightedFeatureLocalization
open Finset Erdos3WeightedLocalQuadraticFactor Erdos3FeatureLipschitzEnvelope
  Erdos3BoundedFeatureClasses Erdos3CommonQuadraticWindow
  Erdos3StableLocalQuadraticFactor Erdos3RelativeStableBohr
  Erdos3StableQuadraticRegularity Erdos3FiniteBohr Erdos3BohrCovering
  Erdos3LocalQuadraticInverse
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

lemma square_sample_budget (z : ℕ) :
    2/(z : ℝ)^2+2/((z^2 : ℕ) : ℝ) = (2/(z : ℝ))^2 := by
  push_cast
  ring

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Local representation on every nonempty subwindow, with a prescribed total
error tau and a separate stability/sample budget for each weighted feature. -/
theorem weighted_class_local_factor (l : List (Feature G)) (g : G → ℝ)
    (hg : g ∈ featureClass l) (R₀ z : Fin l.length → ℕ)
    (hz : ∀ i, 0 < z i)
    (htest : ∀ i, IsStableQuadraticAverageTest (R₀ i) (z i) (l.get i).2)
    {R Z : ℕ} (hR : ∀ i, R₀ i ≤ R) (hZ : 0 < Z) (hzZ : ∀ i, z i ≤ Z)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hbudget : (∑ i : Fin l.length, ((l.get i).1 : ℝ)/(z i : ℝ)) ≤ τ/2) :
    ∃ C : Finset (AddChar G ℂ), C.card ≤ l.length*R ∧
      Fintype.card G ≤ (256*windowDenominator R Z+1)^(2*(l.length*R))*
        (bohr C (commonWidth R Z)).card ∧
      ∀ W : Finset G, W.Nonempty → W ⊆ bohr C (commonWidth R Z) →
      ∀ a : G, ∃ H : ((Σ i : Fin l.length, Fin ((z i)^2)) → ℂ) → ℝ,
        ∃ Q : (Σ i : Fin l.length, Fin ((z i)^2)) → G → ℂ,
          (∀ v, 0 ≤ H v ∧ H v ≤ 1) ∧
          LipschitzWith (∑ i : Fin l.length, (l.get i).1) H ∧
          (∀ p t, ‖Q p t‖ = 1) ∧ (∀ p, IsLocallyQuadratic (W : Set G) (Q p)) ∧
          (𝔼 t : W, (g (a+t)-H (fun p ↦ Q p t))^2) ≤ τ^2 := by
  obtain ⟨Φ,hΦ,hΦLip,hΦweighted,hrep⟩ := featureClass_factor hg
  obtain ⟨C,hC,hcard,hlocal⟩ := weighted_stable_factor_local
    (fun i ↦ (l.get i).2) R₀ z (fun i ↦ (z i)^2) hz
    (fun i ↦ pow_pos (hz i) 2) htest hR hZ hzZ
    (fun i ↦ (l.get i).1) Φ hΦ hΦweighted (fun i ↦ 2/(z i : ℝ))
    (fun i ↦ by positivity) (fun i ↦ (square_sample_budget (z i)).le)
  refine ⟨C,by simpa only [Fintype.card_fin] using hC,
    by simpa only [Fintype.card_fin] using hcard,?_⟩
  intro W hW hWsub a
  obtain ⟨H,Q,hH,hHLip,hQ,hpoly,herr⟩ := hlocal W hW hWsub a
  refine ⟨H,Q,hH,hHLip,hQ,hpoly,?_⟩
  simp only [hrep] at herr
  apply herr.trans
  have he : (∑ i : Fin l.length, ((l.get i).1 : ℝ)*(2/(z i : ℝ))) =
      2*(∑ i : Fin l.length, ((l.get i).1 : ℝ)/(z i : ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  apply pow_le_pow_left₀ (by positivity)
  linarith

/-- The final approximation domain can also have any requested relative
stability tolerance, without changing the weighted error bound. -/
theorem weighted_class_stable_local_factor (l : List (Feature G)) (g : G → ℝ)
    (hg : g ∈ featureClass l) (R₀ z : Fin l.length → ℕ)
    (hz : ∀ i, 0 < z i)
    (htest : ∀ i, IsStableQuadraticAverageTest (R₀ i) (z i) (l.get i).2)
    {R Z u : ℕ} (hR : ∀ i, R₀ i ≤ R) (hZ : 0 < Z) (hzZ : ∀ i, z i ≤ Z)
    (hu : 0 < u) {τ : ℝ} (hτ : 0 ≤ τ)
    (hbudget : (∑ i : Fin l.length, ((l.get i).1 : ℝ)/(z i : ℝ)) ≤ τ/2) :
    ∃ C : Finset (AddChar G ℂ), ∃ r : ℝ,
      C.card ≤ l.length*R ∧ commonWidth R Z/2 ≤ r ∧ r ≤ commonWidth R Z ∧
      RelativeStable C u r ∧
      Fintype.card G ≤ (512*windowDenominator R Z+1)^(2*(l.length*R))*(bohr C r).card ∧
      ∀ a : G, ∃ H : ((Σ i : Fin l.length, Fin ((z i)^2)) → ℂ) → ℝ,
        ∃ Q : (Σ i : Fin l.length, Fin ((z i)^2)) → G → ℂ,
          (∀ v, 0 ≤ H v ∧ H v ≤ 1) ∧
          LipschitzWith (∑ i : Fin l.length, (l.get i).1) H ∧
          (∀ p t, ‖Q p t‖ = 1) ∧ (∀ p, IsLocallyQuadratic (bohr C r : Set G) (Q p)) ∧
          (𝔼 t : bohr C r, (g (a+t)-H (fun p ↦ Q p t))^2) ≤ τ^2 := by
  obtain ⟨C,hC,_,hlocal⟩ := weighted_class_local_factor l g hg R₀ z hz htest hR hZ hzZ hτ hbudget
  have hw : 0 < commonWidth R Z/2 := div_pos (commonWidth_pos R hZ) (by norm_num)
  obtain ⟨r,hr,hrmax,hstable⟩ := exists_relative_stable C hw hu
  have hrr : r ≤ commonWidth R Z := by linarith
  refine ⟨C,r,hC,hr,hrr,hstable,half_common_window_card_bound C hC hZ hr,?_⟩
  exact hlocal (bohr C r) ⟨0,bohr_zero C (by linarith)⟩ (bohr_mono C hrr)

#print axioms weighted_class_local_factor
#print axioms weighted_class_stable_local_factor
end Erdos3WeightedFeatureLocalization
