import Submission.WeightedFeatureLocalization
import Submission.BudgetedStrongQuadraticRegularity

/-! Local factor representations preserving adaptive test provenance. The
weighted localization cost is read from the actual tagged list, so the stage
budget proved in strong regularity applies directly. -/
namespace Erdos3TaggedFeatureLocalization
open Finset Erdos3BudgetedStrongRegularity Erdos3BoundedFeatureClasses
  Erdos3FeatureLipschitzEnvelope Erdos3ClippedSumPerturbation
  Erdos3WeightedLocalQuadraticFactor Erdos3WeightedFeatureLocalization
  Erdos3StableQuadraticRegularity Erdos3CommonQuadraticWindow
  Erdos3StableLocalQuadraticFactor Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3BohrCovering Erdos3LocalQuadraticInverse
open scoped BigOperators Classical
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma tagged_feature_factor (t : List (TaggedTest G)) (ρ : ℕ → NNReal)
    (g : G → ℝ) (hg : g ∈ featureClass (taggedFeatures ρ t)) :
    ∃ Φ : (Fin t.length → ℝ) → ℝ,
      (∀ v, 0 ≤ Φ v ∧ Φ v ≤ 1) ∧
      (∀ v u, |Φ v-Φ u| ≤ weightedDistance (fun i ↦ ρ (t.get i).1) v u) ∧
      (∀ x, Φ (fun i ↦ (t.get i).2 x) = g x) := by
  let c : G → Fin t.length → ℝ := fun x i ↦ (t.get i).2 x
  let w : Fin t.length → NNReal := fun i ↦ ρ (t.get i).1
  have hcontrol (x y : G) : |g x-g y| ≤ weightedDistance w (c x) (c y) := by
    have hh := hg.2 x y
    change |g x-g y| ≤ featureDistance (taggedFeatures ρ t) x y at hh
    simp only [featureDistance,taggedFeatures,List.map_map,Function.comp_def] at hh
    rw [list_sum_map_eq_sum_get] at hh
    exact hh
  exact ⟨boundedEnvelope c w g,boundedEnvelope_bounds c w g,
    boundedEnvelope_abs_sub c w g,boundedEnvelope_on_coordinates c w g hg.1 hcontrol⟩

/-- The weighted provenance budget gives a tau-accurate local phase factor on
a stable common window, with no further dependence of the error on t.length. -/
theorem tagged_stable_local_factor (t : List (TaggedTest G)) (ρ : ℕ → NNReal)
    (g : G → ℝ) (hg : g ∈ featureClass (taggedFeatures ρ t))
    (R₀ z : ℕ → ℕ) (hz : ∀ j, 0 < z j)
    (htest : ∀ p ∈ t, IsStableQuadraticAverageTest (R₀ p.1) (z p.1) p.2)
    {R Z u : ℕ} (hR : ∀ p ∈ t, R₀ p.1 ≤ R) (hZ : 0 < Z)
    (hzZ : ∀ p ∈ t, z p.1 ≤ Z) (hu : 0 < u) {τ : ℝ} (hτ : 0 < τ)
    (hbudget : tagCost (fun j ↦ (ρ j : ℝ)/(z j : ℝ)) t ≤ τ/2) :
    ∃ C : Finset (AddChar G ℂ), ∃ r : ℝ,
      C.card ≤ t.length*R ∧ commonWidth R Z/2 ≤ r ∧ r ≤ commonWidth R Z ∧
      RelativeStable C u r ∧
      Fintype.card G ≤ (512*windowDenominator R Z+1)^(2*(t.length*R))*(bohr C r).card ∧
      ∀ a : G, ∃ H : ((Σ i : Fin t.length, Fin ((z (t.get i).1)^2)) → ℂ) → ℝ,
        ∃ Q : (Σ i : Fin t.length, Fin ((z (t.get i).1)^2)) → G → ℂ,
          (∀ v, 0 ≤ H v ∧ H v ≤ 1) ∧
          LipschitzWith (∑ i : Fin t.length, ρ (t.get i).1) H ∧
          (∀ p x, ‖Q p x‖ = 1) ∧ (∀ p, IsLocallyQuadratic (bohr C r : Set G) (Q p)) ∧
          (𝔼 x : bohr C r, (g (a+x)-H (fun p ↦ Q p x))^2) ≤ τ^2 := by
  obtain ⟨Φ,hΦ,hΦweighted,hrep⟩ := tagged_feature_factor t ρ g hg
  obtain ⟨C,hC,_,hlocal⟩ := weighted_stable_factor_local
    (fun i : Fin t.length ↦ (t.get i).2) (fun i ↦ R₀ (t.get i).1) (fun i ↦ z (t.get i).1)
    (fun i ↦ (z (t.get i).1)^2) (fun i ↦ hz _)
    (fun i ↦ pow_pos (hz _) 2) (fun i ↦ htest _ (List.get_mem _ _))
    (fun i ↦ hR _ (List.get_mem _ _)) hZ (fun i ↦ hzZ _ (List.get_mem _ _))
    (fun i ↦ ρ (t.get i).1) Φ hΦ hΦweighted (fun i ↦ 2/(z (t.get i).1 : ℝ))
    (fun i ↦ by positivity) (fun i ↦ (square_sample_budget _).le)
  have hC' : C.card ≤ t.length*R := by simpa only [Fintype.card_fin] using hC
  have hw : 0 < commonWidth R Z/2 := div_pos (commonWidth_pos R hZ) (by norm_num)
  obtain ⟨r,hr,hrmax,hstable⟩ := exists_relative_stable C hw hu
  have hrr : r ≤ commonWidth R Z := by linarith
  refine ⟨C,r,hC',hr,hrr,hstable,half_common_window_card_bound C hC' hZ hr,?_⟩
  intro a
  obtain ⟨H,Q,hH,hHLip,hQ,hpoly,herr⟩ := hlocal (bohr C r)
    ⟨0,bohr_zero C (by linarith)⟩ (bohr_mono C hrr) a
  refine ⟨H,Q,hH,hHLip,hQ,hpoly,?_⟩
  simp only [hrep] at herr
  apply herr.trans
  have he : (∑ i : Fin t.length, (ρ (t.get i).1 : ℝ)*(2/(z (t.get i).1 : ℝ))) =
      2*tagCost (fun j ↦ (ρ j : ℝ)/(z j : ℝ)) t := by
    rw [tagCost,list_sum_map_eq_sum_get,mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  apply pow_le_pow_left₀
  · have hn : 0 ≤ tagCost (fun j ↦ (ρ j : ℝ)/(z j : ℝ)) t := by
      unfold tagCost
      apply List.sum_nonneg
      intro a ha
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
      positivity
    positivity
  · linarith

lemma tagged_phase_count_bound (t : List (TaggedTest G)) (z : ℕ → ℕ) {Z : ℕ}
    (hZ : ∀ p ∈ t, z p.1 ≤ Z) :
    Fintype.card (Σ i : Fin t.length, Fin ((z (t.get i).1)^2)) ≤ t.length*Z^2 := by
  simp only [Fintype.card_sigma,Fintype.card_fin]
  calc
    _ ≤ ∑ _i : Fin t.length, Z^2 := sum_le_sum (fun i _ ↦ Nat.pow_le_pow_left (hZ _ (List.get_mem _ _)) 2)
    _ = _ := by simp

#print axioms tagged_stable_local_factor
#print axioms tagged_phase_count_bound
end Erdos3TaggedFeatureLocalization
