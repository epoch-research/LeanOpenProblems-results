import Submission.LocalQuadraticRegularityFactor
import Submission.StableWindowCounting

/-! The common factor window itself can be chosen relatively stable, with an
independent tolerance and no additional phase-count or rank loss. Sampling
is performed on that window, not on a larger set followed by restriction. -/
namespace Erdos3StableLocalQuadraticFactor
open Finset Erdos3LocalQuadraticRegularityFactor Erdos3CommonQuadraticWindow
  Erdos3FiniteBohr Erdos3BohrCovering Erdos3RelativeStableBohr
  Erdos3StableQuadraticRegularity Erdos3ClippedWeakRegularity
  Erdos3LocalQuadraticInverse
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma half_common_window_card_bound (C : Finset (AddChar G ℂ)) {T R z : ℕ}
    (hC : C.card ≤ T*R) (hz : 0 < z) {r : ℝ} (hr : commonWidth R z/2 ≤ r) :
    Fintype.card G ≤ (512*windowDenominator R z+1)^(2*(T*R))*(bohr C r).card := by
  have hq : 0 < 256*windowDenominator R z := by
    exact Nat.mul_pos (by decide) (windowDenominator_pos R hz)
  have h := card_bohr_lower C hq
  have he : 2/((256*windowDenominator R z : ℕ) : ℝ) = commonWidth R z/2 := by
    unfold commonWidth
    push_cast
    ring
  rw [he] at h
  have hc := card_le_card (bohr_mono C hr)
  calc
    _ ≤ (2*(256*windowDenominator R z)+1)^(2*C.card)*(bohr C (commonWidth R z/2)).card := h
    _ ≤ _ := by
      rw [show 2*(256*windowDenominator R z)+1 = 512*windowDenominator R z+1 by ring]
      gcongr
      omega

/-- The additional window-stability tolerance u is independent of the test
stability z and does not alter either the number of coordinates or the error. -/
theorem stable_window_local_factor (l : List (G → ℝ)) {R z u : ℕ}
    (hz : 0 < z) (hu : 0 < u) (hl : ∀ ψ ∈ l, IsStableQuadraticAverageTest R z ψ)
    (ρ : ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ C : Finset (AddChar G ℂ), ∃ r : ℝ,
      C.card ≤ l.length*R ∧ commonWidth R z/2 ≤ r ∧ r ≤ commonWidth R z ∧
      RelativeStable C u r ∧
      Fintype.card G ≤ (512*windowDenominator R z+1)^(2*(l.length*R))*(bohr C r).card ∧
      ∀ a : G, ∃ Φ : (Fin l.length × Fin M → ℂ) → ℝ,
        ∃ Q : (Fin l.length × Fin M) → G → ℂ,
          (∀ v, 0 ≤ Φ v ∧ Φ v ≤ 1) ∧
          LipschitzWith (⟨|ρ|,abs_nonneg ρ⟩*(l.length : NNReal)) Φ ∧
          (∀ p t, ‖Q p t‖ = 1) ∧
          (∀ p, IsLocallyQuadratic (bohr C r : Set G) (Q p)) ∧
          (𝔼 t : bohr C r, (clippedSum ρ l (a+t)-Φ (fun p ↦ Q p t))^2) ≤
            ρ^2*(l.length : ℝ)^2*(2/(z : ℝ)^2+2/(M : ℝ)) := by
  obtain ⟨C,hC,_,hlocal⟩ := stable_test_list_local_factor_on_subwindows l hz hl ρ hM
  have hw : 0 < commonWidth R z/2 := div_pos (commonWidth_pos R hz) (by norm_num)
  obtain ⟨r,hr,hrmax,hstable⟩ := exists_relative_stable C hw hu
  have hrr : r ≤ commonWidth R z := by linarith
  refine ⟨C,r,hC,hr,hrr,hstable,half_common_window_card_bound C hC hz hr,?_⟩
  exact hlocal (bohr C r) ⟨0,bohr_zero C (by linarith)⟩ (bohr_mono C hrr)

#print axioms half_common_window_card_bound
#print axioms stable_window_local_factor
end Erdos3StableLocalQuadraticFactor
