import Submission.BohrTransport
import Submission.LocalSiftedIncrement

/-! Fixed-tolerance stable Bohr sets with a radius-relative stability window. -/
namespace Erdos3RelativeStableBohr
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3BohrStableScale Erdos3BohrTransport
open scoped BigOperators Classical
set_option maxHeartbeats 2500000
variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

/-- The denominator controlling the relative stability window. -/
def windowDenominator (d z : ℕ) : ℕ := 4*z*(7*d+1)
noncomputable def relativeWidth (D : Finset (AddChar G ℂ)) (z : ℕ) (r : ℝ) : ℝ :=
  r/(windowDenominator D.card z : ℝ)

def RelativeStable (D : Finset (AddChar G ℂ)) (z : ℕ) (r : ℝ) : Prop :=
  ((bohr D (r+relativeWidth D z r)).card : ℝ) ≤
    (1+1/(z : ℝ))*((bohr D (r-relativeWidth D z r)).card : ℝ)

lemma windowDenominator_pos (d : ℕ) {z : ℕ} (hz : 0 < z) :
    0 < windowDenominator d z := by unfold windowDenominator; positivity
lemma relativeWidth_pos (D : Finset (AddChar G ℂ)) {z : ℕ} (hz : 0 < z)
    {r : ℝ} (hr : 0 < r) : 0 < relativeWidth D z r := by
  unfold relativeWidth
  exact div_pos hr (by exact_mod_cast windowDenominator_pos D.card hz)
lemma relativeWidth_le_quarter (D : Finset (AddChar G ℂ)) {z : ℕ} (hz : 0 < z)
    {r : ℝ} (hr : 0 ≤ r) : relativeWidth D z r ≤ r/4 := by
  unfold relativeWidth
  apply div_le_div_of_nonneg_left hr (by norm_num)
  exact_mod_cast (show 4 ≤ windowDenominator D.card z by unfold windowDenominator; nlinarith)

lemma stable_growth_mono (D : Finset (AddChar G ℂ)) {r h h' δ δ' : ℝ}
    (hhh : h' ≤ h) (hδ : 0 ≤ δ) (hδδ : δ ≤ δ')
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ)) :
    ((bohr D (r+h')).card : ℝ) ≤ (1+δ')*((bohr D (r-h')).card : ℝ) := by
  have hleft : ((bohr D (r+h')).card : ℝ) ≤ (bohr D (r+h)).card := by
    exact_mod_cast card_le_card (bohr_mono D (by linarith : r+h' ≤ r+h))
  have hright : ((bohr D (r-h)).card : ℝ) ≤ (bohr D (r-h')).card := by
    exact_mod_cast card_le_card (bohr_mono D (by linarith : r-h ≤ r-h'))
  calc
    _ ≤ ((bohr D (r+h)).card : ℝ) := hleft
    _ ≤ (1+δ)*((bohr D (r-h)).card : ℝ) := hgrowth
    _ ≤ (1+δ)*((bohr D (r-h')).card : ℝ) := mul_le_mul_of_nonneg_left hright (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

lemma relativeWidth_le_stabilityWidth (D : Finset (AddChar G ℂ)) (z : ℕ)
    {r R : ℝ} (hr : r ≤ 2*R) : relativeWidth D z r ≤ stabilityWidth D z R := by
  have he : stabilityWidth D z R = (2*R)/(windowDenominator D.card z : ℝ) := by
    unfold stabilityWidth stabilitySteps windowDenominator
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right hr (Nat.cast_nonneg _)

/-- Every radius has a stable radius within a factor of two, with a relative window. -/
theorem exists_relative_stable (D : Finset (AddChar G ℂ)) {R : ℝ} (hR : 0 < R)
    {z : ℕ} (hz : 0 < z) : ∃ r : ℝ, R ≤ r ∧ r ≤ 2*R ∧ RelativeStable D z r := by
  obtain ⟨r,hlo,hhi,hgrowth⟩ := exists_stable_radius D hR hz
  have hw := stabilityWidth_pos D hz hR
  have hr : r ≤ 2*R := by linarith
  refine ⟨r,by linarith,hr,?_⟩
  exact stable_growth_mono D (relativeWidth_le_stabilityWidth D z hr)
    (by positivity : (0 : ℝ) ≤ 1/z) le_rfl hgrowth

lemma relativeWidth_transport (e : G ≃+ H) (D : Finset (AddChar G ℂ)) (z : ℕ) (r : ℝ) :
    relativeWidth (transportChars e D) z r = relativeWidth D z r := by
  simp only [relativeWidth, transportChars_card]

lemma RelativeStable.transport {D : Finset (AddChar G ℂ)} {z : ℕ} {r : ℝ}
    (h : RelativeStable D z r) (e : G ≃+ H) : RelativeStable (transportChars e D) z r := by
  simpa only [RelativeStable, relativeWidth_transport, transport_bohr_card] using h

lemma RelativeStable.enlargement {D : Finset (AddChar G ℂ)} {z : ℕ} {r h : ℝ}
    (hstable : RelativeStable D z r) (hz : 0 < z)
    (hh : h ≤ relativeWidth D z r) (hr : 0 ≤ r) :
    ((bohr D (r+h)).card : ℝ) ≤ (1+1/(z : ℝ))*((bohr D r).card : ℝ) := by
  have hwidth := relativeWidth_le_quarter D hz hr
  have hw0 : 0 ≤ relativeWidth D z r := by unfold relativeWidth; positivity
  have h₁ : ((bohr D (r+h)).card : ℝ) ≤ (bohr D (r+relativeWidth D z r)).card := by
    exact_mod_cast card_le_card (bohr_mono D (by linarith : r+h ≤ r+relativeWidth D z r))
  have h₂ : ((bohr D (r-relativeWidth D z r)).card : ℝ) ≤ (bohr D r).card := by
    exact_mod_cast card_le_card (bohr_mono D (by linarith : r-relativeWidth D z r ≤ r))
  exact (h₁.trans hstable).trans (mul_le_mul_of_nonneg_left h₂ (by positivity))

lemma RelativeStable.weaken {D : Finset (AddChar G ℂ)} {z z' : ℕ} {r : ℝ}
    (hstable : RelativeStable D z' r) (hz : 0 < z) (hzz : z ≤ z') (hr : 0 ≤ r) :
    ((bohr D (r+relativeWidth D z' r)).card : ℝ) ≤
      (1+1/(z : ℝ))*((bohr D (r-relativeWidth D z' r)).card : ℝ) := by
  have hzzR : (z : ℝ) ≤ z' := by exact_mod_cast hzz
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  apply hstable.trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  gcongr

/-- The first localized window has an explicit size relative to the previous base. -/
lemma initial_window_card_bound (D : Finset (AddChar G ℂ)) {z : ℕ} (hz : 0 < z)
    {r w : ℝ} (hr : 0 < r) (hw : relativeWidth D z r/4 ≤ w) :
    (bohr D r).card ≤
      (16*windowDenominator D.card z+1)^(2*D.card)*(bohr D w).card := by
  let q := 8*windowDenominator D.card z
  have hq : 0 < q := by dsimp [q]; exact Nat.mul_pos (by decide) (windowDenominator_pos D.card hz)
  have hh := card_scale_le D hr hq
  have he : 2*r/(q : ℝ) = relativeWidth D z r/4 := by
    dsimp [q,relativeWidth]
    push_cast
    ring
  rw [he] at hh
  exact hh.trans (by
    have hc := card_le_card (bohr_mono D hw)
    simpa only [q, show 2*(8*windowDenominator D.card z)+1 = 16*windowDenominator D.card z+1 by omega]
      using Nat.mul_le_mul_left ((2*q+1)^(2*D.card)) hc)

#print axioms exists_relative_stable
#print axioms initial_window_card_bound
end Erdos3RelativeStableBohr
