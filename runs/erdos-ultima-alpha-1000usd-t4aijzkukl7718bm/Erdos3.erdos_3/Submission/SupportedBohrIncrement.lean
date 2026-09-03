import Submission.SupportedAlmostPeriods
import Submission.RelativeBohrPeriods

/-! Relative spectral extraction for supported popular-difference smoothing,
followed by a conditional density increment. Auxiliary results only. -/
namespace Erdos3SupportedBohrIncrement
open Finset Erdos3SupportedAlmostPeriods Erdos3RelativeBohrPeriods
  Erdos3AsymmetricFourierSmoothing Erdos3AsymmetricSifting Erdos3AsymmetricIncrement
  Erdos3FiniteFourier Erdos3FiniteBohr Erdos3FourierSmoothing Erdos3BohrTranslation
  Erdos3CorrelationSifting Erdos3BohrLocalAverages Erdos3LocalCorrelationCentering
  Erdos3CrootSisaskL2
open scoped BigOperators Classical ComplexConjugate Pointwise
set_option maxHeartbeats 3000000
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma sampling_log_bound {a b p q n : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hcard : a^n*q ≤ 2*b^n*p) :
    Real.log (2/((p : ℝ)/q)) ≤ Real.log (4*((b : ℝ)/a)^n) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcardR : (a : ℝ)^n*q ≤ 2*(b : ℝ)^n*p := by exact_mod_cast hcard
  apply Real.log_le_log (by positivity)
  rw [div_div_eq_mul_div, div_pow, ← mul_div_assoc,
    div_le_div_iff₀ hpR (pow_pos haR n)]
  nlinarith

lemma supported_l1_le (S T W : Finset G) (hS : S.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    {m : ℕ} (hWS : W.card ≤ 2^(2*m)*S.card) :
    (∑ χ : AddChar G ℂ,
      ‖hat (ccrossSmooth S T (fun x ↦ (truncate W f x : ℂ))) χ‖) ≤ (2 : ℝ)^m := by
  have hh := ccrossSmooth_hat_l1_sq_support S T W hS
    (fun x ↦ (truncate W f x : ℂ))
    (fun x ↦ by simpa only [Complex.norm_real, Real.norm_eq_abs] using truncate_abs_le_one W f hf x)
    (fun x hx ↦ by simp only [truncate_support W f x hx, Complex.ofReal_zero])
  have hW : density W ≤ (2 : ℝ)^(2*m)*density S := by
    unfold density
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hWS
  have hle : density W/density S ≤ ((2 : ℝ)^m)^2 := by
    apply (div_le_iff₀ (density_pos S hS)).mpr
    rw [← pow_mul, mul_comm m 2]
    exact hW
  have hsq := hh.trans hle
  have hsum : 0 ≤ ∑ χ : AddChar G ℂ,
      ‖hat (ccrossSmooth S T (fun x ↦ (truncate W f x : ℂ))) χ‖ := sum_nonneg (fun _ _ ↦ norm_nonneg _)
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]

/-- A support and an inner sumset bound give relative-rank popular Bohr periods. -/
theorem exists_supported_relative_popular_periods (S T Q W : Finset G)
    (hS : S.Nonempty) (hT : T.Nonempty) (hQ : Q.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {b : ℝ}
    (hbad : crossPairDensity S T (fun x ↦ 1-f x) ≤ b*density S*density T)
    (hW : ∀ s ∈ S, ∀ t ∈ T, t-s ∈ W)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hWS : W.card ≤ 2^(2*m)*S.card)
    (n : ℕ) {R : ℕ} {ε : ℝ} (hε : 0 < ε) (herr : ε*4^(R+1) ≤ 1)
    (hR : 16*Real.log (4*(((T+Q).card : ℝ)/T.card)^(256*m^4*r^2)) < R+1) :
    ∃ D : Finset (AddChar G ℂ), D.card ≤ R ∧
      ∀ {δ ρ : ℝ}, 0 ≤ δ → 0 ≤ ρ → ∀ y ∈ bohr D ρ,
        (𝔼 x : G, |normalized Q (x+y)-normalized Q x|) ≤ δ →
        1-b-(4*(n : ℝ)/r+(2 : ℝ)^m*
          (δ/ε+2*(D.card : ℝ)*ρ+2*(1/2 : ℝ)^(2*n))) ≤ crossSmooth S T f y := by
  obtain ⟨P,hP,hPQ,hPc,hper,hzero,_⟩ := exists_supported_popular_periods
    S T Q W hS hT hQ f hf hbad hW hm hr hWS
  let F : G → ℂ := ccrossSmooth S T (fun x ↦ (truncate W f x : ℂ))
  have hL : (∑ χ : AddChar G ℂ, ‖hat F χ‖) ≤ (2 : ℝ)^m := supported_l1_le S T W hS f hf hWS
  have hper' : ∀ s ∈ P, ∀ t ∈ P, ∀ x, ‖F (x+s-t)-F x‖ ≤ 2/(r : ℝ) := by
    intro s hs t ht x
    have hh := hper s hs t ht (x-t)
    rw [show x-t+s = x+s-t by abel, sub_add_cancel] at hh
    simpa only [F, ccrossSmooth_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hh
  have hR' : 16*Real.log (2/((P.card : ℝ)/Q.card)) < R+1 :=
    (mul_le_mul_of_nonneg_left (sampling_log_bound hT.card_pos hP.card_pos hQ.card_pos hPc)
      (by norm_num : (0 : ℝ) ≤ 16)).trans_lt hR
  obtain ⟨D,_,hcard,hperD⟩ := exists_relative_almost_periods P Q hP hQ hPQ F n hL hε hper' hR' herr
  refine ⟨D,hcard,?_⟩
  intro δ ρ hδ hρ y hy hstable
  have hh := hperD hδ hρ y hy hstable 0
  have he : 2*(n : ℝ)*(2/(r : ℝ)) = 4*(n : ℝ)/r := by ring
  simp only [zero_add, F, ccrossSmooth_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, he] at hh
  have hmono : crossSmooth S T (truncate W f) y ≤ crossSmooth S T f y :=
    crossSmooth_mono S T _ _ (truncate_le W f (fun x ↦ (hf x).1)) y
  linarith [(abs_le.mp hh).1]

/-- Stable reference Bohr sets yield a genuine translate with increased local density,
provided the displayed popular-pair and parameter hypotheses hold. -/
theorem supported_bohr_increment (A B S T W : Finset G)
    (E : Finset (AddChar G ℂ)) {q h δ ρ : ℝ}
    (hq : 0 ≤ q) (hh : 0 ≤ h) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hgrowth : ((bohr E (q+h)).card : ℝ) ≤ (1+δ)*((bohr E (q-h)).card : ℝ))
    (hA : A.Nonempty) (hAB : A ⊆ B) (hS : S.Nonempty) (hT : T.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {b H : ℝ} (hH : 0 ≤ H)
    (hfc : ∀ t, H*f t ≤ Erdos3CorrelationMoments.corr (localNormalized A B) t/density B)
    (hbad : crossPairDensity S T (fun x ↦ 1-f x) ≤ b*density S*density T)
    (hW : ∀ s ∈ S, ∀ t ∈ T, t-s ∈ W)
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hWS : W.card ≤ 2^(2*m)*S.card)
    (n : ℕ) {R : ℕ} {ε : ℝ} (hε : 0 < ε) (herr : ε*4^(R+1) ≤ 1)
    (hR : 16*Real.log (4*(((T+bohr E q).card : ℝ)/T.card)^(256*m^4*r^2)) < R+1) :
    ∃ D : Finset (AddChar G ℂ), D.card ≤ R ∧ ∃ x : G,
      H*(1-b-(4*(n : ℝ)/r+(2 : ℝ)^m*
        (δ/ε+2*(D.card : ℝ)*ρ+2*(1/2 : ℝ)^(2*n))))*relativeDensity A B ≤
          smooth (bohr (E ∪ D) (min h ρ)) (indicator A) x := by
  obtain ⟨D,hcard,hpop⟩ := exists_supported_relative_popular_periods
    S T (bohr E q) W hS hT ⟨0,bohr_zero E hq⟩ f hf hbad hW hm hr hWS n hε herr hR
  refine ⟨D,hcard,?_⟩
  apply local_asymmetric_increment A B S T (bohr (E ∪ D) (min h ρ))
    hA hAB hS hT ⟨0,bohr_zero _ (le_min hh hρ)⟩ f hH hfc
  intro y hy
  have hyE : y ∈ bohr E h := by
    apply mem_bohr.mpr
    intro χ hχ
    exact (mem_bohr.mp hy χ (mem_union_left _ hχ)).trans (min_le_left _ _)
  have hyD : y ∈ bohr D ρ := by
    apply mem_bohr.mpr
    intro χ hχ
    exact (mem_bohr.mp hy χ (mem_union_right _ hχ)).trans (min_le_right _ _)
  exact hpop hδ hρ y hyD (normalized_bohr_translation_le E hq hh hδ hgrowth hyE)

#print axioms exists_supported_relative_popular_periods
#print axioms supported_bohr_increment
end Erdos3SupportedBohrIncrement
