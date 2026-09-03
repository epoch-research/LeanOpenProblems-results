import Submission.FiniteFourier
import Submission.FiniteBohr

/-! Spectral extraction of Bohr almost-periods from a large set of uniform almost-periods.
This is an auxiliary result, not a settlement of Erdős Problem 3. -/
namespace Erdos3SpectralAlmostPeriods
open Finset Erdos3FiniteFourier Erdos3FiniteBohr Erdos3ChangSpectrum
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma walk_close (T : Finset G) (hT : T.Nonempty) (f : G → ℂ) {e : ℝ}
    (hper : ∀ s ∈ T, ∀ t ∈ T, ∀ x, ‖f (x+s-t)-f x‖ ≤ e) (n : ℕ) (x : G) :
    ‖walkSmooth T n f x-f x‖ ≤ (n : ℝ)*e := by
  letI : Nonempty T := hT.to_subtype
  induction n generalizing x with
  | zero => simp [walkSmooth]
  | succ n ih =>
    have heq : walkSmooth T (n+1) f x-f x =
        𝔼 b : T, 𝔼 c : T, (walkSmooth T n f (x+(c : G)-(b : G))-f x) := by
      simp only [walkSmooth, cdiffSmooth, expect_sub_distrib, Fintype.expect_const]
    rw [heq]
    calc
      _ ≤ 𝔼 b : T, ‖𝔼 c : T, (walkSmooth T n f (x+(c : G)-(b : G))-f x)‖ :=
        RCLike.norm_expect_le (K := ℂ)
      _ ≤ (n : ℝ)*e+e := by
        apply expect_le univ_nonempty
        intro b _
        apply (RCLike.norm_expect_le (K := ℂ)).trans
        apply expect_le univ_nonempty
        intro c _
        calc
          _ = ‖(walkSmooth T n f (x+(c : G)-(b : G))-f (x+(c : G)-(b : G))) +
              (f (x+(c : G)-(b : G))-f x)‖ := by congr 1; ring
          _ ≤ _ := (norm_add_le _ _).trans
            (add_le_add (ih _) (hper c c.property b b.property x))
      _ = _ := by push_cast; ring

lemma shift_eq_sum (f : G → ℂ) (x t : G) :
    f (x+t)-f x = ∑ χ : AddChar G ℂ, hat f χ*χ x*(χ t-1) := by
  rw [inversion f (x+t), inversion f x, ← sum_sub_distrib]
  apply sum_congr rfl
  intro χ _
  rw [χ.map_add_eq_mul]
  ring

lemma spectral_factor_bound {b d η : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) (hη : 0 ≤ η) (hbig : 1/2 ≤ b → d ≤ η) (n : ℕ) :
    b^(2*n)*d ≤ η+2*(1/2 : ℝ)^(2*n) := by
  by_cases hb : 1/2 ≤ b
  · calc
      _ ≤ 1*d := mul_le_mul_of_nonneg_right (pow_le_one₀ hb0 hb1) hd0
      _ ≤ η := by simpa using hbig hb
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · calc
      _ ≤ (1/2 : ℝ)^(2*n)*2 :=
        mul_le_mul (pow_le_pow_left₀ hb0 (le_of_not_ge hb) _) hd2 hd0 (by positivity)
      _ ≤ _ := by linarith

/-- Repeated symmetric averaging suppresses the small spectrum exponentially. -/
theorem walk_shift_bound (T : Finset G) (f : G → ℂ) (n : ℕ) {L η : ℝ}
    (hL : (∑ χ : AddChar G ℂ, ‖hat f χ‖) ≤ L) (hη : 0 ≤ η) (t : G)
    (ht : ∀ χ : AddChar G ℂ, 1/2 ≤ ‖meanChar T χ‖ → ‖χ t-1‖ ≤ η) (x : G) :
    ‖walkSmooth T n f (x+t)-walkSmooth T n f x‖ ≤ L*(η+2*(1/2 : ℝ)^(2*n)) := by
  rw [shift_eq_sum]
  calc
    _ ≤ ∑ χ : AddChar G ℂ, ‖hat (walkSmooth T n f) χ*χ x*(χ t-1)‖ := norm_sum_le _ _
    _ ≤ ∑ χ : AddChar G ℂ, ‖hat f χ‖*(η+2*(1/2 : ℝ)^(2*n)) := by
      apply sum_le_sum
      intro χ _
      have hb := spectral_factor_bound (norm_nonneg _) (norm_meanChar_le_one T χ)
        (norm_nonneg _) (norm_char_sub_one_le_two χ t) hη (ht χ) n
      calc
        _ = ‖hat f χ‖*(‖meanChar T χ‖^(2*n)*‖χ t-1‖) := by
          rw [hat_walkSmooth]
          simp only [norm_mul, χ.norm_apply, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = (∑ χ : AddChar G ℂ, ‖hat f χ‖)*(η+2*(1/2 : ℝ)^(2*n)) := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hL (by positivity)

/-- Chang's lemma turns a large family T of uniform almost-periods into a Bohr family.
The spectral tail and the accumulated averaging error are both explicit. -/
theorem exists_bohr_almost_periods (T : Finset G) (hT : T.Nonempty) (f : G → ℂ)
    (n : ℕ) {L η e : ℝ} (hL : (∑ χ : AddChar G ℂ, ‖hat f χ‖) ≤ L) (hη : 0 ≤ η)
    (hper : ∀ s ∈ T, ∀ t ∈ T, ∀ x, ‖f (x+s-t)-f x‖ ≤ e) :
    ∃ D : Finset (AddChar G ℂ), D ⊆ spectrum T (1/2) ∧
      D.card ≤ ⌊16*Real.log (1/Erdos3CorrelationSifting.density T)⌋₊ ∧
      ∀ t ∈ bohr D (η/(D.card+1)), ∀ x : G,
        ‖f (x+t)-f x‖ ≤ 2*(n : ℝ)*e+L*(η+2*(1/2 : ℝ)^(2*n)) := by
  obtain ⟨D,hD,hcard,hspan⟩ := exists_spectrum_generators T hT (η := 1/2) (by norm_num) (by norm_num)
  have hc : 4*Real.log (1/Erdos3CorrelationSifting.density T)/(1/2 : ℝ)^2 =
      16*Real.log (1/Erdos3CorrelationSifting.density T) := by ring
  rw [hc] at hcard
  refine ⟨D,hD,hcard,?_⟩
  intro t ht x
  have hrad : 0 ≤ η/((D.card : ℝ)+1) := by positivity
  have hbound : (D.card : ℝ)*(η/((D.card : ℝ)+1)) ≤ η := by
    have hp : (0 : ℝ) < D.card+1 := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hp]
    nlinarith
  have ht' (χ : AddChar G ℂ) (hχ : 1/2 ≤ ‖meanChar T χ‖) : ‖χ t-1‖ ≤ η := by
    have hχ' : χ ∈ spectrum T (1/2) := by simpa only [Erdos3ChangSpectrum.spectrum, meanChar, mem_filter, mem_univ, true_and] using hχ
    exact (span_control D (hspan hχ') hrad ht).trans hbound
  have hs := walk_shift_bound T f n hL hη t ht' x
  have h₁ := walk_close T hT f hper n (x+t)
  have h₂ := walk_close T hT f hper n x
  calc
    _ = ‖(f (x+t)-walkSmooth T n f (x+t))+
        (walkSmooth T n f (x+t)-walkSmooth T n f x)+(walkSmooth T n f x-f x)‖ := by
      congr 1
      ring
    _ ≤ (‖f (x+t)-walkSmooth T n f (x+t)‖ +
        ‖walkSmooth T n f (x+t)-walkSmooth T n f x‖)+‖walkSmooth T n f x-f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((n : ℝ)*e+L*(η+2*(1/2 : ℝ)^(2*n)))+(n : ℝ)*e :=
      add_le_add (add_le_add (by simpa only [norm_sub_rev] using h₁) hs) h₂
    _ = _ := by ring

#print axioms walk_close
#print axioms walk_shift_bound
#print axioms exists_bohr_almost_periods
end Erdos3SpectralAlmostPeriods
