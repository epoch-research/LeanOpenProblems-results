import Submission.StableQuadraticRegularity
import Submission.RelativeSpectrumPhase

/-! A stable quadratic average has an approximation with frozen centers on its
relative Bohr window. The error is the stability tolerance, not an inverse
Bohr density. -/
namespace Erdos3FixedCenterQuadraticAverage
open Finset Erdos3QuadraticAverageDetectors Erdos3RelativeStableBohr
  Erdos3FiniteBohr Erdos3BohrTranslation Erdos3CorrelationSifting
  Erdos3RelativeSpectrumPhase Erdos3BohrCovering Erdos3LocalQuadraticInverse
  Erdos3FiniteUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def fixedAverage (B : Finset G) (q : G → G → ℂ)
    (b : G → ℂ) (a t : G) : ℂ :=
  𝔼 y : B, b (a-y)*conj (q (a-y) (y+t))

lemma weighted_translation_bound_complex (w : G → ℝ) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (t : G) :
    ‖(𝔼 x : G, (w (x+t) : ℂ)*f x)-(𝔼 x : G, (w x : ℂ)*f x)‖ ≤
      𝔼 x : G, |w (x+t)-w x| := by
  rw [← expect_sub_distrib]
  have he (x : G) : (w (x+t) : ℂ)*f x-(w x : ℂ)*f x =
      ((w (x+t)-w x : ℝ) : ℂ)*f x := by rw [Complex.ofReal_sub,sub_mul]
  simp only [he]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le_expect
  intro x _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_one _)

lemma complexAverage_shift (B : Finset G) (hB : B.Nonempty)
    (q : G → G → ℂ) (b : G → ℂ) (a t : G) :
    complexAverage B q b (a+t) =
      𝔼 x : G, (normalized B (x+t) : ℂ)*(b (a-x)*conj (q (a-x) (x+t))) := by
  unfold complexAverage
  rw [← expect_normalized_mul_complex B hB (fun y ↦ b ((a+t)-y)*conj (q ((a+t)-y) y))]
  symm
  apply Fintype.expect_equiv (Equiv.addRight t)
  intro x
  change (normalized B (x+t) : ℂ)*(b (a-x)*conj (q (a-x) (x+t))) =
    (normalized B (x+t) : ℂ)*(b ((a+t)-(x+t))*conj (q ((a+t)-(x+t)) (x+t)))
  rw [show (a+t)-(x+t) = a-x by abel]

/-- Freezing the centers costs only the L1 translation error of the averaging
measure. No polynomial hypothesis is needed for this analytic estimate. -/
theorem complexAverage_sub_fixed_le (B : Finset G) (hB : B.Nonempty)
    (q : G → G → ℂ) (hq : ∀ a y, ‖q a y‖ = 1)
    (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (a t : G) :
    ‖complexAverage B q b (a+t)-fixedAverage B q b a t‖ ≤
      𝔼 x : G, |normalized B (x+t)-normalized B x| := by
  rw [complexAverage_shift B hB, fixedAverage,
    ← expect_normalized_mul_complex B hB (fun y ↦ b (a-y)*conj (q (a-y) (y+t)))]
  apply weighted_translation_bound_complex
  intro x
  simpa only [norm_mul,Complex.norm_conj,hq,mul_one] using hb (a-x)

/-- Every translate in the relative stability window admits the same fixed
center representation to precision 1/z. -/
theorem stable_fixed_approximation (D : Finset (AddChar G ℂ)) {r : ℝ}
    (hr : 0 < r) {z : ℕ} (hz : 0 < z) (hstable : RelativeStable D z r)
    (q : G → G → ℂ) (hq : ∀ a y, ‖q a y‖ = 1)
    (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (a : G)
    {t : G} (ht : t ∈ bohr D (relativeWidth D z r)) :
    ‖complexAverage (bohr D r) q b (a+t)-fixedAverage (bohr D r) q b a t‖ ≤
      1/(z : ℝ) := by
  apply (complexAverage_sub_fixed_le _ ⟨0,bohr_zero D hr.le⟩ q hq b hb a t).trans
  exact normalized_bohr_translation_le D hr.le (relativeWidth_pos D hz hr).le
    (by positivity) hstable ht

lemma fixedAverage_norm (B : Finset G) (hB : B.Nonempty)
    (q : G → G → ℂ) (hq : ∀ a y, ‖q a y‖ = 1)
    (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (a t : G) :
    ‖fixedAverage B q b a t‖ ≤ 1 := by
  letI : Nonempty B := hB.to_subtype
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro y _
  simpa only [norm_mul,Complex.norm_conj,hq,mul_one] using hb (a-y)

lemma stable_fixed_real_approximation (D : Finset (AddChar G ℂ)) {r : ℝ}
    (hr : 0 < r) {z : ℕ} (hz : 0 < z) (hstable : RelativeStable D z r)
    (q : G → G → ℂ) (hq : ∀ a y, ‖q a y‖ = 1)
    (b : G → ℂ) (hb : ∀ a, ‖b a‖ ≤ 1) (a : G)
    {t : G} (ht : t ∈ bohr D (relativeWidth D z r)) :
    |realAverage (bohr D r) q b (a+t)-(fixedAverage (bohr D r) q b a t).re| ≤
      1/(z : ℝ) := by
  exact (Complex.abs_re_le_norm
    (complexAverage (bohr D r) q b (a+t)-fixedAverage (bohr D r) q b a t)).trans
    (stable_fixed_approximation D hr hz hstable q hq b hb a ht)

lemma IsLocallyQuadratic.translate {R S : Set G} {q : G → ℂ}
    (hq : IsLocallyQuadratic R q) (y : G) (hS : ∀ t ∈ S, y+t ∈ R) :
    IsLocallyQuadratic S (fun t ↦ q (y+t)) := by
  intro x h k l hx hxh hxk hxkh hxl hxlh hxlk hxlkh
  have ht := hq (y+x) h k l (hS x hx)
    (by simpa only [add_assoc] using hS (x+h) hxh)
    (by simpa only [add_assoc] using hS (x+k) hxk)
    (by simpa only [add_assoc] using hS ((x+k)+h) hxkh)
    (by simpa only [add_assoc] using hS (x+l) hxl)
    (by simpa only [add_assoc] using hS ((x+l)+h) hxlh)
    (by simpa only [add_assoc] using hS ((x+l)+k) hxlk)
    (by simpa only [add_assoc] using hS (((x+l)+k)+h) hxlkh)
  simpa only [derivative,add_assoc] using ht

/-- The larger domain of quadraticity absorbs all shifted centers, so sampled
centers need not be trimmed to an interior subset. -/
theorem shifted_phase_quadratic (D : Finset (AddChar G ℂ)) {r : ℝ}
    (hr : 0 ≤ r) (hrmax : r ≤ 1/32) {z : ℕ} (hz : 0 < z)
    (q : G → G → ℂ)
    (hq : ∀ a, IsLocallyQuadratic (bohr D (1/16) : Set G) (q a))
    (a : G) {y : G} (hy : y ∈ bohr D r) :
    IsLocallyQuadratic (bohr D (relativeWidth D z r) : Set G)
      (fun t ↦ q (a-y) (y+t)) := by
  apply IsLocallyQuadratic.translate (hq (a-y)) y
  intro t ht
  apply bohr_mono D (show r+relativeWidth D z r ≤ 1/16 from
    by linarith [relativeWidth_le_quarter D hz hr])
  exact bohr_add hy ht

#print axioms stable_fixed_approximation
#print axioms shifted_phase_quadratic
end Erdos3FixedCenterQuadraticAverage
