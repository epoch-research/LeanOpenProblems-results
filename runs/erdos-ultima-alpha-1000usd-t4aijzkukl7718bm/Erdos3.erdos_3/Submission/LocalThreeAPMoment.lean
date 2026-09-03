import Submission.LocalCorrelationCentering
import Submission.RobustWeightedUnbalancing
import Submission.ThreeAPSifting

/-! A local weighted moment gain for three-term-progression-free sets.
The weighted mass of admissible centers is an explicit hypothesis; this does not
prove that the localized density increment can be iterated. -/
namespace Erdos3LocalThreeAPMoment
open Finset Erdos3FiniteBohr Erdos3CorrelationMoments Erdos3CorrelationSifting
  Erdos3BohrLocalAverages Erdos3LocalCorrelationCentering Erdos3ThreeAPSifting
  Erdos3RobustWeightedUnbalancing
open scoped BigOperators Classical
set_option maxHeartbeats 2500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def doubledMass (Z : Finset G) (w : G → ℝ) : ℝ :=
  (∑ a ∈ Z, w (a+a))/(Fintype.card G : ℝ)

lemma weighted_double_lower (Z : Finset G) (hZ : ThreeAPFree (Z : Set G))
    (w f : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x) {c : ℝ}
    (hc : ∀ a ∈ Z, c ≤ f (a+a)) :
    c*doubledMass Z w ≤ 𝔼 x : G, w x*f x := by
  have hsum : c*(∑ a ∈ Z, w (a+a)) ≤ ∑ x : G, w x*f x := by
    calc
      _ = ∑ a ∈ Z, w (a+a)*c := by rw [mul_sum]; apply sum_congr rfl; intro a _; ring
      _ ≤ ∑ a ∈ Z, w (a+a)*f (a+a) := sum_le_sum (fun a ha ↦ mul_le_mul_of_nonneg_left (hc a ha) (hw _))
      _ = ∑ x ∈ Z.image (fun a ↦ a+a), w x*f x := by rw [sum_image (double_injOn Z hZ)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ ↦ mul_nonneg (hw x) (hf x))
  rw [Fintype.expect_eq_sum_div_card]
  calc
    c*doubledMass Z w = (c*(∑ a ∈ Z, w (a+a)))/(Fintype.card G : ℝ) := by unfold doubledMass; ring
    _ ≤ _ := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

lemma weighted_deficit (Z : Finset G) (hZ : ThreeAPFree (Z : Set G)) (w f : G → ℝ)
    (hw : ∀ x, 0 ≤ w x) {p : ℕ} (hp : Even p)
    (hmass : (2/3 : ℝ)^p ≤ doubledMass Z w)
    (hneg : ∀ a ∈ Z, f (a+a) ≤ -3/4) :
    (1/2 : ℝ)^p ≤ |𝔼 x : G, w x*(f x)^p| := by
  have hpoint (a : G) (ha : a ∈ Z) : (3/4 : ℝ)^p ≤ (f (a+a))^p := by
    calc
      _ ≤ (-f (a+a))^p := pow_le_pow_left₀ (by norm_num) (by linarith [hneg a ha]) p
      _ = _ := hp.neg_pow _
  calc
    (1/2 : ℝ)^p = (3/4 : ℝ)^p*(2/3 : ℝ)^p := by rw [← mul_pow]; norm_num
    _ ≤ (3/4 : ℝ)^p*doubledMass Z w := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ 𝔼 x : G, w x*(f x)^p := weighted_double_lower Z hZ w (fun x ↦ (f x)^p)
      hw (fun x ↦ hp.pow_nonneg _) hpoint
    _ ≤ _ := le_abs_self _

lemma conv_localNormalized (A B : Finset G) (t : G) :
    conv (localNormalized A B) t = conv (indicator A) t/(relativeDensity A B)^2 := by
  unfold conv localNormalized
  simp_rw [div_mul_div_comm, ← sq]
  exact (expect_div ..).symm

lemma local_convolution_at_double (A B : Finset G) (hA : A.Nonempty) (hAB : A ⊆ B)
    (hfree : ThreeAPFree (A : Set G)) {a : G} (ha : a ∈ A) :
    conv (localNormalized A B) (a+a)/density B = 1/((relativeDensity A B)^2*(B.card : ℝ)) := by
  rw [conv_localNormalized, conv_indicator_double A hfree ha]
  unfold density
  have hα := (relativeDensity_pos A B hA hAB).ne'
  have hB : (B.card : ℝ) ≠ 0 := by exact_mod_cast (hA.mono hAB).card_pos.ne'
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := G)
  field_simp

/-- A local three-term-free set has a large weighted correlation moment if the chosen
symmetric correlation weight gives enough mass to admissible doubled centers. -/
theorem local_threeAP_weighted_gain (D : Finset (AddChar G ℂ)) {r h δ : ℝ}
    (hr : 0 ≤ r) (hh : 0 ≤ h) (hδ : 0 ≤ δ)
    (hgrowth : ((bohr D (r+h)).card : ℝ) ≤ (1+δ)*((bohr D (r-h)).card : ℝ))
    (A Z : Finset G) (hA : A.Nonempty) (hAB : A ⊆ bohr D r) (hZA : Z ⊆ A)
    (hfree : ThreeAPFree (A : Set G))
    (hsize : 8 ≤ (relativeDensity A (bohr D r))^2*((bohr D r).card : ℝ))
    (herror : δ*(2/relativeDensity A (bohr D r)+1) ≤ 1/256)
    (u : G → ℝ) (hu : ∀ x, 0 ≤ u x) (humean : (𝔼 x : G, u x) = 1)
    (hueven : ∀ x, u (-x) = u x)
    (hweight : ∀ t, corr u t ≠ 0 → t ∈ bohr D h)
    (hcenters : ∀ a ∈ Z, a+a ∈ bohr D h)
    {p : ℕ} (hp : 0 < p) (hpeven : Even p)
    (hmass : (2/3 : ℝ)^p ≤ doubledMass Z (corr u)) :
    (17/16 : ℝ)^(8*p) ≤ 𝔼 t : G, corr u t*
      (corr (localNormalized A (bohr D r)) t/density (bohr D r))^(8*p) := by
  let B := bohr D r
  let f := localNormalized A B
  let g : G → ℝ := fun x ↦ f x-indicator B x
  have hB : B.Nonempty := hA.mono hAB
  have hβ := density_pos B hB
  have hα := relativeDensity_pos A B hA hAB
  have hf (x : G) : 0 ≤ f x := div_nonneg (indicator_nonneg A x) hα.le
  have hsmall : δ*density B*(2/relativeDensity A B+1) ≤ density B/256 := by
    have he := mul_le_mul_of_nonneg_left herror hβ.le
    nlinarith
  have hcorr (t : G) (ht : t ∈ bohr D h) :
      |corr g t-(corr f t-density B)| ≤ density B/256 := by
    exact ((bohr_local_centering D hr hh hδ hgrowth A hA hAB ht).1).trans hsmall
  have hconv (t : G) (ht : t ∈ bohr D h) :
      |conv g t-(conv f t-density B)| ≤ density B/256 := by
    exact ((bohr_local_centering D hr hh hδ hgrowth A hA hAB ht).2).trans hsmall
  have hneg (a : G) (ha : a ∈ Z) : conv g (a+a)/density B ≤ -3/4 := by
    have hv : conv f (a+a)/density B ≤ 1/8 := by
      rw [local_convolution_at_double A B hA hAB hfree (hZA ha)]
      exact one_div_le_one_div_of_le (by norm_num) hsize
    have he := (abs_le.mp (hconv (a+a) (hcenters a ha))).2
    have hv' := (div_le_iff₀ hβ).mp hv
    apply (div_le_iff₀ hβ).mpr
    nlinarith
  have hZ : ThreeAPFree (Z : Set G) := by
    intro a ha b hb c hc he
    exact hfree (hZA ha) (hZA hb) (hZA hc) he
  have hw (t : G) : 0 ≤ corr u t := expect_nonneg (fun x _ ↦ mul_nonneg (hu x) (hu _))
  have hdeficit := weighted_deficit Z hZ (corr u) (fun t ↦ conv g t/density B) hw hpeven hmass hneg
  exact local_weighted_unbalance f g u hf hu humean hueven hβ hp hdeficit
    (fun t ht ↦ hcorr t (hweight t ht))

#print axioms weighted_deficit
#print axioms local_threeAP_weighted_gain
end Erdos3LocalThreeAPMoment
