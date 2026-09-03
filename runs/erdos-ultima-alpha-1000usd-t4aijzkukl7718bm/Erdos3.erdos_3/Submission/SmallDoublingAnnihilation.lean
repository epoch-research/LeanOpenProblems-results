import Submission.AveragedAntisymmetry

/-! Sampling in a small-doubling set gives simultaneous approximate annihilation
of its large spectrum, with no ambient-density loss. -/
namespace Erdos3SmallDoublingAnnihilation
open Finset Erdos3CrootSisaskL2 Erdos3CorrelationSifting Erdos3FiniteFourier
  Erdos3SpectralGraphEnergy
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma norm_character_difference (χ : AddChar G ℂ) (s t : G) :
    ‖χ s-χ t‖ = ‖χ (s-t)-1‖ := by
  have he : χ s-χ t = (χ (s-t)-1)*χ t := by
    rw [sub_mul,one_mul,← χ.map_add_eq_mul,sub_add_cancel]
  rw [he,norm_mul,AddChar.norm_apply,mul_one]

lemma sum_character_shift (f : G → ℝ) (s : G) (χ : AddChar G ℂ) :
    (∑ x, (f (x+s) : ℂ)*conj (χ x)) = χ s*(∑ x, (f x : ℂ)*conj (χ x)) := by
  calc
    _ = ∑ x, (f x : ℂ)*conj (χ (x-s)) :=
      Fintype.sum_equiv (Equiv.addRight s) _ _ (fun x ↦ by simp)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      rw [char_sub,map_mul,starRingEnd_self_apply]
      ring

lemma sum_indicator_character (A : Finset G) (χ : AddChar G ℂ) :
    (∑ x, (indicator A x : ℂ)*conj (χ x)) = (A.card : ℂ)*conj (meanChar A χ) := by
  calc
    _ = ∑ x ∈ A, conj (χ x) := by simp [indicator,apply_ite]
    _ = _ := by
      have hh := (Fintype.card_mul_expect (fun a : A ↦ conj (χ a))).symm
      rw [sum_coe_sort A (fun x ↦ conj (χ x))] at hh
      simpa only [meanChar,expect_conj,Fintype.card_coe] using hh

lemma sum_smooth_indicator_character (A : Finset G) (χ : AddChar G ℂ) :
    (∑ x, (smooth A (indicator A) x : ℂ)*conj (χ x)) =
      (A.card : ℂ)*((‖meanChar A χ‖^2 : ℝ) : ℂ) := by
  simp only [smooth,ofReal_expect,expect_mul]
  rw [← expect_sum_comm]
  simp_rw [sum_character_shift,sum_indicator_character]
  rw [← expect_mul]
  change meanChar A χ*((A.card : ℂ)*conj (meanChar A χ)) = _
  rw [mul_left_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]

lemma smooth_indicator_support (A : Finset G) (x : G) (hx : x ∉ A-A) :
    smooth A (indicator A) x = 0 := by
  apply expect_eq_zero
  intro a _
  apply if_neg
  intro hxa
  apply hx
  simpa only [add_sub_cancel_right] using sub_mem_sub hxa a.property

lemma sqNorm_indicator (A : Finset G) : sqNorm (indicator A) = A.card := by
  simp [sqNorm,indicator]

lemma sum_supported_character_sq_le (S : Finset G) (f : G → ℝ)
    (hs : ∀ x, x ∉ S → f x = 0) (χ : AddChar G ℂ) :
    ‖∑ x, (f x : ℂ)*conj (χ x)‖^2 ≤ (S.card : ℝ)*sqNorm f := by
  have he : (∑ x, (f x : ℂ)*conj (χ x)) = ∑ x ∈ S, (f x : ℂ)*conj (χ x) := by
    symm
    apply sum_subset (subset_univ S)
    intro x _ hx
    simp [hs x hx]
  have hn : ‖∑ x, (f x : ℂ)*conj (χ x)‖ ≤ ∑ x ∈ S, |f x| := by
    rw [he]
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_conj,
      AddChar.norm_apply,mul_one] using norm_sum_le S (fun x ↦ (f x : ℂ)*conj (χ x))
  calc
    _ ≤ (∑ x ∈ S, |f x|)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ (S.card : ℝ)*(∑ x ∈ S, (f x)^2) := by
      simpa only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sq_abs] using
        sum_mul_sq_le_sq_mul_sq S (fun _ ↦ (1 : ℝ)) (fun x ↦ |f x|)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ ↦ sq_nonneg _)) (by positivity)

lemma shifted_smooth_character_bound (A : Finset G) (s t : G) (χ : AddChar G ℂ) :
    (A.card : ℝ)^2*‖χ (s-t)-1‖^2*‖meanChar A χ‖^4 ≤
      2*((A-A).card : ℝ)*sqNorm (fun x ↦ smooth A (indicator A) (x+s)-smooth A (indicator A) (x+t)) := by
  let f : G → ℝ := smooth A (indicator A)
  let S : Finset G := ((A-A).image (fun x ↦ x-s)) ∪ ((A-A).image (fun x ↦ x-t))
  have hc : S.card ≤ 2*(A-A).card := by
    exact (card_union_le _ _).trans (by rw [card_image_of_injective _ (fun _ _ h ↦ sub_left_injective h),
      card_image_of_injective _ (fun _ _ h ↦ sub_left_injective h)]; omega)
  have hs (x : G) (hx : x ∉ S) : f (x+s)-f (x+t) = 0 := by
    have hns : x+s ∉ A-A := by
      intro h
      exact hx (mem_union_left _ (mem_image.mpr ⟨x+s,h,add_sub_cancel_right _ _⟩))
    have hnt : x+t ∉ A-A := by
      intro h
      exact hx (mem_union_right _ (mem_image.mpr ⟨x+t,h,add_sub_cancel_right _ _⟩))
    rw [show f (x+s) = 0 from smooth_indicator_support A _ hns,
      show f (x+t) = 0 from smooth_indicator_support A _ hnt,sub_self]
  have hb := sum_supported_character_sq_le S (fun x ↦ f (x+s)-f (x+t)) hs χ
  have hid : (∑ x, ((f (x+s)-f (x+t) : ℝ) : ℂ)*conj (χ x)) =
      (χ s-χ t)*((A.card : ℂ)*((‖meanChar A χ‖^2 : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_sub,sub_mul,sum_sub_distrib,sum_character_shift,f,
      sum_smooth_indicator_character]
  have hn : ‖(χ s-χ t)*((A.card : ℂ)*((‖meanChar A χ‖^2 : ℝ) : ℂ))‖^2 =
      (A.card : ℝ)^2*‖χ (s-t)-1‖^2*‖meanChar A χ‖^4 := by
    rw [norm_mul,norm_mul,norm_character_difference,Complex.norm_natCast,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    ring
  rw [hid,hn] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc)
    (sum_nonneg (fun _ _ ↦ sq_nonneg _)))

/-- Every character with large mean on A is approximately annihilated by
all differences of a large subset. The analytic cost uses |A-A|/|A|;
the packing cost uses |A+A|/|A|, not the ambient density. -/
theorem exists_spectrum_almost_annihilators (A : Finset G) (hA : A.Nonempty)
    {n : ℕ} (hn : 0 < n) :
    ∃ T : Finset G, T.Nonempty ∧ T ⊆ A ∧
      A.card^n*A.card ≤ 2*(A+A).card^n*T.card ∧
      ∀ s ∈ T, ∀ t ∈ T, ∀ χ : AddChar G ℂ,
        (n : ℝ)*(A.card : ℝ)*‖χ (s-t)-1‖^2*‖meanChar A χ‖^4 ≤ 16*((A-A).card : ℝ) := by
  obtain ⟨T,hsub,hcard,hper⟩ := exists_many_L2_almost_periods A A hA hA (indicator A) hn
  have hT : T.Nonempty := by
    apply card_pos.mp
    by_contra h
    have hz : T.card = 0 := by omega
    rw [hz,mul_zero] at hcard
    have hp := mul_pos (pow_pos hA.card_pos n) hA.card_pos
    omega
  refine ⟨T,hT,hsub,?_,?_⟩
  · convert hcard using 1
    congr 4
    ext x
    simp only [mem_add]
  · intro s hs t ht χ
    have hp := hper s hs t ht
    rw [sqNorm_indicator] at hp
    have he := (shifted_smooth_character_bound A s t χ).trans
      (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*((A-A).card : ℝ)))
    have ha : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    have he' := mul_le_mul_of_nonneg_left he hnR.le
    field_simp at he'
    nlinarith only [he']

#print axioms exists_spectrum_almost_annihilators
end Erdos3SmallDoublingAnnihilation
