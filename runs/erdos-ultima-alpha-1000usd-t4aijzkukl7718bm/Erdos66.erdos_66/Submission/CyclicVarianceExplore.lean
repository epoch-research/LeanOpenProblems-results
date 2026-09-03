import Submission.MixedEnergyExplore

/-! An exact variance floor for self-convolution on finite abelian groups.
The square-root scale this forces is compatible with the conjectured limit. -/
namespace Erdos66CyclicVariance
open Erdos66MixedEnergy
open scoped Classical
variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma sum_conv (f g : G → ℝ) : (∑ t, conv f g t) = (∑ x, f x) * (∑ x, g x) := by
  unfold conv
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have he (x : G) : (∑ t, g (t - x)) = ∑ t, g t := by
    simpa only [Equiv.coe_addRight, sub_eq_add_neg] using Equiv.sum_comp (Equiv.addRight (-x)) g
  simp_rw [he]
  exact (Finset.sum_mul _ _ _).symm

lemma sum_corr (f : G → ℝ) : (∑ t, corr f t) = (∑ x, f x) ^ 2 := by
  unfold corr
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have he (x : G) : (∑ t, f (x + t)) = ∑ t, f t := by
    exact Equiv.sum_comp (Equiv.addLeft x) f
  simp_rw [he]
  rw [← Finset.sum_mul, pow_two]

lemma corr_zero (f : G → ℝ) : corr f 0 = ∑ x, f x ^ 2 := by
  simp [corr, pow_two]

lemma variance_identity (f : G → ℝ) (μ : ℝ) :
    (∑ t, (conv f f t - μ) ^ 2) =
      energy f f - 2 * μ * (∑ x, f x) ^ 2 + Fintype.card G * μ ^ 2 := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, energy,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (∑ x : G, 2 * conv f f x * μ) = 2 * μ * ∑ x : G, conv f f x by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx; ring]
  rw [sum_conv, ← pow_two]

/-- Removing the autocorrelation's diagonal and applying Cauchy--Schwarz
provides the additional term beyond the usual mean-square inequality. -/
lemma energy_floor (f : G → ℝ) :
    ((∑ x, f x) ^ 2 - ∑ x, f x ^ 2) ^ 2 ≤
      ((Fintype.card G : ℝ) - 1) * (energy f f - (∑ x, f x ^ 2) ^ 2) := by
  let S : Finset G := Finset.univ.erase 0
  have hs : (S.card : ℝ) = (Fintype.card G : ℝ) - 1 := by
    have hh := Finset.card_erase_add_one (s := Finset.univ) (a := (0 : G)) (Finset.mem_univ _)
    have hh' : (S.card : ℝ) + 1 = Fintype.card G := by exact_mod_cast hh
    linarith
  have hsum : (∑ t ∈ S, corr f t) = (∑ x, f x) ^ 2 - ∑ x, f x ^ 2 := by
    have hh := Finset.sum_erase_add (s := Finset.univ) (a := (0 : G)) (f := corr f) (Finset.mem_univ _)
    rw [sum_corr, corr_zero] at hh
    change (∑ t ∈ S, corr f t) + (∑ x, f x ^ 2) = (∑ x, f x) ^ 2 at hh
    linarith
  have hsq : (∑ t ∈ S, corr f t ^ 2) = energy f f - (∑ x, f x ^ 2) ^ 2 := by
    have hh := Finset.sum_erase_add (s := Finset.univ) (a := (0 : G)) (f := fun t ↦ corr f t ^ 2)
      (Finset.mem_univ _)
    have he : (∑ t : G, corr f t ^ 2) = energy f f := by
      rw [energy_eq_corr_inner]
      simp [pow_two]
    dsimp at hh
    rw [he, corr_zero] at hh
    change (∑ t ∈ S, corr f t ^ 2) + (∑ x, f x ^ 2) ^ 2 = energy f f at hh
    linarith
  have hh := Finset.sum_mul_sq_le_sq_mul_sq S (corr f) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  rw [hs, hsum, hsq] at hh
  nlinarith

/-- A denominator-free exact variance bound, valid for arbitrary real weights. -/
lemma variance_floor (f : G → ℝ) (μ : ℝ)
    (hμ : (Fintype.card G : ℝ) * μ = (∑ x, f x) ^ 2) :
    ((Fintype.card G : ℝ) * (∑ x, f x ^ 2) - (∑ x, f x) ^ 2) ^ 2 ≤
      (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) - 1) *
        (∑ t, (conv f f t - μ) ^ 2) := by
  have hh := mul_le_mul_of_nonneg_left (energy_floor f) (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  rw [variance_identity]
  nlinarith [sq_nonneg ((Fintype.card G : ℝ) * μ - (∑ x, f x) ^ 2)]

/-- The same floor holds about any proposed center; choosing the mean only
minimizes the left-hand variance. -/
lemma variance_floor_any_center (f : G → ℝ) (μ : ℝ) :
    ((Fintype.card G : ℝ) * (∑ x, f x ^ 2) - (∑ x, f x) ^ 2) ^ 2 ≤
      (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) - 1) *
        (∑ t, (conv f f t - μ) ^ 2) := by
  have hM : (1 : ℝ) ≤ Fintype.card G := by
    have hh : 0 < Fintype.card G := Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)
    exact_mod_cast (show 1 ≤ Fintype.card G by omega)
  have hh := mul_le_mul_of_nonneg_left (energy_floor f) (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  have hs := mul_nonneg (sub_nonneg.mpr hM)
    (sq_nonneg ((Fintype.card G : ℝ) * μ - (∑ x, f x) ^ 2))
  rw [variance_identity]
  nlinarith

noncomputable def indicator (B : Finset G) (x : G) : ℝ := if x ∈ B then 1 else 0

lemma sum_indicator (B : Finset G) : (∑ x, indicator B x) = B.card := by
  simp [indicator, ← Finset.sum_filter]

lemma sum_indicator_sq (B : Finset G) : (∑ x, indicator B x ^ 2) = B.card := by
  simp [indicator, ← Finset.sum_filter]

lemma conv_indicator (B : Finset G) (z : G) :
    conv (indicator B) (indicator B) z = ((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) := by
  simp [conv, indicator, ← Finset.sum_filter]

  congr 1
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- In particular, sparse indicator convolutions have variance at least
approximately their mean. This does not require any Fourier theory. -/
theorem indicator_variance_floor (B : Finset G) (μ : ℝ)
    (hμ : (Fintype.card G : ℝ) * μ = (B.card : ℝ) ^ 2) :
    (B.card : ℝ) ^ 2 * ((Fintype.card G : ℝ) - B.card) ^ 2 ≤
      (Fintype.card G : ℝ) * ((Fintype.card G : ℝ) - 1) *
        (∑ z : G, (((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - μ) ^ 2) := by
  have hh := variance_floor (indicator B) μ (by simpa only [sum_indicator] using hμ)
  simp only [sum_indicator, sum_indicator_sq, conv_indicator] at hh
  convert hh using 1 <;> ring

/-- A uniform error estimate must respect the variance floor. -/
theorem uniform_error_floor (B : Finset G) (μ E : ℝ)
    (hμ : (Fintype.card G : ℝ) * μ = (B.card : ℝ) ^ 2) (hE : 0 ≤ E)
    (he : ∀ z : G, |(((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - μ)| ≤ E) :
    (B.card : ℝ) ^ 2 * ((Fintype.card G : ℝ) - B.card) ^ 2 ≤
      (Fintype.card G : ℝ) ^ 2 * ((Fintype.card G : ℝ) - 1) * E ^ 2 := by
  have hu : (∑ z : G, (((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - μ) ^ 2) ≤
      (Fintype.card G : ℝ) * E ^ 2 := by
    calc
      _ ≤ ∑ _z : G, E ^ 2 := by
        apply Finset.sum_le_sum
        intro z hz
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hE).mpr (he z)
      _ = _ := by simp
  have hM : (1 : ℝ) ≤ Fintype.card G := by
    have hh : 0 < Fintype.card G := Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)
    exact_mod_cast (show 1 ≤ Fintype.card G by omega)
  have hh := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ Fintype.card G * ((Fintype.card G : ℝ) - 1) from
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hM))
  have hl := indicator_variance_floor B μ hμ
  nlinarith

/-- A version of the uniform error floor not requiring the proposed center
to be the exact mean. -/
theorem uniform_error_floor_any_center (B : Finset G) (μ E : ℝ) (hE : 0 ≤ E)
    (he : ∀ z : G, |(((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - μ)| ≤ E) :
    (B.card : ℝ) ^ 2 * ((Fintype.card G : ℝ) - B.card) ^ 2 ≤
      (Fintype.card G : ℝ) ^ 2 * ((Fintype.card G : ℝ) - 1) * E ^ 2 := by
  have hu : (∑ z : G, (((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - μ) ^ 2) ≤
      (Fintype.card G : ℝ) * E ^ 2 := by
    calc
      _ ≤ ∑ _z : G, E ^ 2 := by
        apply Finset.sum_le_sum
        intro z hz
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hE).mpr (he z)
      _ = _ := by simp
  have hM : (1 : ℝ) ≤ Fintype.card G := by
    have hh : 0 < Fintype.card G := Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)
    exact_mod_cast (show 1 ≤ Fintype.card G by omega)
  have hh := mul_le_mul_of_nonneg_left hu
    (mul_nonneg (Nat.cast_nonneg (Fintype.card G)) (sub_nonneg.mpr hM))
  have hl := variance_floor_any_center (indicator B) μ
  simp only [sum_indicator, sum_indicator_sq, conv_indicator] at hl
  nlinarith

/-- A proper nonempty finite subset cannot have exactly constant
self-convolution, even when the center is freely chosen. -/
theorem constant_convolution_trivial (B : Finset G) (μ : ℝ)
    (h : ∀ z : G, (((B.filter (fun a ↦ z - a ∈ B)).card : ℝ)) = μ) :
    B = ∅ ∨ B = Finset.univ := by
  have he := uniform_error_floor_any_center B μ 0 le_rfl (by intro z; rw [h z]; simp)
  have hm : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hcard : (B.card : ℝ) ≤ Fintype.card G := by exact_mod_cast Finset.card_le_univ B
  have hz : (B.card : ℝ) * ((Fintype.card G : ℝ) - B.card) = 0 := by nlinarith [sq_nonneg ((B.card : ℝ) * ((Fintype.card G : ℝ) - B.card))]
  rcases mul_eq_zero.mp hz with hz | hz
  · left
    exact Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hz)
  · right
    have hh : B.card = Fintype.card G := by exact_mod_cast (sub_eq_zero.mp hz).symm
    exact Finset.eq_univ_of_card B hh

end Erdos66CyclicVariance
