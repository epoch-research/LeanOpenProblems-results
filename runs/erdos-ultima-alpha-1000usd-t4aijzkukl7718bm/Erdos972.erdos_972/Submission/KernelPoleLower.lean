import Submission.PrimeRatioKernel

/-! Lower bounds for the prime-ratio kernel energy from a uniform simple-pole approximation. -/
namespace Erdos972KernelPoleLower

open Finset Complex
open Erdos972ExponentialSum Erdos972PrimeFejer Erdos972PrimeRatioKernel

noncomputable def pole (ε t : ℝ) : ℂ :=
  ((ε : ℂ) + Complex.I * ((-2 * Real.pi * t : ℝ) : ℂ))⁻¹

lemma phase_re_lower (t : ℝ) : 1 - 2 * Real.pi * |t| ≤ (phase t).re := by
  have h := (Complex.abs_re_le_norm (phase t - 1)).trans (norm_phase_sub_one_le t)
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith [(abs_le.mp h).1]

lemma phase_re_ge_neg_one (t : ℝ) : -1 ≤ (phase t).re := by
  have h := Complex.abs_re_le_norm (phase t)
  rw [norm_phase] at h
  exact (abs_le.mp h).1

lemma phase_re_half {t c η : ℝ} (ht : |t| ≤ η)
    (hη : 2 * Real.pi * η * |c| ≤ 1 / 2) :
    1 / 2 ≤ (phase (-t * c)).re := by
  have hb := phase_re_lower (-t * c)
  rw [abs_mul, abs_neg] at hb
  have hm := mul_le_mul_of_nonneg_right ht (abs_nonneg c)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith

lemma pole_norm_upper {ε t η : ℝ} (hη : 0 < η) (ht : η ≤ |t|) :
    ‖pole ε t‖ ≤ 1 / (2 * Real.pi * η) := by
  have hl : 2 * Real.pi * η ≤
      ‖(ε : ℂ) + Complex.I * ((-2 * Real.pi * t : ℝ) : ℂ)‖ := by
    have hi := Complex.abs_im_le_norm ((ε : ℂ) + Complex.I * ((-2 * Real.pi * t : ℝ) : ℂ))
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add] at hi
    have ha : |-2 * Real.pi * t| = 2 * Real.pi * |t| := by
      rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    rw [ha] at hi
    exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans hi
  unfold pole
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hl

lemma pole_norm_lower {u t : ℝ} (hu : 0 < u) (ht : |t| ≤ 1 / (4 * u)) :
    u / 4 ≤ ‖pole (1 / u) t‖ := by
  let z : ℂ := (((1 / u : ℝ) : ℂ) + Complex.I * ((-2 * Real.pi * t : ℝ) : ℂ))
  have hz0 : z ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    have huinv : (1 / u : ℝ) ≠ 0 := by positivity
    apply huinv
    simpa [z] using he
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzle : ‖z‖ ≤ 4 / u := by
    have he : ‖(Complex.I : ℂ) * ((-2 * Real.pi * t : ℝ) : ℂ)‖ = 2 * Real.pi * |t| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      norm_num
    have hb := norm_add_le (((1 / u : ℝ) : ℂ))
      (Complex.I * ((-2 * Real.pi * t : ℝ) : ℂ))
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 / u : ℝ))] at hb
    have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * Real.pi by positivity)
    have hpi : 2 * Real.pi * (1 / (4 * u)) ≤ 2 / u := by
      apply (le_div_iff₀ hu).mpr
      have he' : 2 * Real.pi * (1 / (4 * u)) * u = Real.pi / 2 := by field_simp; ring
      rw [he']
      linarith [Real.pi_lt_four]
    change ‖z‖ ≤ _ at hb
    calc
      ‖z‖ ≤ 1 / u + 2 / u := by linarith [(hm.trans hpi)]
      _ ≤ 4 / u := by
        have hinv : 0 ≤ u⁻¹ := by positivity
        simp only [div_eq_mul_inv, one_mul]
        linarith
  have hinv := one_div_le_one_div_of_le hzn hzle
  have he : 1 / (4 / u) = u / 4 := by field_simp
  rw [he] at hinv
  simpa only [pole, z, norm_inv, one_div] using hinv

lemma norm_lower_of_pole {u t C : ℝ} {z : ℂ} (hu : 0 < u)
    (ht : |t| ≤ 1 / (4 * u)) (hC : 8 * C ≤ u)
    (hz : ‖z - pole (1 / u) t‖ ≤ C) : u / 8 ≤ ‖z‖ := by
  have hl := pole_norm_lower hu ht
  have hs := norm_sub_norm_le (pole (1 / u) t) z
  rw [norm_sub_rev] at hs
  linarith

lemma norm_upper_of_pole {ε t C η : ℝ} {z : ℂ}
    (hη : 0 < η) (ht : η ≤ |t|) (hz : ‖z - pole ε t‖ ≤ C) :
    ‖z‖ ≤ C + 1 / (2 * Real.pi * η) := by
  have hs := norm_sub_norm_le z (pole ε t)
  have hb := pole_norm_upper (ε := ε) hη ht
  linarith

/-- A uniform pole approximation forces a large positive band in the Fourier
matrix. Frequencies outside a fixed small interval contribute only a bounded error. -/
theorem pairEnergy_lower_of_pole (S : Finset ℕ) (w x : ℕ → ℝ)
    (c C η : ℝ) (H u : ℕ) (hu : 0 < u) (hC : 0 ≤ C)
    (hCu : 8 * C ≤ u) (hη : 0 < η)
    (hphase : 2 * Real.pi * η * |c| ≤ 1 / 2)
    (hsmall : 1 / (4 * (u : ℝ)) ≤ η)
    (hpole : ∀ t : ℝ, |t| ≤ (H : ℝ) / (4 * (u : ℝ) ^ 2) →
      ‖weightedExpSum S w x t - pole (1 / u) t‖ ≤ C) :
    ((H - u : ℕ) : ℝ) * u * ((u : ℝ) ^ 2 / 128) -
      (H : ℝ) ^ 2 * (C + 1 / (2 * Real.pi * η)) ^ 2 ≤
        pairEnergy S w x c (4 * (u : ℝ) ^ 2) H := by
  let D : ℝ := 4 * (u : ℝ) ^ 2
  let F : ℝ := C + 1 / (2 * Real.pi * η)
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let A : ℕ → ℕ → ℝ := fun i j =>
    (phase (-((i : ℝ) - j) / D * c)).re *
      ‖weightedExpSum S w x (((i : ℝ) - j) / D)‖ ^ 2
  have htbound (i j : ℕ) (hi : i < H) (hj : j < H) :
      |((i : ℝ) - j) / D| ≤ (H : ℝ) / D := by
    rw [abs_div, abs_of_pos hD]
    apply div_le_div_of_nonneg_right _ hD.le
    apply abs_le.mpr
    have hiR : (i : ℝ) < H := Nat.cast_lt.mpr hi
    have hjR : (j : ℝ) < H := Nat.cast_lt.mpr hj
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) j]
  have hlow (i j : ℕ) (hi : i < H) (hj : j < H) : -F ^ 2 ≤ A i j := by
    let t : ℝ := ((i : ℝ) - j) / D
    have he : -((i : ℝ) - j) / D * c = -t * c := by dsimp [t]; ring
    change -F ^ 2 ≤ (phase _).re * _
    rw [he]
    by_cases ht : |t| ≤ η
    · have hr := phase_re_half ht hphase
      have hh := mul_nonneg (by linarith : 0 ≤ (phase (-t * c)).re)
        (sq_nonneg ‖weightedExpSum S w x t‖)
      nlinarith [sq_nonneg F]
    · have hz := norm_upper_of_pole hη (le_of_not_ge ht) (hpole t (htbound i j hi hj))
      change ‖weightedExpSum S w x t‖ ≤ F at hz
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hz 2
      have hr := mul_le_mul_of_nonneg_right (phase_re_ge_neg_one (-t * c))
        (sq_nonneg ‖weightedExpSum S w x t‖)
      nlinarith
  have hband (i j : ℕ) (hi : i < H - u) (hj : j ∈ Ioc i (i + u)) :
      (u : ℝ) ^ 2 / 128 ≤ A i j := by
    have hiH : i < H := by omega
    have hjH : j < H := by obtain ⟨_, hj⟩ := mem_Ioc.mp hj; omega
    have ht : |((i : ℝ) - j) / D| ≤ 1 / (4 * (u : ℝ)) := by
      rw [abs_div, abs_of_pos hD]
      have hij : (i : ℝ) ≤ j := Nat.cast_le.mpr (mem_Ioc.mp hj).1.le
      rw [abs_of_nonpos (sub_nonpos.mpr hij)]
      apply (div_le_iff₀ hD).mpr
      have he : (1 / (4 * (u : ℝ))) * D = (u : ℝ) := by dsimp [D]; field_simp
      rw [he]
      have hh : (j : ℝ) ≤ i + u := by exact_mod_cast (mem_Ioc.mp hj).2
      linarith
    have hz := norm_lower_of_pole huR ht hCu (hpole _ (htbound i j hiH hjH))
    have hr := phase_re_half (ht.trans hsmall) hphase
    have he : -(((i : ℝ) - j) / D) * c = -((i : ℝ) - j) / D * c := by ring
    rw [he] at hr
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (u : ℝ) / 8) hz 2
    have hm := mul_le_mul_of_nonneg_right hr (sq_nonneg ‖weightedExpSum S w x (((i : ℝ) - j) / D)‖)
    dsimp [A]
    nlinarith
  rw [pairEnergy_fourier]
  exact matrix_band_lower H u A ((u : ℝ) ^ 2 / 128) (F ^ 2) (sq_nonneg F)
    (fun i hi j hj => hlow i j hi hj) (fun i hi j hj => hband i j hi hj)

#print axioms pairEnergy_lower_of_pole

end Erdos972KernelPoleLower
