import FormalConjecturesUtil

/-! The exact norm criterion for the quadratic-factor eight-point template. -/

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Erdos213.QuadraticTemplate

/-- A complex number whose Euclidean norm is rational. -/
def RationalNorm (z : ℂ) : Prop := ∃ q : ℚ, (q : ℝ) = ‖z‖

lemma RationalNorm.mul {a b : ℂ} (ha : RationalNorm a) (hb : RationalNorm b) :
    RationalNorm (a * b) := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  exact ⟨r*s, by simp [hr, hs]⟩

lemma RationalNorm.div {a b : ℂ} (ha : RationalNorm a) (hb : RationalNorm b) :
    RationalNorm (a / b) := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  exact ⟨r/s, by simp [hr, hs]⟩

lemma RationalNorm.pow {a : ℂ} (ha : RationalNorm a) (n : ℕ) :
    RationalNorm (a ^ n) := by
  obtain ⟨r, hr⟩ := ha
  exact ⟨r^n, by simp [hr, norm_pow]⟩

lemma RationalNorm.inv {a : ℂ} (ha : RationalNorm a) : RationalNorm a⁻¹ := by
  obtain ⟨r, hr⟩ := ha
  exact ⟨r⁻¹, by simp [hr]⟩

lemma RationalNorm.neg {a : ℂ} (ha : RationalNorm a) : RationalNorm (-a) := by
  simpa [RationalNorm] using ha

lemma RationalNorm.int (a : ℤ) : RationalNorm (a : ℂ) := by
  refine ⟨(a.natAbs : ℚ), ?_⟩
  simp

noncomputable def point (t : ℂ) : Fin 8 → ℂ :=
  ![0, 1-t^2, (t+2)^2/3, t+2, (t+2)*(t+1), t+1, 2*t+1, t^2+t+1]

lemma rational_pair_differences (t : ℂ)
    (h0 : RationalNorm t)
    (hp1 : RationalNorm (t+1)) (hm1 : RationalNorm (t-1))
    (hp2 : RationalNorm (t+2)) (h2p1 : RationalNorm (2*t+1))
    (hQ : RationalNorm (t^2+t+1)) :
    ∀ i j : Fin 8, i < j → RationalNorm (point t j - point t i) := by
  have hc1 : RationalNorm (1 : ℂ) := by simpa using RationalNorm.int 1
  have hc3 : RationalNorm (3 : ℂ) := by simpa using RationalNorm.int 3
  have hcm1 : RationalNorm (-1 : ℂ) := by simpa using RationalNorm.int (-1)
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · change RationalNorm (point t 1 - point t 0)
    have he : point t 1 - point t 0 = (-1 * (t-1) * (t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul (RationalNorm.mul hcm1 hm1) hp1)
  · change RationalNorm (point t 2 - point t 0)
    have he : point t 2 - point t 0 = ((((t+2) ^ 2)) / (3)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.div (RationalNorm.pow hp2 2) hc3)
  · change RationalNorm (point t 3 - point t 0)
    have he : point t 3 - point t 0 = ((t+2)) := by
      dsimp [point]
      ring
    rw [he]
    exact hp2
  · change RationalNorm (point t 4 - point t 0)
    have he : point t 4 - point t 0 = ((t+1) * (t+2)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul hp1 hp2)
  · change RationalNorm (point t 5 - point t 0)
    have he : point t 5 - point t 0 = ((t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact hp1
  · change RationalNorm (point t 6 - point t 0)
    have he : point t 6 - point t 0 = ((2*t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact h2p1
  · change RationalNorm (point t 7 - point t 0)
    have he : point t 7 - point t 0 = ((t^2+t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact hQ
  · change RationalNorm (point t 2 - point t 1)
    have he : point t 2 - point t 1 = ((((2*t+1) ^ 2)) / (3)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.div (RationalNorm.pow h2p1 2) hc3)
  · change RationalNorm (point t 3 - point t 1)
    have he : point t 3 - point t 1 = ((t^2+t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact hQ
  · change RationalNorm (point t 4 - point t 1)
    have he : point t 4 - point t 1 = ((t+1) * (2*t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul hp1 h2p1)
  · change RationalNorm (point t 5 - point t 1)
    have he : point t 5 - point t 1 = (t * (t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul h0 hp1)
  · change RationalNorm (point t 6 - point t 1)
    have he : point t 6 - point t 1 = (t * (t+2)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul h0 hp2)
  · change RationalNorm (point t 7 - point t 1)
    have he : point t 7 - point t 1 = (t * (2*t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul h0 h2p1)
  · change RationalNorm (point t 3 - point t 2)
    have he : point t 3 - point t 2 = ((-1 * (t-1) * (t+2)) / (3)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.div (RationalNorm.mul (RationalNorm.mul hcm1 hm1) hp2) hc3)
  · change RationalNorm (point t 4 - point t 2)
    have he : point t 4 - point t 2 = (((t+2) * (2*t+1)) / (3)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.div (RationalNorm.mul hp2 h2p1) hc3)
  · change RationalNorm (point t 5 - point t 2)
    have he : point t 5 - point t 2 = ((-1 * (t^2+t+1)) / (3)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.div (RationalNorm.mul hcm1 hQ) hc3)
  · change RationalNorm (point t 6 - point t 2)
    have he : point t 6 - point t 2 = ((-1 * ((t-1) ^ 2)) / (3)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.div (RationalNorm.mul hcm1 (RationalNorm.pow hm1 2)) hc3)
  · change RationalNorm (point t 7 - point t 2)
    have he : point t 7 - point t 2 = (((t-1) * (2*t+1)) / (3)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.div (RationalNorm.mul hm1 h2p1) hc3)
  · change RationalNorm (point t 4 - point t 3)
    have he : point t 4 - point t 3 = (t * (t+2)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul h0 hp2)
  · change RationalNorm (point t 5 - point t 3)
    have he : point t 5 - point t 3 = (-1) := by
      dsimp [point]
      ring
    rw [he]
    exact hcm1
  · change RationalNorm (point t 6 - point t 3)
    have he : point t 6 - point t 3 = ((t-1)) := by
      dsimp [point]
      ring
    rw [he]
    exact hm1
  · change RationalNorm (point t 7 - point t 3)
    have he : point t 7 - point t 3 = ((t-1) * (t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul hm1 hp1)
  · change RationalNorm (point t 5 - point t 4)
    have he : point t 5 - point t 4 = (-1 * ((t+1) ^ 2)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul hcm1 (RationalNorm.pow hp1 2))
  · change RationalNorm (point t 6 - point t 4)
    have he : point t 6 - point t 4 = (-1 * (t^2+t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul hcm1 hQ)
  · change RationalNorm (point t 7 - point t 4)
    have he : point t 7 - point t 4 = (-1 * (2*t+1)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul hcm1 h2p1)
  · change RationalNorm (point t 6 - point t 5)
    have he : point t 6 - point t 5 = (t) := by
      dsimp [point]
      ring
    rw [he]
    exact h0
  · change RationalNorm (point t 7 - point t 5)
    have he : point t 7 - point t 5 = ((t ^ 2)) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.pow h0 2)
  · change RationalNorm (point t 7 - point t 6)
    have he : point t 7 - point t 6 = ((t-1) * t) := by
      dsimp [point]
      ring
    rw [he]
    exact (RationalNorm.mul hm1 h0)

/-- These six norm conditions are necessary, not just a sufficient list of factors. -/
lemma all_pairwise_norms_iff (t : ℂ) :
    (∀ i j : Fin 8, RationalNorm (point t j - point t i)) ↔
      RationalNorm t ∧ RationalNorm (t+1) ∧ RationalNorm (t-1) ∧
      RationalNorm (t+2) ∧ RationalNorm (2*t+1) ∧ RationalNorm (t^2+t+1) := by
  constructor
  · intro h
    have h0 : RationalNorm t := by
      have he : point t 6 - point t 5 = t := by dsimp [point]; ring
      simpa only [he] using h 5 6
    have hp1 : RationalNorm (t+1) := by simpa [point] using h 0 5
    have hm1 : RationalNorm (t-1) := by
      have he : point t 6 - point t 3 = t-1 := by dsimp [point]; ring
      simpa only [he] using h 3 6
    exact ⟨h0, hp1, hm1, by simpa [point] using h 0 3,
      by simpa [point] using h 0 6, by simpa [point] using h 0 7⟩
  · rintro ⟨h0, hp1, hm1, hp2, h2p1, hQ⟩ i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact rational_pair_differences t h0 hp1 hm1 hp2 h2p1 hQ i j hij
    · exact ⟨0, by simp⟩
    · simpa only [neg_sub] using
        (rational_pair_differences t h0 hp1 hm1 hp2 h2p1 hQ j i hji).neg

lemma rational_distances_iff (t : ℂ) :
    (∀ i j : Fin 8, ∃ q : ℚ, (q : ℝ) = dist (point t i) (point t j)) ↔
      RationalNorm t ∧ RationalNorm (t+1) ∧ RationalNorm (t-1) ∧
      RationalNorm (t+2) ∧ RationalNorm (2*t+1) ∧ RationalNorm (t^2+t+1) := by
  simpa only [RationalNorm, dist_eq_norm', eq_comm] using all_pairwise_norms_iff t

lemma rationalNorm_iff_normSq (z : ℂ) :
    RationalNorm z ↔ ∃ q : ℚ, Complex.normSq z = (q : ℝ)^2 := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, by rw [Complex.normSq_eq_norm_sq, hq]⟩
  · rintro ⟨q, hq⟩
    refine ⟨|q|, ?_⟩
    rw [Rat.cast_abs]
    apply (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
    rw [sq_abs, ← Complex.normSq_eq_norm_sq, hq]

lemma rationalNorm_iff_isSquare {z : ℂ} {r : ℚ}
    (hr : Complex.normSq z = (r : ℝ)) :
    RationalNorm z ↔ IsSquare r := by
  rw [rationalNorm_iff_normSq]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have he : (r : ℝ) = (q : ℝ)^2 := hr ▸ hq
    exact_mod_cast (he.trans (pow_two (q : ℝ)))
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [hr, hq]
    push_cast
    ring

lemma quadratic_norm_identity (t : ℂ) :
    Complex.normSq (t^2+t+1) =
      Complex.normSq t ^ 2 + Complex.normSq (t+1) ^ 2 + 1 -
        Complex.normSq t * Complex.normSq (t+1) -
        Complex.normSq t - Complex.normSq (t+1) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    pow_two, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im]
  ring

/-- In side-length coordinates, the extra condition is a single explicit quartic square. -/
lemma extra_norm_iff_discriminant (t : ℂ) (a c : ℚ)
    (ha : Complex.normSq t = (a : ℝ)^2)
    (hc : Complex.normSq (t+1) = (c : ℝ)^2) :
    RationalNorm (t^2+t+1) ↔
      IsSquare (a^4 + c^4 + 1 - a^2*c^2 - a^2 - c^2) := by
  apply rationalNorm_iff_isSquare
  rw [quadratic_norm_identity, ha, hc]
  push_cast
  ring

noncomputable def oldParameter : ℂ :=
  ⟨-29493/41905, (-696/41905)*Real.sqrt 2002⟩

lemma oldParameter_normSq_zero : Complex.normSq oldParameter = (87/85 : ℝ)^2 := by
  have hs : Real.sqrt 2002 ^ 2 = 2002 := Real.sq_sqrt (by norm_num)
  simp only [oldParameter, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat]
  nlinarith [hs]

lemma oldParameter_normSq_plus_one : Complex.normSq (oldParameter+1) = (68/85 : ℝ)^2 := by
  have hs : Real.sqrt 2002 ^ 2 = 2002 := Real.sq_sqrt (by norm_num)
  simp only [oldParameter, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat]
  nlinarith [hs]

lemma oldParameter_normSq_minus_one : Complex.normSq (oldParameter-1) = (158/85 : ℝ)^2 := by
  have hs : Real.sqrt 2002 ^ 2 = 2002 := Real.sq_sqrt (by norm_num)
  simp only [oldParameter, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat]
  nlinarith [hs]

lemma oldParameter_normSq_plus_two : Complex.normSq (oldParameter+2) = (127/85 : ℝ)^2 := by
  have hs : Real.sqrt 2002 ^ 2 = 2002 := Real.sq_sqrt (by norm_num)
  simp only [oldParameter, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat]
  nlinarith [hs]

lemma oldParameter_normSq_double_plus_one : Complex.normSq (2*oldParameter+1) = (131/85 : ℝ)^2 := by
  have hs : Real.sqrt 2002 ^ 2 = 2002 := Real.sq_sqrt (by norm_num)
  simp only [oldParameter, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat]
  nlinarith [hs]

lemma oldParameter_norms :
    RationalNorm oldParameter ∧ RationalNorm (oldParameter+1) ∧
    RationalNorm (oldParameter-1) ∧ RationalNorm (oldParameter+2) ∧
    RationalNorm (2*oldParameter+1) := by
  exact ⟨rationalNorm_iff_normSq _ |>.mpr ⟨87/85, by norm_num [oldParameter_normSq_zero]⟩,
    rationalNorm_iff_normSq _ |>.mpr ⟨68/85, by norm_num [oldParameter_normSq_plus_one]⟩,
    rationalNorm_iff_normSq _ |>.mpr ⟨158/85, by norm_num [oldParameter_normSq_minus_one]⟩,
    rationalNorm_iff_normSq _ |>.mpr ⟨127/85, by norm_num [oldParameter_normSq_plus_two]⟩,
    rationalNorm_iff_normSq _ |>.mpr ⟨131/85, by norm_num [oldParameter_normSq_double_plus_one]⟩⟩

lemma oldParameter_extra_normSq :
    Complex.normSq (oldParameter^2+oldParameter+1) = (7778281/52200625 : ℝ) := by
  rw [quadratic_norm_identity, oldParameter_normSq_zero, oldParameter_normSq_plus_one]
  norm_num

lemma oldParameter_extra_not_rational : ¬ RationalNorm (oldParameter^2+oldParameter+1) := by
  rw [rationalNorm_iff_isSquare
    (r := 7778281/52200625) (by norm_num; exact oldParameter_extra_normSq)]
  norm_num

lemma oldParameter_not_eight_rational_points :
    ¬ (∀ i j : Fin 8, ∃ q : ℚ, (q : ℝ) = dist (point oldParameter i) (point oldParameter j)) := by
  intro h
  exact oldParameter_extra_not_rational ((rational_distances_iff oldParameter).mp h).2.2.2.2.2

/-- The primitive cube roots cannot satisfy even the `t-1` length condition. -/
lemma quadratic_ne_zero (t : ℂ) (ht : t.im ≠ 0) (hm1 : RationalNorm (t-1)) :
    t^2+t+1 ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im] at hr hi
  have hprod : (2*t.re+1)*t.im = 0 := by linear_combination hi
  have hx : t.re = -1/2 := by
    have hh := (mul_eq_zero.mp hprod).resolve_right ht
    linarith
  have hn : Complex.normSq (t-1) = 3 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    rw [hx] at hr ⊢
    nlinarith
  have hbad : IsSquare (3 : ℚ) :=
    (rationalNorm_iff_isSquare (r := 3) (by simpa using hn)).mp hm1
  norm_num at hbad

lemma point_injective (t : ℂ) (ht : t.im ≠ 0) (hm1 : RationalNorm (t-1)) :
    Function.Injective (point t) := by
  have hnQ := quadratic_ne_zero t ht hm1
  have hn0 : t ≠ 0 := by
    intro h
    exact ht (by simp [h])
  have hnp1 : t+1 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnm1 : t-1 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnp2 : t+2 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hn2p1 : 2*t+1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    exact ht (by linarith)
  have hdiff : ∀ i j : Fin 8, i < j → point t j - point t i ≠ 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · change point t 1 - point t 0 ≠ 0
      have he : point t 1 - point t 0 = (-1 * (t-1) * (t+1)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) hnm1) hnp1)
    · change point t 2 - point t 0 ≠ 0
      have he : point t 2 - point t 0 = ((((t+2) ^ 2)) / (3)) := by dsimp [point]; ring
      rw [he]
      exact (div_ne_zero (pow_ne_zero 2 hnp2) (by norm_num : (3 : ℂ) ≠ 0))
    · change point t 3 - point t 0 ≠ 0
      have he : point t 3 - point t 0 = ((t+2)) := by dsimp [point]; ring
      rw [he]
      exact hnp2
    · change point t 4 - point t 0 ≠ 0
      have he : point t 4 - point t 0 = ((t+1) * (t+2)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero hnp1 hnp2)
    · change point t 5 - point t 0 ≠ 0
      have he : point t 5 - point t 0 = ((t+1)) := by dsimp [point]; ring
      rw [he]
      exact hnp1
    · change point t 6 - point t 0 ≠ 0
      have he : point t 6 - point t 0 = ((2*t+1)) := by dsimp [point]; ring
      rw [he]
      exact hn2p1
    · change point t 7 - point t 0 ≠ 0
      have he : point t 7 - point t 0 = ((t^2+t+1)) := by dsimp [point]; ring
      rw [he]
      exact hnQ
    · change point t 2 - point t 1 ≠ 0
      have he : point t 2 - point t 1 = ((((2*t+1) ^ 2)) / (3)) := by dsimp [point]; ring
      rw [he]
      exact (div_ne_zero (pow_ne_zero 2 hn2p1) (by norm_num : (3 : ℂ) ≠ 0))
    · change point t 3 - point t 1 ≠ 0
      have he : point t 3 - point t 1 = ((t^2+t+1)) := by dsimp [point]; ring
      rw [he]
      exact hnQ
    · change point t 4 - point t 1 ≠ 0
      have he : point t 4 - point t 1 = ((t+1) * (2*t+1)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero hnp1 hn2p1)
    · change point t 5 - point t 1 ≠ 0
      have he : point t 5 - point t 1 = (t * (t+1)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero hn0 hnp1)
    · change point t 6 - point t 1 ≠ 0
      have he : point t 6 - point t 1 = (t * (t+2)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero hn0 hnp2)
    · change point t 7 - point t 1 ≠ 0
      have he : point t 7 - point t 1 = (t * (2*t+1)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero hn0 hn2p1)
    · change point t 3 - point t 2 ≠ 0
      have he : point t 3 - point t 2 = ((-1 * (t-1) * (t+2)) / (3)) := by dsimp [point]; ring
      rw [he]
      exact (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) hnm1) hnp2) (by norm_num : (3 : ℂ) ≠ 0))
    · change point t 4 - point t 2 ≠ 0
      have he : point t 4 - point t 2 = (((t+2) * (2*t+1)) / (3)) := by dsimp [point]; ring
      rw [he]
      exact (div_ne_zero (mul_ne_zero hnp2 hn2p1) (by norm_num : (3 : ℂ) ≠ 0))
    · change point t 5 - point t 2 ≠ 0
      have he : point t 5 - point t 2 = ((-1 * (t^2+t+1)) / (3)) := by dsimp [point]; ring
      rw [he]
      exact (div_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) hnQ) (by norm_num : (3 : ℂ) ≠ 0))
    · change point t 6 - point t 2 ≠ 0
      have he : point t 6 - point t 2 = ((-1 * ((t-1) ^ 2)) / (3)) := by dsimp [point]; ring
      rw [he]
      exact (div_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) (pow_ne_zero 2 hnm1)) (by norm_num : (3 : ℂ) ≠ 0))
    · change point t 7 - point t 2 ≠ 0
      have he : point t 7 - point t 2 = (((t-1) * (2*t+1)) / (3)) := by dsimp [point]; ring
      rw [he]
      exact (div_ne_zero (mul_ne_zero hnm1 hn2p1) (by norm_num : (3 : ℂ) ≠ 0))
    · change point t 4 - point t 3 ≠ 0
      have he : point t 4 - point t 3 = (t * (t+2)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero hn0 hnp2)
    · change point t 5 - point t 3 ≠ 0
      have he : point t 5 - point t 3 = (-1) := by dsimp [point]; ring
      rw [he]
      exact (by norm_num : (-1 : ℂ) ≠ 0)
    · change point t 6 - point t 3 ≠ 0
      have he : point t 6 - point t 3 = ((t-1)) := by dsimp [point]; ring
      rw [he]
      exact hnm1
    · change point t 7 - point t 3 ≠ 0
      have he : point t 7 - point t 3 = ((t-1) * (t+1)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero hnm1 hnp1)
    · change point t 5 - point t 4 ≠ 0
      have he : point t 5 - point t 4 = (-1 * ((t+1) ^ 2)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) (pow_ne_zero 2 hnp1))
    · change point t 6 - point t 4 ≠ 0
      have he : point t 6 - point t 4 = (-1 * (t^2+t+1)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) hnQ)
    · change point t 7 - point t 4 ≠ 0
      have he : point t 7 - point t 4 = (-1 * (2*t+1)) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) hn2p1)
    · change point t 6 - point t 5 ≠ 0
      have he : point t 6 - point t 5 = (t) := by dsimp [point]; ring
      rw [he]
      exact hn0
    · change point t 7 - point t 5 ≠ 0
      have he : point t 7 - point t 5 = ((t ^ 2)) := by dsimp [point]; ring
      rw [he]
      exact (pow_ne_zero 2 hn0)
    · change point t 7 - point t 6 ≠ 0
      have he : point t 7 - point t 6 = ((t-1) * t) := by dsimp [point]; ring
      rw [he]
      exact (mul_ne_zero hnm1 hn0)
  intro i j he
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim (hdiff i j hij (sub_eq_zero.mpr he.symm))
  · exact hij
  · exact False.elim (hdiff j i hji (sub_eq_zero.mpr he))

private lemma collinear_of_det_zero {a b c : ℂ}
    (hz : (b-a).re*(c-a).im - (b-a).im*(c-a).re = 0) :
    Collinear ℝ {a,b,c} := by
  by_cases hab : b = a
  · subst b
    simpa using (collinear_pair ℝ a c)
  have hv : b-a ≠ 0 := sub_ne_zero.mpr hab
  have hdiv : ((c-a)/(b-a)).im = 0 := by
    rw [Complex.div_im]
    have hn : (c-a).im*(b-a).re-(c-a).re*(b-a).im = 0 := by
      linear_combination hz
    rw [← sub_div, hn, zero_div]
  let r : ℝ := ((c-a)/(b-a)).re
  have he : (c-a)/(b-a) = (r : ℂ) := by
    apply Complex.ext <;> simp [r, hdiv]
  have he' : c = r • (b-a) + a := by
    have hmul := (div_eq_iff hv).mp he
    rw [Complex.real_smul]
    linear_combination hmul
  rw [collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℂ))]
  refine ⟨b-a, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨r, he'⟩

lemma vertical_symmetry_collinear (t : ℂ) (ht : t.re = -1/2) :
    Collinear ℝ {point t 1, point t 3, point t 5} := by
  apply collinear_of_det_zero
  dsimp [point]
  simp only [pow_two, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
  rw [ht]
  ring

lemma unit_circle_collinear (t : ℂ) (ht : Complex.normSq t = 1) :
    Collinear ℝ {point t 4, point t 5, point t 6} := by
  apply collinear_of_det_zero
  dsimp [point]
  simp only [Complex.normSq_apply] at ht
  linear_combination t.im * ht

lemma shifted_unit_circle_collinear (t : ℂ) (ht : Complex.normSq (t+1) = 1) :
    Collinear ℝ {point t 0, point t 5, point t 7} := by
  apply collinear_of_det_zero
  dsimp [point]
  simp only [pow_two, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im] at ht
  linear_combination t.im * ht

/-- The three isosceles specializations cannot provide a general-position witness. -/
lemma symmetric_not_nontrilinear (t : ℂ) (ht : t.im ≠ 0) (hm1 : RationalNorm (t-1))
    (hsym : t.re = -1/2 ∨ Complex.normSq t = 1 ∨ Complex.normSq (t+1) = 1) :
    ¬ EuclideanGeometry.NonTrilinear (Set.range (point t)) := by
  intro h
  have hi := point_injective t ht hm1
  rcases hsym with hs | hs | hs
  · exact h (Set.mem_range_self 1) (Set.mem_range_self 3) (Set.mem_range_self 5)
      (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
      (vertical_symmetry_collinear t hs)
  · exact h (Set.mem_range_self 4) (Set.mem_range_self 5) (Set.mem_range_self 6)
      (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
      (unit_circle_collinear t hs)
  · exact h (Set.mem_range_self 0) (Set.mem_range_self 5) (Set.mem_range_self 7)
      (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))
      (shifted_unit_circle_collinear t hs)

#print axioms all_pairwise_norms_iff
#print axioms extra_norm_iff_discriminant
#print axioms oldParameter_norms
#print axioms oldParameter_not_eight_rational_points
#print axioms point_injective
#print axioms symmetric_not_nontrilinear

end Erdos213.QuadraticTemplate
