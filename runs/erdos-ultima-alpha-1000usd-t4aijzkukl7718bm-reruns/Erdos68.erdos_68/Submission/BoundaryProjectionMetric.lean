import FormalConjecturesUtil

/-!
The real minimum-norm projection for a two-coordinate boundary map.
This is auxiliary geometry, not a proof or disproof of Erdős 68.
-/
namespace BoundaryProjectionMetric

open Finset

noncomputable def mean {D : ℕ} (B : Fin D → ℝ) : ℝ := (∑ i, B i) / D
noncomputable def centered {D : ℕ} (B : Fin D → ℝ) (i : Fin D) : ℝ :=
  B i - mean B
noncomputable def spread {D : ℕ} (B : Fin D → ℝ) : ℝ :=
  ∑ i, centered B i ^ 2
noncomputable def projection {D : ℕ} (B : Fin D → ℝ) (s b : ℝ) (i : Fin D) : ℝ :=
  s / D + (b - mean B * s) / spread B * centered B i

lemma centered_sum {D : ℕ} (B : Fin D → ℝ) (hD : 0 < D) :
    ∑ i, centered B i = 0 := by
  have hd : (D : ℝ) ≠ 0 := by positivity
  simp only [centered, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mean]
  field_simp
  ring

lemma centered_boundary_sum {D : ℕ} (B : Fin D → ℝ) (hD : 0 < D) :
    ∑ i, centered B i * B i = spread B := by
  have hz := centered_sum B hD
  calc
    _ = ∑ i, (centered B i ^ 2 + mean B * centered B i) := by
      apply sum_congr rfl
      intro i _
      dsimp [centered]
      ring
    _ = _ := by rw [sum_add_distrib, ← mul_sum, hz, mul_zero, add_zero]; rfl

lemma projection_sum {D : ℕ} (B : Fin D → ℝ) (hD : 0 < D) (s b : ℝ) :
    ∑ i, projection B s b i = s := by
  have hd : (D : ℝ) ≠ 0 := by positivity
  simp only [projection, sum_add_distrib, ← mul_sum, centered_sum B hD,
    mul_zero, add_zero, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma projection_boundary_sum {D : ℕ} (B : Fin D → ℝ) (hD : 0 < D)
    (hV : spread B ≠ 0) (s b : ℝ) :
    ∑ i, projection B s b i * B i = b := by
  have hd : (D : ℝ) ≠ 0 := by positivity
  have hsum : (∑ i, B i) = D * mean B := by
    dsimp [mean]
    field_simp
  simp only [projection, add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
  rw [centered_boundary_sum B hD, hsum]
  field_simp
  ring

/-- This expression concerns the orthogonal projection, not the norm of
an arbitrary integral lift of the pair. -/
theorem projection_norm_sq {D : ℕ} (B : Fin D → ℝ) (hD : 0 < D)
    (hV : spread B ≠ 0) (s b : ℝ) :
    (∑ i, projection B s b i ^ 2) =
      s^2 / D + (b - mean B * s)^2 / spread B := by
  have hd : (D : ℝ) ≠ 0 := by positivity
  calc
    _ = ∑ i, ((s / D)^2 +
        (2 * (s / D) * ((b - mean B * s) / spread B)) * centered B i +
        ((b - mean B * s) / spread B)^2 * centered B i ^ 2) := by
      apply sum_congr rfl
      intro i _
      dsimp [projection]
      ring
    _ = (D : ℝ) * (s / D)^2 +
        (2 * (s / D) * ((b - mean B * s) / spread B)) * (∑ i, centered B i) +
        ((b - mean B * s) / spread B)^2 * spread B := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, spread]
    _ = _ := by
      rw [centered_sum B hD]
      field_simp
      ring

lemma centered_weight_sum {D : ℕ} (B w : Fin D → ℝ) :
    (∑ i, w i * centered B i) =
      (∑ i, w i * B i) - mean B * (∑ i, w i) := by
  simp only [centered, mul_sub, sum_sub_distrib, ← sum_mul]
  ring

/-- The displayed projection minimizes squared norm among all real lifts
with the same two coordinates. -/
theorem projection_minimal {D : ℕ} (B w : Fin D → ℝ) (hD : 0 < D)
    (hV : spread B ≠ 0) (s b : ℝ)
    (hs : (∑ i, w i) = s) (hb : (∑ i, w i * B i) = b) :
    s^2 / D + (b - mean B * s)^2 / spread B ≤ ∑ i, w i ^ 2 := by
  let p := projection B s b
  have hps : (∑ i, p i) = s := projection_sum B hD s b
  have hpb : (∑ i, p i * B i) = b := projection_boundary_sum B hD hV s b
  have hrs : (∑ i, (w i - p i)) = 0 := by rw [sum_sub_distrib, hs, hps, sub_self]
  have hrb : (∑ i, (w i - p i) * B i) = 0 := by
    simp only [sub_mul, sum_sub_distrib, hb, hpb, sub_self]
  have hrc : (∑ i, (w i - p i) * centered B i) = 0 := by
    rw [centered_weight_sum, hrb, hrs]
    ring
  have horth : (∑ i, (w i - p i) * p i) = 0 := by
    change (∑ i, (w i - p i) *
      (s / D + (b - mean B * s) / spread B * centered B i)) = 0
    calc
      _ = (∑ i, (w i - p i)) * (s / D) +
          ((b - mean B * s) / spread B) *
            (∑ i, (w i - p i) * centered B i) := by
        simp only [sum_mul, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hrs, hrc]; ring
  have hid : (∑ i, w i ^ 2) = (∑ i, p i ^ 2) +
      2 * (∑ i, (w i - p i) * p i) + (∑ i, (w i - p i)^2) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hn : 0 ≤ ∑ i, (w i - p i)^2 := sum_nonneg (fun i _ => sq_nonneg _)
  rw [hid, horth, mul_zero, add_zero]
  rw [show (∑ i, p i ^ 2) = s^2 / D + (b - mean B * s)^2 / spread B from
    projection_norm_sq B hD hV s b]
  linarith

/-- Under a rational value, the natural integer pair has this projected
norm. The large retained coefficient A cancels from the discrepancy. -/
theorem rational_pair_projection {D : ℕ} (B : Fin D → ℝ) (hD : 0 < D)
    (hV : spread B ≠ 0) (A : ℤ) (q : ℚ) :
    (∑ i, projection B (q.den : ℝ) ((A * q.num : ℤ) : ℝ) i ^ 2) =
      (q.den : ℝ)^2 * (1 / D + ((A : ℝ) * (q : ℝ) - mean B)^2 / spread B) := by
  rw [projection_norm_sq B hD hV]
  have hq : (q.num : ℝ) = (q.den : ℝ) * (q : ℝ) := by
    have he := Rat.cast_def q (K := ℝ)
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [he]
    field_simp
  simp only [Int.cast_mul]
  rw [hq]
  ring

/-- The elementary integer estimate behind the two-dimensional Gauss
shortest-vector certificate. -/
lemma integer_binary_bound (m n : ℤ) (h : m ≠ 0 ∨ n ≠ 0) :
    (1 : ℝ) ≤ (m : ℝ)^2 + (n : ℝ)^2 - |(m : ℝ) * (n : ℝ)| := by
  have habs (k : ℤ) (hk : k ≠ 0) : (1 : ℝ) ≤ |(k : ℝ)| := by
    exact_mod_cast Int.one_le_abs hk
  by_cases hm : m = 0
  · have hn : n ≠ 0 := h.resolve_left (by simp [hm])
    have hh := habs n hn
    simp only [hm, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul,
      abs_zero, zero_add, sub_zero]
    nlinarith [sq_abs (n : ℝ)]
  · by_cases hn : n = 0
    · have hh := habs m hm
      simp only [hn, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
        abs_zero, add_zero, sub_zero]
      nlinarith [sq_abs (m : ℝ)]
    · have hh := habs m hm
      have hk := habs n hn
      rw [abs_mul]
      nlinarith [sq_nonneg (|(m : ℝ)| - |(n : ℝ)|),
        sq_abs (m : ℝ), sq_abs (n : ℝ)]

/-- If a positive binary quadratic form is Gauss-reduced, its first basis
vector is a shortest nonzero integer vector. This inequality is the part
of that assertion independent of a change of integral basis. -/
theorem reduced_binary_form_bound (a b c : ℝ) (ha : 0 ≤ a)
    (hac : a ≤ c) (hb : 2 * |b| ≤ a) (m n : ℤ) (h : m ≠ 0 ∨ n ≠ 0) :
    a ≤ a * (m : ℝ)^2 + 2*b*(m : ℝ)*(n : ℝ) + c*(n : ℝ)^2 := by
  have hi := mul_le_mul_of_nonneg_left (integer_binary_bound m n h) ha
  have hn := mul_le_mul_of_nonneg_right hac (sq_nonneg (n : ℝ))
  have hmul := mul_le_mul_of_nonneg_right hb (abs_nonneg ((m : ℝ)*(n : ℝ)))
  have hcross : -a * |(m : ℝ)*(n : ℝ)| ≤ 2*b*(m : ℝ)*(n : ℝ) := by
    have hh := neg_abs_le (2*b*(m : ℝ)*(n : ℝ))
    have he : |2*b*(m : ℝ)*(n : ℝ)| = 2 * |b| *|(m : ℝ)*(n : ℝ)| := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [he] at hh
    linarith
  nlinarith

end BoundaryProjectionMetric

#print axioms BoundaryProjectionMetric.projection_norm_sq
#print axioms BoundaryProjectionMetric.projection_minimal
#print axioms BoundaryProjectionMetric.rational_pair_projection

#print axioms BoundaryProjectionMetric.reduced_binary_form_bound
