import FormalConjecturesUtil

/-!
# An integer-matrix determinant criterion

This auxiliary criterion is not a proof of Erdős 68. A family satisfying
its hypotheses for the factorial-minus-one sum has not been constructed.
The exponent in the smallness condition is essential: merely making the
positive determinants tend to zero, with growing matrix sizes, does not
suffice.
-/

namespace PositiveMatrixCriterion

noncomputable def pencil {d : ℕ} (x : ℝ) (A B : Matrix (Fin d) (Fin d) ℤ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => x * (A i j : ℝ) - (B i j : ℝ)

lemma scaled_rational_det (r : ℚ) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℤ) :
    (r.den : ℝ) ^ d * (pencil (r : ℝ) A B).det =
      ((Matrix.det (fun i j => r.num * A i j - (r.den : ℤ) * B i j) : ℤ) : ℝ) := by
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
  have hr : (r.den : ℝ) * (r : ℝ) = r.num := by
    rw [Rat.cast_def]
    field_simp
  rw [Int.cast_det]
  have hm : (r.den : ℝ) • pencil (r : ℝ) A B =
      Matrix.map (fun i j => r.num * A i j - (r.den : ℤ) * B i j)
        (fun z : ℤ => (z : ℝ)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, pencil, Matrix.map_apply,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [mul_sub, ← mul_assoc, hr]
  rw [← hm, Matrix.det_smul, Fintype.card_fin]

lemma rational_positive_det_lower_bound (r : ℚ) {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℤ)
    (hpos : 0 < (pencil (r : ℝ) A B).det) :
    (1 / (r.den : ℝ)) ^ d ≤ (pencil (r : ℝ) A B).det := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  let z : ℤ := Matrix.det (fun i j => r.num * A i j - (r.den : ℤ) * B i j)
  have hz : (r.den : ℝ) ^ d * (pencil (r : ℝ) A B).det = (z : ℝ) :=
    scaled_rational_det r A B
  have hzpos : 0 < z := by
    have : (0 : ℝ) < z := by rw [← hz]; positivity
    exact_mod_cast this
  have hzge : (1 : ℝ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  have hmul : (r.den : ℝ) ^ d * (1 / (r.den : ℝ)) ^ d = 1 := by
    rw [← mul_pow]
    simp [hd.ne']
  apply (mul_le_mul_iff_right₀ (pow_pos hd d)).mp
  rw [hmul, hz]
  exact hzge

/-- The sizes can vary. Positivity supplies nonvanishing, and the size-relative
bound supplies the rational-denominator contradiction. No matrix family for
the original conjecture is asserted here. -/
theorem irrational_of_positive_small_determinants (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℤ),
      0 < (pencil x A B).det ∧ (pencil x A B).det < ε ^ d) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  obtain ⟨d, A, B, hp, hs⟩ := h (1 / (r.den : ℝ)) (by positivity)
  exact (not_lt_of_ge (rational_positive_det_lower_bound r A B hp)) hs

/-- At a rational number, positive determinants can still tend to zero if
matrix size grows. This example attains the rational lower bound exactly. -/
lemma half_identity_det (d : ℕ) :
    (pencil (1 / 2) (1 : Matrix (Fin d) (Fin d) ℤ) 0).det =
      (1 / 2 : ℝ) ^ d := by
  have hm : pencil (1 / 2) (1 : Matrix (Fin d) (Fin d) ℤ) 0 =
      (1 / 2 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [pencil]
    · simp [pencil, hij]
  rw [hm, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]

lemma rational_example_positive_det_tendsto :
    (∀ d : ℕ, 0 < (pencil (1 / 2) (1 : Matrix (Fin d) (Fin d) ℤ) 0).det) ∧
    Filter.Tendsto
      (fun d : ℕ => (pencil (1 / 2) (1 : Matrix (Fin d) (Fin d) ℤ) 0).det)
      Filter.atTop (nhds 0) := by
  simp only [half_identity_det]
  constructor
  · intro d
    positivity
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end PositiveMatrixCriterion

#print axioms PositiveMatrixCriterion.scaled_rational_det
#print axioms PositiveMatrixCriterion.rational_positive_det_lower_bound
#print axioms PositiveMatrixCriterion.irrational_of_positive_small_determinants

#print axioms PositiveMatrixCriterion.rational_example_positive_det_tendsto
