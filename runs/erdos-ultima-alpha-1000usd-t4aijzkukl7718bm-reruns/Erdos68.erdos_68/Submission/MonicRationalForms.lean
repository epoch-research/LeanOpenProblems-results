import Submission.RisingMonicForms

/-!
A fixed monic denominator in the rising-factorial construction does not
supply new row values: its forms reduce to integer-polynomial forms.
This is auxiliary analysis, not a settlement of Erdős 68.
-/
namespace MonicRationalForms

open Polynomial RisingMonicForms Erdos68Development

lemma quotient_product (P Q R : Polynomial ℤ) (hQ : Q.Monic) (hR : R.Monic) :
    P /ₘ (Q*R) = (P /ₘ Q) /ₘ R := by
  apply (div_modByMonic_unique ((P /ₘ Q) /ₘ R)
    (P %ₘ Q + Q*((P /ₘ Q) %ₘ R)) (hQ.mul hR) ?_).1
  constructor
  · have h1 := modByMonic_add_div P hQ
    have h2 := modByMonic_add_div (P /ₘ Q) hR
    calc
      _ = P %ₘ Q + Q*(((P /ₘ Q) %ₘ R)+R*((P /ₘ Q) /ₘ R)) := by ring
      _ = P := by rw [h2, h1]
  · apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt_iff.mpr
    rw [degree_mul]
    constructor
    · apply (degree_modByMonic_lt P hQ).trans_le
      rw [degree_eq_natDegree hQ.ne_zero, degree_eq_natDegree hR.ne_zero]
      norm_cast
      omega
    · rw [degree_mul]
      have h := degree_modByMonic_lt (P /ₘ Q) hR
      rw [degree_eq_natDegree hQ.ne_zero]
      exact WithBot.add_lt_add_left (by simp) h

lemma quotient_add_constant (H : Polynomial ℤ) (c : ℤ) (n : ℕ) :
    (H+C c) /ₘ rowPolynomial n = H /ₘ rowPolynomial n := by
  apply (div_modByMonic_unique (H /ₘ rowPolynomial n)
    (H %ₘ rowPolynomial n+C c) (rowPolynomial_monic n) ?_).1
  constructor
  · have h := modByMonic_add_div H (rowPolynomial_monic n)
    linear_combination h
  · apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt_iff.mpr
    refine ⟨degree_modByMonic_lt H (rowPolynomial_monic n), ?_⟩
    apply degree_lt_degree
    rw [natDegree_C, rowPolynomial_natDegree]
    omega

/-- Every quotient contribution of a fixed monic rational auxiliary function
is reproduced by an integer polynomial, when its retained value is integral. -/
theorem polynomial_replacement (P Q : Polynomial ℤ) (hQ : Q.Monic)
    (A : ℤ) :
    ∃ H : Polynomial ℤ, H.eval 1 = A ∧
      ∀ n : ℕ, H /ₘ rowPolynomial n = P /ₘ (Q*rowPolynomial n) := by
  let H := P /ₘ Q
  refine ⟨H+C (A-H.eval 1), ?_, ?_⟩
  · simp
  · intro n
    rw [quotient_add_constant, quotient_product P Q (rowPolynomial n) hQ (rowPolynomial_monic n)]

/-- The equivalent row values form the same convergent integer linear form.
No smallness or nonvanishing is asserted. -/
theorem hasSum_rational_rows (P Q : Polynomial ℤ) (hQ : Q.Monic)
    (hQ1 : Q.eval 1 ≠ 0) (A : ℤ) (hA : P.eval 1 = A*Q.eval 1) :
    ∃ B : ℤ, HasSum
      (fun n : ℕ => (((P.eval 1:ℤ):ℝ)/((Q.eval 1:ℤ):ℝ))*term n-
        (((P /ₘ (Q*rowPolynomial n)).eval 1:ℤ):ℝ))
      ((A:ℝ)*(∑' n : ℕ, term n)-B) := by
  have hval : ((P.eval 1:ℤ):ℝ)/((Q.eval 1:ℤ):ℝ) = (A:ℝ) := by
    rw [hA, Int.cast_mul]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast hQ1)
  rw [hval]
  obtain ⟨H, hH, hquot⟩ := polynomial_replacement P Q hQ A
  refine ⟨boundary H, ?_⟩
  have hs := hasSum_residueRows H
  rw [hH] at hs
  convert hs using 1
  funext n
  rw [row_identity, hH, hquot n]

#print axioms quotient_product
#print axioms polynomial_replacement
#print axioms hasSum_rational_rows

end MonicRationalForms
