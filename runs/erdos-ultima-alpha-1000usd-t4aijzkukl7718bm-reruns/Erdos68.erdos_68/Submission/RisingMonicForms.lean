import Submission.Development

/-!
# Integer-boundary forms from monic rising-factorial polynomials

These exact identities do not settle Erdős 68. A useful family would still
need nonvanishing and a bound forcing its errors to tend to zero.
-/

namespace RisingMonicForms

open Polynomial Erdos68Development

/-- In mathematical indices this is R_(n+1)(X). -/
noncomputable def rowPolynomial (n : ℕ) : Polynomial ℤ :=
  (ascPochhammer ℤ (n + 1)).comp (X + C 1) - C 1

lemma rowPolynomial_natDegree (n : ℕ) : (rowPolynomial n).natDegree = n + 1 := by
  rw [rowPolynomial, natDegree_sub_C, natDegree_comp,
    natDegree_X_add_C, ascPochhammer_natDegree, mul_one]

lemma rowPolynomial_monic (n : ℕ) : (rowPolynomial n).Monic := by
  apply ((monic_ascPochhammer ℤ (n + 1)).comp_X_add_C 1).sub_of_left
  apply degree_lt_degree
  rw [natDegree_C, natDegree_comp, natDegree_X_add_C, ascPochhammer_natDegree, mul_one]
  omega

lemma rowPolynomial_eval_one (n : ℕ) :
    (rowPolynomial n).eval 1 = ((n + 2).factorial : ℤ) - 1 := by
  have h := factorial_mul_ascPochhammer ℤ 1 (n + 1)
  simpa [rowPolynomial, eval_comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

lemma quotient_eq_zero (P : Polynomial ℤ) (n : ℕ) (hn : P.natDegree ≤ n) :
    P /ₘ rowPolynomial n = 0 := by
  apply (divByMonic_eq_zero_iff (rowPolynomial_monic n)).mpr
  apply degree_lt_degree
  rw [rowPolynomial_natDegree]
  omega

noncomputable def boundary (P : Polynomial ℤ) : ℤ :=
  ∑ n ∈ Finset.range P.natDegree, (P /ₘ rowPolynomial n).eval 1

noncomputable def residueRow (P : Polynomial ℤ) (n : ℕ) : ℝ :=
  (((P %ₘ rowPolynomial n).eval 1 : ℤ) : ℝ) * term n

lemma row_identity (P : Polynomial ℤ) (n : ℕ) :
    residueRow P n = ((P.eval 1 : ℤ) : ℝ) * term n -
      (((P /ₘ rowPolynomial n).eval 1 : ℤ) : ℝ) := by
  have he := congrArg (fun p : Polynomial ℤ => p.eval 1)
    (modByMonic_add_div P (rowPolynomial_monic n))
  simp only [eval_add, eval_mul, rowPolynomial_eval_one] at he
  have heR := congrArg (fun z : ℤ => (z : ℝ)) he
  push_cast at heR
  unfold residueRow term
  have hd := (denom_pos n).ne'
  field_simp
  nlinarith [heR]

/-- The quotient values have finite support and integral total boundary. -/
lemma hasSum_quotients (P : Polynomial ℤ) :
    HasSum (fun n => (((P /ₘ rowPolynomial n).eval 1 : ℤ) : ℝ))
      (boundary P : ℝ) := by
  convert hasSum_sum_of_ne_finset_zero (s := Finset.range P.natDegree)
    (f := fun n => (((P /ₘ rowPolynomial n).eval 1 : ℤ) : ℝ))
    (by
      intro n hn
      have hle : P.natDegree ≤ n := by simpa using hn
      simp [quotient_eq_zero P n hle]) using 1
  · simp [boundary]
  · infer_instance

/-- An exact integer linear form, with no coefficient-denominator clearing. -/
theorem hasSum_residueRows (P : Polynomial ℤ) :
    HasSum (residueRow P)
      (((P.eval 1 : ℤ) : ℝ) * (∑' n : ℕ, term n) - (boundary P : ℝ)) := by
  have hfun : residueRow P = fun n => ((P.eval 1 : ℤ) : ℝ) * term n -
      (((P /ₘ rowPolynomial n).eval 1 : ℤ) : ℝ) := by
    funext n
    exact row_identity P n
  rw [hfun]
  exact (summable_term.hasSum.mul_left ((P.eval 1 : ℤ) : ℝ)).sub (hasSum_quotients P)

theorem integer_form_identity (P : Polynomial ℤ) :
    ((P.eval 1 : ℤ) : ℝ) * (∑' n : ℕ, term n) - (boundary P : ℝ) =
      ∑' n : ℕ, residueRow P n := (hasSum_residueRows P).tsum_eq.symm

lemma residueRow_of_large_index (P : Polynomial ℤ) (n : ℕ) (hn : P.natDegree ≤ n) :
    residueRow P n = ((P.eval 1 : ℤ) : ℝ) * term n := by
  rw [row_identity, quotient_eq_zero P n hn]
  simp

noncomputable def productKernel (K : ℕ) : Polynomial ℤ :=
  ∏ n ∈ Finset.range K, rowPolynomial n

lemma productKernel_monic (K : ℕ) : (productKernel K).Monic :=
  monic_prod_of_monic _ _ (fun n _ => rowPolynomial_monic n)

lemma productKernel_eval_one (K : ℕ) :
    (productKernel K).eval 1 =
      ∏ n ∈ Finset.range K, (((n + 2).factorial : ℤ) - 1) := by
  simp [productKernel, eval_prod, rowPolynomial_eval_one]

/-- All initial K rows vanish exactly for this product kernel. -/
theorem productKernel_initial_rows_zero (K n : ℕ) (hn : n < K) :
    residueRow (productKernel K) n = 0 := by
  have hd : rowPolynomial n ∣ productKernel K :=
    Finset.dvd_prod_of_mem rowPolynomial (Finset.mem_range.mpr hn)
  have hz := (modByMonic_eq_zero_iff_dvd (rowPolynomial_monic n)).mpr hd
  simp [residueRow, hz]

/-- A vanishing row still imposes the corresponding denominator divisibility
on the leading coefficient. Integrality of the polynomial coefficients is
essential here; this is not asserted for arbitrary rational kernels. -/
lemma zero_row_implies_dvd (P : Polynomial ℤ) (n : ℕ)
    (hz : residueRow P n = 0) :
    (((n + 2).factorial : ℤ) - 1) ∣ P.eval 1 := by
  have hr : ((P %ₘ rowPolynomial n).eval 1 : ℤ) = 0 := by
    have hR : (((P %ₘ rowPolynomial n).eval 1 : ℤ) : ℝ) = 0 :=
      (mul_eq_zero.mp hz).resolve_right (term_pos n).ne'
    exact_mod_cast hR
  have he := congrArg (fun p : Polynomial ℤ => p.eval 1)
    (modByMonic_add_div P (rowPolynomial_monic n))
  simp only [eval_add, eval_mul, rowPolynomial_eval_one, hr, zero_add] at he
  exact ⟨(P /ₘ rowPolynomial n).eval 1, he.symm⟩

#print axioms zero_row_implies_dvd
#print axioms hasSum_residueRows
#print axioms integer_form_identity
#print axioms productKernel_initial_rows_zero

end RisingMonicForms
