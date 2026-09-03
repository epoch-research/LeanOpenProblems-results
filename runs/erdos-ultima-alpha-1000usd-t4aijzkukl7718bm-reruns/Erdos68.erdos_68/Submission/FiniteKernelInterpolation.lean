import Submission.IndexDependentTelescoping

/-!
# Finite row cancellation does not constrain the boundary integer

Auxiliary results for the kernel approach to Erdős 68. No small positive
sequence of integer linear forms is constructed here.
-/

namespace FiniteKernelInterpolation

open Polynomial

/-- Integer-valued on the nonnegative integers; coefficients may be rational. -/
def IntegerValuedNat (H : Polynomial ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, H.eval (n : ℚ) = z

noncomputable def choosePoly (k : ℕ) : Polynomial ℚ :=
  C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

lemma choosePoly_eval (k n : ℕ) : (choosePoly k).eval (n : ℚ) = n.choose k := by
  have hf : (k.factorial : ℚ) ≠ 0 := by positivity
  simp only [choosePoly, eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

/-- Newton interpolation preserves integer values on all natural inputs. -/
theorem exists_integerValued_interpolant (v : ℕ → ℤ) (N : ℕ) :
    ∃ H : Polynomial ℚ, IntegerValuedNat H ∧
      ∀ n ≤ N, H.eval (n : ℚ) = v n := by
  induction N with
  | zero =>
      refine ⟨C (v 0 : ℚ), ?_, ?_⟩
      · intro n
        exact ⟨v 0, by simp⟩
      · intro n hn
        have : n = 0 := by omega
        simp [this]
  | succ N ih =>
      obtain ⟨H, hi, he⟩ := ih
      obtain ⟨z, hz⟩ := hi (N + 1)
      refine ⟨H + C ((v (N + 1) - z : ℤ) : ℚ) * choosePoly (N + 1), ?_, ?_⟩
      · intro n
        obtain ⟨w, hw⟩ := hi n
        refine ⟨w + (v (N + 1) - z) * (n.choose (N + 1) : ℤ), ?_⟩
        simp only [eval_add, eval_mul, eval_C, choosePoly_eval, hw]
        push_cast
        ring
      · intro n hn
        simp only [eval_add, eval_mul, eval_C, choosePoly_eval]
        by_cases heq : n = N + 1
        · subst n
          rw [hz, Nat.choose_self]
          push_cast
          ring
        · rw [Nat.choose_eq_zero_of_lt (by omega), he n (by omega)]
          simp

/-- The integer values imposed by cancelling successive rows. -/
def nodeValue (A B : ℤ) : ℕ → ℤ
  | 0 => B
  | n + 1 => (n + 2 : ℤ) * nodeValue A B n -
      (A / ((n + 2).factorial - 1 : ℤ)) * (n + 2).factorial

noncomputable def rowNumerator (H : Polynomial ℚ) (n : ℕ) : ℚ :=
  (n + 2 : ℚ) * H.eval ((n + 1 : ℕ) : ℚ) - H.eval ((n + 2 : ℕ) : ℚ)

noncomputable def rationalKernel (A : ℤ) (H : Polynomial ℚ) (n : ℕ) : ℚ :=
  A - (1 - 1 / ((n + 2).factorial : ℚ)) * rowNumerator H n

/-- Every admissible leading integer A permits every boundary integer B,
even when all the selected rows vanish exactly. -/
theorem finite_rows_zero_arbitrary_boundary (N : ℕ) (A B : ℤ)
    (hA : ∀ n < N, ((n + 2).factorial - 1 : ℤ) ∣ A) :
    ∃ H : Polynomial ℚ, IntegerValuedNat H ∧ H.eval 1 = B ∧
      ∀ n < N, rationalKernel A H n = 0 := by
  let v : ℕ → ℤ := fun n => if n = 0 then 0 else nodeValue A B (n - 1)
  obtain ⟨H, hi, he⟩ := exists_integerValued_interpolant v (N + 1)
  refine ⟨H, hi, ?_, ?_⟩
  · simpa [v, nodeValue] using he 1 (by omega)
  · intro n hn
    have he1 : H.eval ((n + 1 : ℕ) : ℚ) = nodeValue A B n := by
      simpa [v] using he (n + 1) (by omega)
    have he2 : H.eval ((n + 2 : ℕ) : ℚ) = nodeValue A B (n + 1) := by
      simpa [v] using he (n + 2) (by omega)
    have hnum : rowNumerator H n =
        (A / ((n + 2).factorial - 1 : ℤ) : ℤ) * ((n + 2).factorial : ℚ) := by
      simp only [rowNumerator, he1, he2, nodeValue]
      push_cast
      ring
    have hdiv : ((A / ((n + 2).factorial - 1 : ℤ) : ℤ) : ℚ) *
        (((n + 2).factorial : ℚ) - 1) = A := by
      exact_mod_cast Int.ediv_mul_cancel (hA n hn)
    have hf : ((n + 2).factorial : ℚ) ≠ 0 := by positivity
    unfold rationalKernel
    rw [hnum]
    field_simp
    nlinarith [hdiv]

lemma summable_eval_div_factorial (H : Polynomial ℚ) :
    Summable (fun n : ℕ => ((H.eval (n : ℚ) : ℚ) : ℝ) / (n.factorial : ℝ)) := by
  induction H using Polynomial.induction_on' with
  | add H K hH hK =>
      simpa only [eval_add, Rat.cast_add, add_div] using hH.add hK
  | monomial k c =>
      simpa only [eval_monomial, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
        mul_div_assoc] using
        (IndexDependentTelescoping.summable_nat_pow_div_factorial k).mul_left (c : ℝ)

noncomputable def scaledEval (H : Polynomial ℚ) (n : ℕ) : ℝ :=
  ((H.eval (n : ℚ) : ℚ) : ℝ) / (n.factorial : ℝ)

lemma rowNumerator_div (H : Polynomial ℚ) (n : ℕ) :
    (rowNumerator H n : ℝ) / ((n + 2).factorial : ℝ) =
      scaledEval H (n + 1) - scaledEval H (n + 2) := by
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have hfac : ((n + 2).factorial : ℝ) =
      (n + 2 : ℝ) * ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ (n + 1)
  unfold rowNumerator scaledEval
  push_cast
  rw [hfac]
  field_simp

lemma hasSum_rows (H : Polynomial ℚ) :
    HasSum (fun n : ℕ => (rowNumerator H n : ℝ) / ((n + 2).factorial : ℝ))
      ((H.eval 1 : ℚ) : ℝ) := by
  have hs : Summable (scaledEval H) := summable_eval_div_factorial H
  have hs1 : Summable (fun n => scaledEval H (n + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable (fun n => scaledEval H (n + 2)) :=
    (summable_nat_add_iff 2).mpr hs
  have he := Summable.sum_add_tsum_nat_add 1 hs1
  have he' : (∑' n, scaledEval H (n + 1)) - (∑' n, scaledEval H (n + 2)) =
      ((H.eval 1 : ℚ) : ℝ) := by
    simp only [Finset.sum_range_one, zero_add, Nat.add_assoc] at he
    have hbase : scaledEval H 1 = ((H.eval 1 : ℚ) : ℝ) := by simp [scaledEval]
    rw [hbase] at he
    linarith
  simpa only [rowNumerator_div, he'] using hs1.hasSum.sub hs2.hasSum

lemma kernel_div (A : ℤ) (H : Polynomial ℚ) (n : ℕ) :
    (rationalKernel A H n : ℝ) / (((n + 2).factorial : ℝ) - 1) =
      (A : ℝ) / (((n + 2).factorial : ℝ) - 1) -
        (rowNumerator H n : ℝ) / ((n + 2).factorial : ℝ) := by
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
  have hd : ((n + 2).factorial : ℝ) - 1 ≠ 0 :=
    ne_of_gt (Erdos68Development.denom_pos n)
  unfold rationalKernel
  push_cast
  field_simp

/-- The interpolation construction leaves the total form equal to A*alpha-B;
finite zeros alone do not bound it or fix its sign. -/
theorem hasSum_kernel (A : ℤ) (H : Polynomial ℚ) :
    HasSum (fun n : ℕ =>
      (rationalKernel A H n : ℝ) / (((n + 2).factorial : ℝ) - 1))
      ((A : ℝ) * (∑' n : ℕ, Erdos68Development.term n) - ((H.eval 1 : ℚ) : ℝ)) := by
  simpa only [kernel_div, Erdos68Development.term, mul_one_div] using
    (Erdos68Development.summable_term.hasSum.mul_left (A : ℝ)).sub (hasSum_rows H)

#print axioms exists_integerValued_interpolant
#print axioms finite_rows_zero_arbitrary_boundary
#print axioms hasSum_kernel

end FiniteKernelInterpolation
