import Submission.ShiftedPoleKernels

/-!
Exact constant-column cancellation cannot be obtained by replacing a
polynomial auxiliary function with a reduced rational function. This is
an auxiliary obstruction, not a proof or disproof of Erdős 68.
-/

namespace RationalFunctionColumn

open Polynomial

lemma constant_of_shift_fixed (Q : Polynomial ℚ)
    (h : Q.comp (X - C 1) = Q) : Q = C (Q.eval 0) := by
  have hv : ∀ n : ℕ, Q.eval (n : ℚ) = Q.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have he := congrArg (fun R : Polynomial ℚ => R.eval ((n+1 : ℕ) : ℚ)) h
      simp only [eval_comp, eval_sub, eval_X, eval_C, Nat.cast_add, Nat.cast_one,
        add_sub_cancel_right] at he
      simpa only [Nat.cast_add, Nat.cast_one] using he.symm.trans ih
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => (n : ℚ)) := Nat.cast_injective
  apply (Set.infinite_range_of_injective hi).mono
  rintro x ⟨n, rfl⟩
  simpa only [eval_C] using hv n

/-- The denominator of a reduced rational solution must be constant.
This statement is purely polynomial arithmetic. -/
theorem denominator_constant (P Q : Polynomial ℚ) (j : ℕ) (A : ℚ)
    (hcop : IsCoprime P Q)
    (h : X^j * P.comp (X-C 1) * Q - P * Q.comp (X-C 1) =
      C A * Q.comp (X-C 1) * Q) : Q = C (Q.eval 0) := by
  have hprod : Q ∣ P * Q.comp (X-C 1) := by
    refine ⟨X^j * P.comp (X-C 1) - C A * Q.comp (X-C 1), ?_⟩
    linear_combination -h
  have hd : Q ∣ Q.comp (X-C 1) := hcop.symm.dvd_of_dvd_mul_left hprod
  have he : Q = Q.comp (X-C 1) := by
    apply Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff hd
    · simp only [natDegree_comp, natDegree_X_sub_C, mul_one, le_refl]
    · rw [leadingCoeff_comp (by rw [natDegree_X_sub_C]; decide), leadingCoeff_X_sub_C, one_pow, mul_one]
  exact constant_of_shift_fixed Q he.symm

/-- Eventual equality at natural rows gives the polynomial identity after
clearing denominators. The poles must not lie at the rows being evaluated. -/
lemma identity_of_eventual_rows (P Q : Polynomial ℚ) (j N : ℕ) (A : ℚ)
    (hQ : ∀ n ≥ N+1, Q.eval (n : ℚ) ≠ 0)
    (h : ∀ n ≥ N,
      (n+2 : ℚ)^(j+1) * P.eval (n+1 : ℚ) / Q.eval (n+1 : ℚ) -
        P.eval (n+2 : ℚ) / Q.eval (n+2 : ℚ) = A) :
    X^(j+1) * P.comp (X-C 1) * Q - P * Q.comp (X-C 1) =
      C A * Q.comp (X-C 1) * Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => ((n+N+2 : ℕ) : ℚ)) := by
    intro n m he
    dsimp only at he
    have he' : n+N+2 = m+N+2 := by exact_mod_cast he
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro x ⟨n, rfl⟩
  have hh := h (n+N) (by omega)
  have h1 : Q.eval (n+N+1 : ℚ) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hQ (n+N+1) (by omega)
  have h2 : Q.eval (n+N+2 : ℚ) ≠ 0 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hQ (n+N+2) (by omega)
  simp only [Nat.cast_add] at hh
  field_simp [h1, h2] at hh
  change _ = _
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_comp, eval_C,
    Nat.cast_add, Nat.cast_ofNat]
  rw [show (n : ℚ)+N+2-1 = (n : ℚ)+N+1 by ring]
  linear_combination hh

/-- A rational-function auxiliary with no poles on the eventual natural
rows cannot cancel a nonzero constant factorial-power column exactly. -/
theorem eventually_constant_column_zero (P Q : Polynomial ℚ)
    (j N : ℕ) (A : ℚ) (hcop : IsCoprime P Q)
    (hQ : ∀ n ≥ N+1, Q.eval (n : ℚ) ≠ 0)
    (h : ∀ n ≥ N,
      (n+2 : ℚ)^(j+1) * P.eval (n+1 : ℚ) / Q.eval (n+1 : ℚ) -
        P.eval (n+2 : ℚ) / Q.eval (n+2 : ℚ) = A) : A = 0 := by
  have he := denominator_constant P Q (j+1) A hcop
    (identity_of_eventual_rows P Q j N A hQ h)
  let H : Polynomial ℚ := C ((Q.eval 0)⁻¹) * P
  apply ShiftedPoleKernels.eventually_constant_column_zero H j N A
  intro n hn
  have hh := h n hn
  rw [he] at hh
  simpa only [RationalKernelForms.rowCoeff, H, eval_mul, eval_C,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hh


/-- A nonzero denominator has only finitely many natural poles, so no
separate pole-location assumption is needed in the eventual statement. -/
theorem rational_function_constant_column_zero (P Q : Polynomial ℚ)
    (j N : ℕ) (A : ℚ) (hcop : IsCoprime P Q) (hQ0 : Q ≠ 0)
    (h : ∀ n ≥ N,
      (n+2 : ℚ)^(j+1) * P.eval (n+1 : ℚ) / Q.eval (n+1 : ℚ) -
        P.eval (n+2 : ℚ) / Q.eval (n+2 : ℚ) = A) : A = 0 := by
  obtain ⟨b, hb⟩ := Q.exists_max_root hQ0
  obtain ⟨M, hM⟩ := exists_nat_gt b
  apply eventually_constant_column_zero P Q j (max N M) A hcop
  · intro n hn hz
    have hroot : Q.IsRoot (n : ℚ) := hz
    have hbound := hb (n : ℚ) hroot
    have hMn : (M : ℚ) ≤ n := by exact_mod_cast (show M ≤ n by omega)
    linarith
  · intro n hn
    exact h n (by omega)

#print axioms rational_function_constant_column_zero

#print axioms denominator_constant
#print axioms eventually_constant_column_zero

end RationalFunctionColumn
