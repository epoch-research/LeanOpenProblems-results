import Submission.PrimePowerIncrementMatrix

/-!
The actual factorial-tail residue vectors have a special compatibility that
arbitrary residue vectors need not have. The resulting correction is exactly
a backward shift, not a new small linear form. This does not settle Spec.lean.
-/

namespace IncrementTargetCompatibility

open Finset PrimeLeadingForms PrimePowerIncrementMatrix

lemma reverse_telescope (f : ℕ → ℚ) (n m : ℕ) (hm : m ≤ n) :
    (∑ j ∈ range m, (f (n-j)-f (n-j-1))) = f n-f (n-m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih (by omega)]
    have he : n-m-1=n-(m+1) := by omega
    rw [he]
    ring

/-- A block of ordinary unit increment weights simply moves the prefix backward. -/
theorem unit_block_identity (c : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N) (i : Fin m) :
    (∑ j : Fin m, (unnormalized c N m i j : ℚ)) =
      ((N+i.val).factorial : ℚ)*
        (partialSum c (N+i.val)-partialSum c (N+i.val-m)) := by
  simp_rw [unnormalized_prefix_identity c N m hm]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    partialSum c (N+i.val-j)-partialSum c (N+i.val-j-1)) m]
  exact reverse_telescope (partialSum c) (N+i.val) m (by omega)

/-- In particular the correction has an exact analytic meaning for any endpoint. -/
theorem corrected_tail_eq_earlier (c : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N)
    (i : Fin m) (x : ℚ) :
    ((N+i.val).factorial : ℚ)*(x-partialSum c (N+i.val)) +
      (∑ j : Fin m, (unnormalized c N m i j : ℚ)) =
    ((N+i.val).factorial : ℚ)*(x-partialSum c (N+i.val-m)) := by
  rw [unit_block_identity c N m hm i]
  ring

/-- For a rational endpoint whose denominator is already absorbed by the earlier
factorial, the corrected target has the full falling-factorial divisibility.
This is a property of this target vector, not surjectivity for arbitrary vectors. -/
theorem target_factorial_quotient (c : ℕ → ℤ) (N m : ℕ) (hm : m ≤ N)
    (i : Fin m) (x : ℚ) (hx : x.den ≤ N+i.val-m) :
    ∃ z : ℤ,
      ((N+i.val).factorial : ℚ)*(x-partialSum c (N+i.val)) +
        (∑ j : Fin m, (unnormalized c N m i j : ℚ)) =
      ((N+i.val).descFactorial m : ℚ)*z := by
  obtain ⟨z, hz⟩ := factorial_mul_tail_integer c (N+i.val-m) (N+i.val-m)
    le_rfl x hx
  refine ⟨z, ?_⟩
  rw [corrected_tail_eq_earlier c N m hm i x]
  have he : ((N+i.val).factorial : ℚ) =
      ((N+i.val).descFactorial m : ℚ)*((N+i.val-m).factorial : ℚ) := by
    exact_mod_cast (by
      rw [Nat.mul_comm, Nat.factorial_mul_descFactorial (by omega : m ≤ N+i.val)])
  rw [he, mul_assoc, hz]

/-- Nonnegative coefficients make the backward correction nonnegative. -/
theorem unit_block_nonneg (c : ℕ → ℤ) (hc : ∀ n, 0 ≤ c n)
    (N m : ℕ) (i : Fin m) :
    (0 : ℚ) ≤ ∑ j : Fin m, (unnormalized c N m i j : ℚ) := by
  apply sum_nonneg
  intro j _
  simp only [unnormalized, normalized, Int.cast_mul, Int.cast_natCast]
  apply mul_nonneg (by positivity)
  apply mul_nonneg (by positivity)
  exact_mod_cast hc (N+i.val-j.val)

theorem corrected_tail_not_smaller (c : ℕ → ℤ) (hc : ∀ n, 0 ≤ c n)
    (N m : ℕ) (hm : m ≤ N) (i : Fin m) (x : ℚ) :
    ((N+i.val).factorial : ℚ)*(x-partialSum c (N+i.val)) ≤
      ((N+i.val).factorial : ℚ)*(x-partialSum c (N+i.val-m)) := by
  have hn := unit_block_nonneg c hc N m i
  rw [← corrected_tail_eq_earlier c N m hm i x]
  linarith

end IncrementTargetCompatibility

#print axioms IncrementTargetCompatibility.corrected_tail_eq_earlier
#print axioms IncrementTargetCompatibility.target_factorial_quotient
#print axioms IncrementTargetCompatibility.corrected_tail_not_smaller
