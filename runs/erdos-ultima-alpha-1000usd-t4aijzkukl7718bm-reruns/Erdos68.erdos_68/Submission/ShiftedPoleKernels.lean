import Submission.PositiveKernelBoundary
import Submission.TailPowerExpansion

/-!
# Shifted original-series poles

Auxiliary identities and an obstruction to exact column cancellation.
These results do not settle Erdős 68.
-/

namespace ShiftedPoleKernels

open Erdos68Development RationalKernelForms

/-- Combining two adjacent original-series poles. -/
lemma two_pole_identity (A h k x n : ℝ)
    (hx : x - 1 ≠ 0) (hxn : x - n ≠ 0) :
    (A - k) / (x - 1) + n * h / (x - n) =
      ((A + n * h - k) * x + n * (k - h - A)) /
        ((x - 1) * (x - n)) := by
  field_simp
  ring

/-- The falling-factorial poles recover shifted original summands exactly. -/
lemma factorial_shifted_pole (n j : ℕ) (h : j + 2 ≤ n) :
    (n.descFactorial j : ℝ) /
        ((n.factorial : ℝ) - (n.descFactorial j : ℝ)) =
      1 / (((n - j).factorial : ℝ) - 1) := by
  have hj : j ≤ n := by omega
  have hf : ((n - j).factorial : ℝ) * (n.descFactorial j : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_mul_descFactorial hj
  have hd : (n.descFactorial j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hj))
  have htwo : (2 : ℝ) ≤ (n - j).factorial := by
    exact_mod_cast (show 2 ≤ (n - j).factorial by
      simpa using Nat.factorial_le (show 2 ≤ n - j by omega))
  have hden : ((n - j).factorial : ℝ) - 1 ≠ 0 := by linarith
  have he : (n.factorial : ℝ) - (n.descFactorial j : ℝ) =
      (n.descFactorial j : ℝ) * (((n - j).factorial : ℝ) - 1) := by
    rw [← hf]
    ring
  rw [he]
  field_simp

/-- An exactly constant polynomial telescoping coefficient must be zero.
This uses irrationality of an individual factorial-power column, not the
unproved irrationality of the original sum. -/
theorem constant_column_zero (H : Polynomial ℚ) (j : ℕ) (A : ℚ)
    (h : ∀ n : ℕ, rowCoeff H (j + 1) n = A) : A = 0 := by
  by_contra hA
  have hs := hasSum_rowCoeff H (j + 1) (by omega)
  have he : (A : ℝ) * (∑' n : ℕ, powerTerm j n) = ((H.eval 1 : ℚ) : ℝ) := by
    have hh : (fun n : ℕ => (rowCoeff H (j + 1) n : ℝ) /
        ((n + 2).factorial : ℝ) ^ (j + 1)) =
        (fun n : ℕ => (A : ℝ) * powerTerm j n) := by
      funext n
      rw [h n]
      simp [powerTerm, div_eq_mul_inv]
    rw [hh] at hs
    simpa only [tsum_mul_left] using hs.tsum_eq
  have hi := (irrational_sum_powerTerm j).ratCast_mul hA
  exact hi ⟨H.eval 1, he.symm⟩

/-- Even eventual exact cancellation of a nonzero constant column is
impossible for a fixed rational polynomial. -/
theorem eventually_constant_column_zero (H : Polynomial ℚ) (j N : ℕ) (A : ℚ)
    (h : ∀ n ≥ N, rowCoeff H (j + 1) n = A) : A = 0 := by
  have hp : PositiveKernelBoundary.columnOperator H j = Polynomial.C A := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hi : Function.Injective (fun n : ℕ => ((n + N + 2 : ℕ) : ℚ)) := by
      intro a b hab
      dsimp only at hab
      have he : a + N + 2 = b + N + 2 := by exact_mod_cast hab
      omega
    apply (Set.infinite_range_of_injective hi).mono
    rintro x ⟨n, rfl⟩
    change (PositiveKernelBoundary.columnOperator H j).eval
      ((n + N + 2 : ℕ) : ℚ) = (Polynomial.C A).eval _
    rw [PositiveKernelBoundary.columnOperator_eval_row, Polynomial.eval_C,
      h (n + N) (by omega)]
  apply constant_column_zero H j A
  intro n
  rw [← PositiveKernelBoundary.columnOperator_eval_row, hp, Polynomial.eval_C]

/-- The two-pole numerator cannot lose its leading factorial-power
coefficient at every row when the retained coefficient A is nonzero. -/
theorem two_pole_leading_nonzero (A : ℚ) (hA : A ≠ 0) (H : Polynomial ℚ) :
    ∃ n : ℕ, A + (n + 2 : ℚ) * H.eval (n + 1 : ℚ) -
      H.eval (n + 2 : ℚ) ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hc : ∀ n : ℕ, rowCoeff H 1 n = -A := by
    intro n
    have hh := hn n
    simp only [rowCoeff, pow_one, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    linarith
  have hz := constant_column_zero H 0 (-A) hc
  exact hA (neg_eq_zero.mp hz)

/-- For every cutoff, the first-column coefficient survives at some later
row. This is not a nonvanishing theorem for the summed original-series form. -/
theorem two_pole_leading_nonzero_after (A : ℚ) (hA : A ≠ 0)
    (H : Polynomial ℚ) (N : ℕ) :
    ∃ n ≥ N, A + (n + 2 : ℚ) * H.eval (n + 1 : ℚ) -
      H.eval (n + 2 : ℚ) ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hc : ∀ n ≥ N, rowCoeff H 1 n = -A := by
    intro n hnN
    have hh := hn n hnN
    simp only [rowCoeff, pow_one, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    linarith
  have hz := eventually_constant_column_zero H 0 N (-A) hc
  exact hA (neg_eq_zero.mp hz)

/-- A shifted-pole telescoping identity for any summable rational sequence
of boundary terms. Only A and the initial boundary are relevant to the
integrality of the final form. -/
theorem hasSum_shifted_kernel (A B : ℚ) (g : ℕ → ℚ)
    (hg : Summable (fun n : ℕ => (g n : ℝ))) (h0 : g 0 = A - B) :
    HasSum (fun n : ℕ => (A : ℝ) * term (n + 1) +
      (g n : ℝ) - (g (n + 1) : ℝ))
      ((A : ℝ) * (∑' n : ℕ, term n) - (B : ℝ)) := by
  have hgs : Summable (fun n : ℕ => (g (n + 1) : ℝ)) :=
    (summable_nat_add_iff 1).mpr hg
  have hts : Summable (fun n : ℕ => term (n + 1)) :=
    (summable_nat_add_iff 1).mpr summable_term
  have hge := hg.sum_add_tsum_nat_add 1
  have hte := summable_term.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hge hte
  have ht0 : term 0 = 1 := by norm_num [term]
  have he : (A : ℝ) * (∑' n : ℕ, term (n + 1)) +
      (∑' n : ℕ, (g n : ℝ)) - (∑' n : ℕ, (g (n + 1) : ℝ)) =
      (A : ℝ) * (∑' n : ℕ, term n) - (B : ℝ) := by
    rw [ht0] at hte
    rw [h0, Rat.cast_sub] at hge
    rw [← hte, ← hge]
    ring
  convert ((hts.hasSum.mul_left (A : ℝ)).add hg.hasSum).sub hgs.hasSum using 1
  exact he.symm

#print axioms factorial_shifted_pole
#print axioms eventually_constant_column_zero
#print axioms two_pole_leading_nonzero_after
#print axioms two_pole_identity
#print axioms constant_column_zero
#print axioms two_pole_leading_nonzero
#print axioms hasSum_shifted_kernel

end ShiftedPoleKernels
