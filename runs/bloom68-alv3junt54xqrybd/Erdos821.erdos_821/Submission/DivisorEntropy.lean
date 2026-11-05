import Submission.FiberBounds

/-!
# An unconditional divisor-entropy upper bound for totient fibers

For every positive `n` and nonnegative real `s`, this file proves

`fiberCard n ≤ n ^ s * exp (∑ d ∈ n.divisors, d ^ (-s))`.

The only earlier fiber input is the proved finite weighted Euler upper bound.
No smooth-prime endpoint certificate is assumed or used. This is an
unconditional upper bound, not a settlement of the endpoint conjecture.
`Submission.Spec` and its conjectural declarations are not imported or used.
-/

namespace Erdos821Fresh

open Nat Finset

set_option maxHeartbeats 500000

/-- The candidates' predecessor weights fit into the full divisor sum. -/
theorem candidate_predecessor_sum_le {n : ℕ} (hn : 0 < n) (s : ℝ) :
    (∑ p ∈ (Erdos821Aux.candidate_primes_finite hn.ne').toFinset,
      ((p - 1 : ℕ) : ℝ) ^ (-s)) ≤ ∑ d ∈ n.divisors, (d : ℝ) ^ (-s) := by
  classical
  let P := (Erdos821Aux.candidate_primes_finite hn.ne').toFinset
  have hP : ∀ p ∈ P, p.Prime ∧ p - 1 ∣ n := by
    intro p hp
    exact (Set.Finite.mem_toFinset (Erdos821Aux.candidate_primes_finite hn.ne')).mp hp
  have hinj : Set.InjOn (fun p : ℕ => p - 1) P := by
    intro p hp q hq hpq
    have hp2 := (hP p hp).1.two_le
    have hq2 := (hP q hq).1.two_le
    change p - 1 = q - 1 at hpq
    omega
  have hsub : P.image (fun p : ℕ => p - 1) ⊆ n.divisors := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨(hP p hp).2, hn.ne'⟩
  calc
    (∑ p ∈ P, ((p - 1 : ℕ) : ℝ) ^ (-s)) =
        ∑ d ∈ P.image (fun p : ℕ => p - 1), (d : ℝ) ^ (-s) := by
      rw [sum_image hinj]
    _ ≤ ∑ d ∈ n.divisors, (d : ℝ) ^ (-s) :=
      sum_le_sum_of_subset_of_nonneg hsub
        (fun d _ _ => Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- A fully unconditional Rankin/Euler upper bound in terms of the negative
moment of the divisors of the target value. -/
theorem fiberCard_le_rpow_exp_divisor_sum {n : ℕ} (hn : 0 < n)
    (s : ℝ) (hs : 0 ≤ s) :
    (Erdos821Aux.fiberCard n : ℝ) ≤ (n : ℝ) ^ s *
      Real.exp (∑ d ∈ n.divisors, (d : ℝ) ^ (-s)) := by
  classical
  let P := (Erdos821Aux.candidate_primes_finite hn.ne').toFinset
  have hprod : (∏ p ∈ P, (1 + ((p - 1 : ℕ) : ℝ) ^ (-s))) ≤
      Real.exp (∑ d ∈ n.divisors, (d : ℝ) ^ (-s)) := by
    calc
      (∏ p ∈ P, (1 + ((p - 1 : ℕ) : ℝ) ^ (-s))) ≤
          ∏ p ∈ P, Real.exp (((p - 1 : ℕ) : ℝ) ^ (-s)) := by
        apply prod_le_prod
        · intro p _
          positivity
        · intro p _
          simpa only [add_comm] using Real.add_one_le_exp (((p - 1 : ℕ) : ℝ) ^ (-s))
      _ = Real.exp (∑ p ∈ P, ((p - 1 : ℕ) : ℝ) ^ (-s)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑ d ∈ n.divisors, (d : ℝ) ^ (-s)) :=
        Real.exp_le_exp.mpr (candidate_predecessor_sum_le hn s)
  have hweighted := (Erdos821Aux.canonical_squarefree_weighted_bound hn s hs).trans hprod
  have hreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_neg (Nat.cast_nonneg n) s, ← div_eq_mul_inv] at hweighted
  simpa only [mul_comm] using
    (div_le_iff₀ (Real.rpow_pos_of_pos hreal s)).mp hweighted

end Erdos821Fresh

#print axioms Erdos821Fresh.candidate_predecessor_sum_le
#print axioms Erdos821Fresh.fiberCard_le_rpow_exp_divisor_sum
