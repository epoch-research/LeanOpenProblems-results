import Submission.NewmanQuarticTrace
import Submission.NewmanReciprocalCandidate
import Submission.NewmanQuarticSquare

/-! An exact classification of quartic factors of candidate digit polynomials.
Higher-degree factors are not classified, so this is not a solution of406. -/

namespace Erdos406QuarticClassification
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount
open Erdos406QuarticTrace Erdos406ReciprocalCandidate Erdos406ReciprocalFlip
open Erdos406QuarticSquare Erdos406FactorBridge

set_option maxHeartbeats 8000000 in
lemma quartic_arithmetic_classification (a b c : ℤ) (t : ℕ)
    (ht : 1 ≤ t) (ht4 : t ≤ 4) (ha : |a| ≤ 6) (hc : |c| ≤ 6)
    (h2a : |a ^ 2 - 2 * b| ≤ 10) (h2c : |c ^ 2 - 2 * b| ≤ 10)
    (h4 : |a ^ 4 - 4 * a ^ 2 * b + 4 * a * c + 2 * b ^ 2 - 4| ≤ 27)
    (hv : (4 : ℤ) ^ t = 82 + 27 * a + 9 * b + 3 * c)
    (hlo : 2 * (4 : ℤ) ^ t < 3 * (82 + 27 * c + 9 * b + 3 * a))
    (hhi : 2 * (82 + 27 * c + 9 * b + 3 * a) < 3 * (4 : ℤ) ^ t)
    (hone : 2 ≤ 2 + a + b + c) :
    (a = -1 ∧ b = 1 ∧ c = 0) ∨ (a = 4 ∧ b = 6 ∧ c = 4) := by
  have hcases :
      (a = -6 ∧ b = 18 ∧ c = -6) ∨ (a = -3 ∧ b = 8 ∧ c = -3) ∨
      (a = -1 ∧ b = 1 ∧ c = 0) ∨ (a = 3 ∧ b = 9 ∧ c = 4) ∨
      (a = 4 ∧ b = 6 ∧ c = 4) := by
    obtain ⟨ha0, ha1⟩ := abs_le.mp ha
    obtain ⟨hc0, hc1⟩ := abs_le.mp hc
    obtain ⟨h2a0, h2a1⟩ := abs_le.mp h2a
    obtain ⟨h2c0, h2c1⟩ := abs_le.mp h2c
    clear h4 ha hc h2a h2c
    interval_cases t <;> interval_cases a <;> interval_cases c <;>
      norm_num at * <;> omega
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | hh |
    ⟨rfl, rfl, rfl⟩ | hh
  · norm_num at h4
  · norm_num at h4
  · exact Or.inl hh
  · norm_num at h4
  · exact Or.inr hh

/-- Every monic quartic divisor of an actual candidate is either the known
quartic factor of256 or (X+1)^4. -/
theorem quartic_factor_classification (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hD : Q.natDegree = 4) :
    Q = qQuartic ∨ Q = (X + 1) ^ 4 := by
  have h0 := (candidate_monic_factor k hg Q hQ hd).1
  have h4 : Q.coeff 4 = 1 := by rw [← hD, coeff_natDegree, hQ.leadingCoeff]
  have hs := Q.as_sum_range_C_mul_X_pow
  rw [hD] at hs
  norm_num [Finset.sum_range_succ, h0, h4] at hs
  change Q = 1 + C (Q.coeff 1) * X + C (Q.coeff 2) * X ^ 2 +
    C (Q.coeff 3) * X ^ 3 + X ^ 4 at hs
  have hshape : Q = X ^ 4 + C (Q.coeff 3) * X ^ 3 + C (Q.coeff 2) * X ^ 2 +
      C (Q.coeff 1) * X + 1 := hs.trans (by ring)
  have hd' := hd
  rw [hshape] at hd'
  obtain ⟨ha, hc, h2a, h2c, htrace⟩ := candidate_quartic_trace_constraints k hg _ _ _ hd'
  obtain ⟨t, ht, _, he⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd (by omega)
  have hb := monic_eval_three_abs_bound Q hQ (candidate_factor_root_bound k hg Q hQ hd)
  rw [he, abs_of_nonneg (by positivity), hD] at hb
  have ht4 : t ≤ 4 := by
    by_contra hh
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) (by omega : 5 ≤ t)
    norm_num at hb hp
    omega
  have hv : Q.eval 3 = 82 + 27 * Q.coeff 3 + 9 * Q.coeff 2 + 3 * Q.coeff 1 := by
    conv_lhs => rw [hshape]
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one]
    ring
  have hrD : Q.reverse.natDegree < 5 := by
    have hh := Q.reverse_natDegree_le
    omega
  have hvr : Q.reverse.eval 3 = 82 + 27 * Q.coeff 1 + 9 * Q.coeff 2 + 3 * Q.coeff 3 := by
    rw [eval_eq_sum_range' hrD]
    norm_num [Finset.sum_range_succ, coeff_reverse, hD, revAt, h0, h4]
    ring
  have hlohi := candidate_factor_reciprocal_ratio k hg Q hQ hd
  rw [he, hvr] at hlohi
  have hone := (candidate_factor_eval_one_even k hg Q hQ hd (by omega)).2
  have hone' : 2 ≤ 2 + Q.coeff 3 + Q.coeff 2 + Q.coeff 1 := by
    rw [hshape] at hone
    norm_num at hone
    omega
  have hval : (4 : ℤ) ^ t = 82 + 27 * Q.coeff 3 + 9 * Q.coeff 2 + 3 * Q.coeff 1 := by
    rw [← he]
    exact hv
  have hh := quartic_arithmetic_classification _ _ _ t (by omega) ht4
    ha hc h2a h2c htrace hval hlohi.1 hlohi.2 hone'
  rcases hh with ⟨ha', hb', hc'⟩ | ⟨ha', hb', hc'⟩
  · left
    rw [hshape, ha', hb', hc']
    simp [qQuartic]
    ring
  · right
    rw [hshape, ha', hb', hc']
    norm_num
    ring

/-- The only irreducible quartic candidate factor is the known nonreciprocal one. -/
theorem irreducible_quartic_classification (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hD : Q.natDegree = 4)
    (hI : Irreducible Q) : Q = qQuartic := by
  rcases quartic_factor_classification k hg Q hQ hd hD with h | h
  · exact h
  · rw [h] at hI
    exact (not_irreducible_pow (by decide : 4 ≠ 1) hI).elim

#print axioms quartic_factor_classification
#print axioms irreducible_quartic_classification
end Erdos406QuarticClassification
