import Submission.ParityDiscrepancyUnbounded
import Submission.FifthPowerBound

/-!
A polynomial gap bound cannot replace the full discrepancy error uniformly in
interval length. Actual parity discrepancies exceed every fixed polynomial of
the already defined uniform Jacobsthal bound. These intervals can be very long;
this does not settle the quadratic Jacobsthal conjecture or its negation.
-/
namespace Erdos970.ParityDiscrepancy
open Finset Filter

lemma exists_exponential_dominates_polynomial (A d K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧
      ((A : ℚ) * (k + 1 : ℚ) ^ d) ^ 2 < (4 / 3 : ℚ) ^ k := by
  have hshift : Tendsto (fun k : ℕ => k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => by omega : ∀ k : ℕ, k ≤ k + 1) tendsto_id
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt (2 * d)
    (by norm_num : (1 : ℝ) < 4 / 3)).comp hshift
  have ht' : Tendsto (fun k : ℕ => ((A : ℝ) * (k + 1 : ℝ) ^ d) ^ 2 /
      (4 / 3 : ℝ) ^ k) atTop (nhds 0) := by
    convert ht.const_mul ((A : ℝ) ^ 2 * (4 / 3)) using 1
    · funext k
      dsimp only [Function.comp_def]
      push_cast
      rw [pow_succ, show 2 * d = d * 2 by omega, pow_mul]
      field_simp; ring
    · norm_num
  have hev := ht'.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨k, hk, hK, hk1⟩ := (hev.and ((eventually_ge_atTop K).and
    (eventually_ge_atTop 1))).exists
  have hh : ((A : ℝ) * (k + 1 : ℝ) ^ d) ^ 2 < (4 / 3 : ℝ) ^ k := by
    have hp : (0 : ℝ) < (4 / 3 : ℝ) ^ k := by positivity
    have hb := (div_lt_iff₀ hp).mp hk
    simpa only [one_mul] using hb
  refine ⟨k, hK, by omega, ?_⟩
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  exact hh

/-- The parity discrepancy exceeds every polynomial in the number of primes,
even with an arbitrary lower length bound and lower quadratic length bound. -/
theorem unbounded_polynomial_parity_discrepancy (A d C M K : ℕ) :
    ∃ (P : Finset ℕ) (a m : ℕ),
      (∀ p ∈ P, p.Prime ∧ Odd p) ∧ K ≤ P.card ∧ 0 < P.card ∧
      M ≤ m ∧ C * P.card ^ 2 ≤ m ∧
      (A : ℚ) * (P.card + 1 : ℚ) ^ d < |alternatingCount P a m| := by
  obtain ⟨k, hK, hk, hpow⟩ := exists_exponential_dominates_polynomial A d K
  obtain ⟨P, hcard, hP⟩ := exists_odd_prime_set k
  let t := 2 * (M + C * k ^ 2) + 1
  have ht : Odd t := ⟨M + C * k ^ 2, rfl⟩
  have hN := primeProduct_pos P (fun p hp => (hP p hp).1.pos)
  have hbig : ((A : ℚ) * (P.card + 1 : ℚ) ^ d) ^ 2 < (4 / 3 : ℚ) ^ P.card := by
    rwa [hcard]
  obtain ⟨a, ha, hdisc⟩ := exists_large_alternatingCount P hP
    ((A : ℚ) * (P.card + 1 : ℚ) ^ d) (by positivity) hbig t ht
  refine ⟨P, a + 1, primeProduct P * t, hP, by omega, by omega, ?_, ?_, hdisc⟩
  · have hle := Nat.le_mul_of_pos_left t hN
    exact (show M ≤ t by dsimp [t]; omega).trans hle
  · have hle := Nat.le_mul_of_pos_left t hN
    rw [hcard]
    exact (show C * k ^ 2 ≤ t by dsimp [t]; omega).trans hle

lemma jacobsthal_add_one_le_fifth (k : ℕ) :
    jacobsthalFunction k + 1 ≤ (fifthPowerConstant + 1) * (k + 1) ^ 5 := by
  have h := jacobsthalFunction_le_fifth k
  have hp : 1 ≤ (k + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- In particular, no fixed polynomial in a valid uniform gap bound controls
parity discrepancy on all intervals. The proof uses the unconditional fifth
power bound, not the original quadratic conjecture. -/
theorem unbounded_jacobsthal_polynomial_parity (A d C M K : ℕ) :
    ∃ (P : Finset ℕ) (a m : ℕ),
      (∀ p ∈ P, p.Prime ∧ Odd p) ∧ K ≤ P.card ∧ 0 < P.card ∧
      M ≤ m ∧ C * P.card ^ 2 ≤ m ∧
      (A : ℚ) * (jacobsthalFunction P.card + 1 : ℚ) ^ d <
        |alternatingCount P a m| := by
  obtain ⟨P, a, m, hP, hK, hk, hM, hC, hlarge⟩ :=
    unbounded_polynomial_parity_discrepancy (A * (fifthPowerConstant + 1) ^ d)
      (5 * d) C M K
  refine ⟨P, a, m, hP, hK, hk, hM, hC, lt_of_le_of_lt ?_ hlarge⟩
  have hn := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_left (jacobsthal_add_one_le_fifth P.card) d)
  have he : A * ((fifthPowerConstant + 1) * (P.card + 1) ^ 5) ^ d =
      (A * (fifthPowerConstant + 1) ^ d) * (P.card + 1) ^ (5 * d) := by
    rw [mul_pow, ← pow_mul]
    ring
  rw [he] at hn
  exact_mod_cast hn

/-- Explicit negation of a possible gap-controlled discrepancy shortcut.
This is not the negation of the Erdős 970 conjecture. -/
theorem no_uniform_gap_polynomial_parity_error (d C K : ℕ) :
    ¬∃ A : ℝ, ∀ (P : Finset ℕ) (a m : ℕ),
      (∀ p ∈ P, p.Prime ∧ Odd p) → K ≤ P.card → C * P.card ^ 2 ≤ m →
      |(alternatingCount P a m : ℝ)| ≤
        A * (jacobsthalFunction P.card + 1 : ℝ) ^ d := by
  rintro ⟨A, hA⟩
  obtain ⟨B, hB⟩ := exists_nat_gt A
  obtain ⟨P, a, m, hP, hK, hk, _, hC, hlarge⟩ :=
    unbounded_jacobsthal_polynomial_parity B d C 0 K
  have hlargeR : (B : ℝ) * (jacobsthalFunction P.card + 1 : ℝ) ^ d <
      |(alternatingCount P a m : ℝ)| := by exact_mod_cast hlarge
  have hsmall := hA P a m hP hK hC
  have hh := mul_le_mul_of_nonneg_right hB.le
    (show (0 : ℝ) ≤ (jacobsthalFunction P.card + 1 : ℝ) ^ d by positivity)
  linarith

#print axioms unbounded_polynomial_parity_discrepancy
#print axioms unbounded_jacobsthal_polynomial_parity
#print axioms no_uniform_gap_polynomial_parity_error
end Erdos970.ParityDiscrepancy
