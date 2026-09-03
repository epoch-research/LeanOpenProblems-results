import Submission.AlignedBoundaryIdentity
import Submission.FactorialMinusOneLcmBound

/-! A limitation of zero-aligned, complete row cancellation: the error of
any form with nonzero retained coefficient is eventually larger than one.
This is auxiliary work, not a proof or disproof of Erdős 68. -/

namespace AlignedBoundaryGrowth

open Finset Erdos68Development LambertDifferenceOperators AlignedBoundaryIdentity
  AlignedRowAnnihilator

private lemma cubic_budget (m : ℕ) (hm : 32 ≤ m) :
    12*(m+2)^2 ≤ m^3 := by
  have h1 : 32*m^2 ≤ m^3 := by
    have := Nat.mul_le_mul_right (m^2) hm
    nlinarith
  have h2 : 32*m ≤ m^2 := by nlinarith
  nlinarith

private lemma block_at_index (N : ℕ) (hN : 10000 ≤ N) :
    ∃ m : ℕ, 32 ≤ m ∧ 4*m^2+m ≤ N ∧ N+1 ≤ 4*(m+2)^2 := by
  let m := N.sqrt/2-1
  have hr : 100 ≤ N.sqrt := Nat.le_sqrt.mpr (by simpa using hN)
  have hm : 32 ≤ m := by dsimp [m]; omega
  have hs1 : 2*(m+1) ≤ N.sqrt := by dsimp [m]; omega
  have hs2 : N.sqrt < 2*(m+2) := by dsimp [m]; omega
  have hlo := (Nat.pow_le_pow_left hs1 2).trans (Nat.sqrt_le' N)
  have hhi := Nat.sqrt_lt'.mp hs2
  refine ⟨m, hm, ?_, ?_⟩ <;> nlinarith

/-- Clearing all original denominators through N eventually costs more
than the next factorial. The bound does not assume pairwise coprimality. -/
theorem common_multiple_ge_factorial (N L : ℕ) (hN : 10000 ≤ N) (hL : 0 < L)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → d.factorial-1 ∣ L) :
    (N+1).factorial ≤ L := by
  obtain ⟨m, hm, hlo, hhi⟩ := block_at_index N hN
  have hb : m^(m^3) ≤ L := by
    apply FactorialMinusOneLcmBound.quadratic_block_height m L (by omega) hL
    intro i hi
    exact hdiv (4*m^2+i) (by nlinarith) (by omega)
  have hc := cubic_budget m hm
  have he : 3*(N+1) ≤ m^3 := by omega
  calc
    (N+1).factorial ≤ (N+1)^(N+1) := Nat.factorial_le_pow _
    _ ≤ (m^3)^(N+1) := Nat.pow_le_pow_left (by omega) _
    _ = m^(3*(N+1)) := by rw [pow_mul]
    _ ≤ m^(m^3) := Nat.pow_le_pow_right (by omega) he
    _ ≤ L := hb

lemma first_omitted_term_le_error (N : ℕ) (hN : 2 ≤ N) :
    1 / ((N+1).factorial-1 : ℝ) ≤
      (∑' k : ℕ, term k)-∑ k ∈ range (N-1), term k := by
  have hsum := summable_term.sum_add_tsum_nat_add (N-1)
  have hs : Summable (fun k => term (k+(N-1))) :=
    (summable_nat_add_iff (N-1)).mpr summable_term
  have ht := hs.le_tsum 0 (fun k _ => (term_pos _).le)
  have he : term (0+(N-1)) = 1/((N+1).factorial-1 : ℝ) := by
    simp only [term, show 0+(N-1)+2=N+1 by omega]
  rw [he] at ht
  linarith

/-- For this specific normalization there are no eventually small nonzero
integer forms: every positive common multiple gives an error greater than 1. -/
theorem scaled_partial_error_gt_one (N L : ℕ) (hN : 10000 ≤ N) (hL : 0 < L)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → d.factorial-1 ∣ L) :
    1 < (L : ℝ)*((∑' k : ℕ, term k)-∑ k ∈ range (N-1), term k) := by
  have hf : ((N+1).factorial : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast common_multiple_ge_factorial N L hN hL hdiv
  have hp : (0 : ℝ) < (N+1).factorial-1 := by
    simpa only [show N-1+2=N+1 by omega] using denom_pos (N-1)
  have hq : (1 : ℝ) < (L : ℝ)/((N+1).factorial-1) := by
    apply (lt_div_iff₀ hp).mpr
    linarith
  have hb := mul_le_mul_of_nonneg_left (first_omitted_term_le_error N (by omega))
    (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  calc
    1 < (L : ℝ)/((N+1).factorial-1) := hq
    _ = (L : ℝ)*(1/((N+1).factorial-1)) := by ring
    _ ≤ _ := hb

/-- The absolute value version covers arbitrary signs of the retained
integer coefficient. Its nonzero hypothesis is essential. -/
theorem integer_partial_error_abs_gt_one (N : ℕ) (A : ℤ)
    (hN : 10000 ≤ N) (hA : A ≠ 0)
    (hdiv : ∀ d, 2 ≤ d → d ≤ N → (d.factorial : ℤ)-1 ∣ A) :
    1 < |(A : ℝ)*((∑' k : ℕ, term k)-∑ k ∈ range (N-1), term k)| := by
  have hd (d : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N) : d.factorial-1 ∣ A.natAbs := by
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_sub (Nat.factorial_pos d), Nat.cast_one] using hdiv d hd hdN
  have h := scaled_partial_error_gt_one N A.natAbs hN (Int.natAbs_pos.mpr hA) hd
  rw [abs_mul, abs_of_pos (partial_sum_error (N-1)).1]
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h

/-- Complete cancellation on 0,...,N cannot give a small nonzero form,
regardless of which integer weights accomplish the cancellation. -/
theorem zero_aligned_error_abs_gt_one (N : ℕ) (hN : 10000 ≤ N)
    (z : ℕ → ℤ) (hA : (∑ j ∈ range (N+1), z j) ≠ 0)
    (hz : ∀ d, 2 ≤ d → d ≤ N →
      (∑ j ∈ range (N+1), (z j : ℚ) /
        ((d.factorial : ℚ)^(j/d)*((d.factorial : ℚ)-1))) = 0) :
    1 < |∑ j ∈ range (N+1), (z j : ℝ)*
      ((∑' k : ℕ, term k)-(prefixQ j : ℝ))| := by
  let A := ∑ j ∈ range (N+1), z j
  have hb := boundary_of_row_cancellation N (by omega) z A rfl hz
  have hdiv (d : ℕ) (hd : 2 ≤ d) (hdN : d ≤ N) : (d.factorial : ℤ)-1 ∣ A :=
    VariableRowAnnihilation.factorial_row_denominator_dvd (range (N+1)) z id d hd
      (hz d hd hdN)
  have hsum : (∑ j ∈ range (N+1), (z j : ℝ)) = (A : ℝ) := by
    exact_mod_cast (show (∑ j ∈ range (N+1), z j) = A from rfl)
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, hsum, hb, ← mul_sub]
  exact integer_partial_error_abs_gt_one N A hN hA hdiv

end AlignedBoundaryGrowth

#print axioms AlignedBoundaryGrowth.common_multiple_ge_factorial
#print axioms AlignedBoundaryGrowth.scaled_partial_error_gt_one
#print axioms AlignedBoundaryGrowth.zero_aligned_error_abs_gt_one
