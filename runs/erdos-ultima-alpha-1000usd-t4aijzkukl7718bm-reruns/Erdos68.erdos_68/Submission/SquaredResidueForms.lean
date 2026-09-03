import Submission.Development

/-!
# Positive squared-residue forms and a uniform obstruction

This file does not settle Erdős 68. It constructs positive integer linear
forms using squared residues, and proves that this construction cannot
produce forms tending to zero for the factorial-minus-one denominators.
-/

namespace SquaredResidueForms

open Erdos68Development

noncomputable def boundary (A : ℕ) (s : Finset ℕ) (b : ℕ → ℤ) : ℤ :=
  ∑ n ∈ s, (2 * (A : ℤ) * b n - (denom n : ℤ) * (b n)^2)

noncomputable def form (A : ℕ) (s : Finset ℕ) (b : ℕ → ℤ) : ℝ :=
  (A : ℝ)^2 * (∑' n : ℕ, term n) - boundary A s b

noncomputable def residueRow (A : ℕ) (s : Finset ℕ) (b : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((A : ℝ) - (denom n : ℝ) * (if n ∈ s then (b n : ℝ) else 0))^2 /
    (denom n : ℝ)

lemma denom_pos_nat (n : ℕ) : 0 < denom n := by
  have hf : 2 ≤ (n + 2).factorial := by
    simpa using Nat.factorial_le (show 2 ≤ n + 2 by omega)
  unfold denom
  omega

lemma residueRow_identity (A : ℕ) (s : Finset ℕ) (b : ℕ → ℤ) (n : ℕ) :
    residueRow A s b n = (A : ℝ)^2 * term n -
      (if n ∈ s then ((2 * (A : ℤ) * b n - (denom n : ℤ) * (b n)^2 : ℤ) : ℝ)
        else 0) := by
  have hd : (denom n : ℝ) ≠ 0 := by exact_mod_cast (denom_pos_nat n).ne'
  rw [term_eq_inv_denom]
  unfold residueRow
  split_ifs <;> push_cast <;> field_simp <;> ring

lemma residueRow_nonneg (A : ℕ) (s : Finset ℕ) (b : ℕ → ℤ) (n : ℕ) :
    0 ≤ residueRow A s b n := by
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- The boundary is integral, and the series of squared residues is its
exact error against the original sum. -/
theorem hasSum_residueRow (A : ℕ) (s : Finset ℕ) (b : ℕ → ℤ) :
    HasSum (residueRow A s b) (form A s b) := by
  have hb : HasSum (fun n : ℕ =>
      if n ∈ s then ((2 * (A : ℤ) * b n - (denom n : ℤ) * (b n)^2 : ℤ) : ℝ)
        else 0) (boundary A s b : ℝ) := by
    convert hasSum_sum_of_ne_finset_zero (s := s)
      (f := fun n : ℕ => if n ∈ s then
        ((2 * (A : ℤ) * b n - (denom n : ℤ) * (b n)^2 : ℤ) : ℝ) else 0)
      (by intro n hn; simp [hn]) using 1
    · simp [boundary]
    · infer_instance
  have hfun : residueRow A s b = fun n => (A : ℝ)^2 * term n -
      (if n ∈ s then ((2 * (A : ℤ) * b n - (denom n : ℤ) * (b n)^2 : ℤ) : ℝ)
        else 0) := by
    funext n
    exact residueRow_identity A s b n
  rw [hfun]
  exact (summable_term.hasSum.mul_left ((A : ℝ)^2)).sub hb

lemma residueRow_le_form (A : ℕ) (s : Finset ℕ) (b : ℕ → ℤ) (n : ℕ) :
    residueRow A s b n ≤ form A s b := by
  have h := (hasSum_residueRow A s b).summable.le_tsum n
    (fun m _ => residueRow_nonneg A s b m)
  rwa [(hasSum_residueRow A s b).tsum_eq] at h

lemma sq_le_residue_sq (A d : ℕ) (hd : 2 * A < d) (z : ℤ) :
    (A : ℝ)^2 ≤ ((A : ℝ) - (d : ℝ) * (z : ℝ))^2 := by
  have hdR : 2 * (A : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  by_cases hz : z ≤ 0
  · have hzR : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    have hh : (d : ℝ) * (z : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) hzR
    nlinarith [sq_nonneg ((d : ℝ) * (z : ℝ))]
  · have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 1 ≤ z by omega)
    have hh : (d : ℝ) ≤ (d : ℝ) * (z : ℝ) := by nlinarith
    nlinarith [sq_nonneg ((d : ℝ) * (z : ℝ) - 2 * A)]

lemma row_lower_of_large_denom (A : ℕ) (s : Finset ℕ) (b : ℕ → ℤ)
    (n : ℕ) (hn : 2 * A < denom n) :
    (A : ℝ)^2 / (denom n : ℝ) ≤ form A s b := by
  apply le_trans ?_ (residueRow_le_form A s b n)
  unfold residueRow
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  by_cases hns : n ∈ s
  · simpa [hns] using sq_le_residue_sq A (denom n) hn (b n)
  · simp [hns]

lemma denom_succ_lt_square (n : ℕ) (hn : 1 ≤ n) :
    denom (n + 1) < (denom n)^2 := by
  by_cases hn1 : n = 1
  · subst n
    norm_num [denom, Nat.factorial]
  · have hb := denom_ge_add_five (show 2 ≤ n by omega)
    rw [denom_nat_succ]
    nlinarith [sq_nonneg ((denom n : ℤ) - (n + 3))]

lemma exists_crossing (A : ℕ) (hA : 0 < A) :
    ∃ m : ℕ, denom m ≤ 2 * A ∧ 2 * A < denom (m + 1) := by
  have hex : ∃ n : ℕ, 2 * A < denom n := by
    refine ⟨2 * A + 2, ?_⟩
    have hh := denom_ge_add_five (show 2 ≤ 2 * A + 2 by omega)
    omega
  let n := Nat.find hex
  have hn : 2 * A < denom n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    rw [he] at hn
    norm_num [denom] at hn
    omega
  refine ⟨n - 1, ?_, ?_⟩
  · have hh : ¬ 2 * A < denom (n - 1) :=
      Nat.find_min hex (show n - 1 < n by omega)
    exact Nat.le_of_not_gt hh
  · simpa only [Nat.sub_add_cancel hn0] using hn

lemma exists_denom_between (A : ℕ) (hA : 0 < A) :
    ∃ n : ℕ, 2 * A < denom n ∧ denom n ≤ 5 * A^2 := by
  obtain ⟨m, hm, hn⟩ := exists_crossing A hA
  refine ⟨m + 1, hn, ?_⟩
  by_cases hm0 : m = 0
  · subst m
    norm_num [denom]
    nlinarith
  · have hh := denom_succ_lt_square m (by omega)
    nlinarith

/-- Every nonzero squared-residue form stays uniformly away from zero.
Thus automatic positivity alone does not yield an irrationality proof. -/
theorem one_fifth_le_form (A : ℕ) (hA : 0 < A)
    (s : Finset ℕ) (b : ℕ → ℤ) : (1 / 5 : ℝ) ≤ form A s b := by
  obtain ⟨n, hn, hbound⟩ := exists_denom_between A hA
  apply le_trans ?_ (row_lower_of_large_denom A s b n hn)
  have hd : (0 : ℝ) < denom n := by exact_mod_cast denom_pos_nat n
  have hb : (denom n : ℝ) ≤ 5 * (A : ℝ)^2 := by exact_mod_cast hbound
  apply (le_div_iff₀ hd).mpr
  nlinarith

lemma square_index_le_denom (n : ℕ) : n^2 ≤ denom n := by
  induction n with
  | zero => simp [denom]
  | succ n ih =>
    rw [denom_nat_succ]
    have hm := Nat.mul_le_mul_left (n + 3) ih
    by_cases hn : n = 0
    · subst n; norm_num [denom]
    · have hn1 : 1 ≤ n := by omega
      have hn2 : n ≤ n^2 := by nlinarith
      nlinarith [Nat.zero_le (n^3)]

/-- Uniform growth of the squared-residue obstruction.  Both the finite
set of modified rows and their integral choices can vary arbitrarily. -/
theorem large_le_form (R A : ℕ) (hR : 1 ≤ R) (hA : 34 * R^2 ≤ A)
    (s : Finset ℕ) (b : ℕ → ℤ) : (R : ℝ) ≤ form A s b := by
  have hA1 : 1 ≤ A := by nlinarith
  obtain ⟨m, hm, hn⟩ := exists_crossing A (by omega)
  have hm2 : m^2 ≤ 2 * A := (square_index_le_denom m).trans hm
  have hd : denom (m + 1) ≤ (3 * m + 8) * A := by
    rw [denom_nat_succ]
    have hh := Nat.mul_le_mul_left (m + 3) hm
    have hh' : m + 2 ≤ (m + 2) * A := by
      simpa using Nat.mul_le_mul_left (m + 2) hA1
    nlinarith
  have hcross : R * (3 * m + 8) ≤ A := by
    have hsq := sq_nonneg ((m : ℤ) - 6 * R)
    have hm2Z : (m : ℤ)^2 ≤ 2 * A := by exact_mod_cast hm2
    have hAZ : 34 * (R : ℤ)^2 ≤ A := by exact_mod_cast hA
    have hRZ : (1 : ℤ) ≤ R := by exact_mod_cast hR
    have hr2 : (R : ℤ) ≤ (R : ℤ)^2 := by nlinarith
    have hh : (R : ℤ) * (3 * m + 8) ≤ A := by nlinarith
    exact_mod_cast hh
  have hprod : R * denom (m + 1) ≤ A^2 := by
    have hh := Nat.mul_le_mul_left R hd
    have hh' := Nat.mul_le_mul_right A hcross
    nlinarith
  apply le_trans ?_ (row_lower_of_large_denom A s b (m + 1) hn)
  have hdpos : (0 : ℝ) < denom (m + 1) := by
    exact_mod_cast denom_pos_nat (m + 1)
  apply (le_div_iff₀ hdpos).mpr
  exact_mod_cast hprod

#print axioms large_le_form
#print axioms hasSum_residueRow
#print axioms one_fifth_le_form

end SquaredResidueForms
