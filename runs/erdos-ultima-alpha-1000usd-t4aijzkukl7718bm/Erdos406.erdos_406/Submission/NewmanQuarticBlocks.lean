import Submission.NewmanJointFlipRigidity
import Submission.NewmanQuarticSquare
import Submission.SparseTriple

/-! Exact block structure of all binary multiples of the known quartic.
This gives a descent for candidates containing that factor. It does not
exclude arbitrary candidates without that factor. -/
set_option maxHeartbeats 2000000

namespace Erdos406QuarticBlocks
open Polynomial Erdos406ReciprocalFlip Erdos406QuarticSquare
open Erdos406SparseTriple

noncomputable def block : ℤ[X] := (X+1)*qQuartic

lemma block_expanded : block = 1+X+X^2+X^5 := by unfold block qQuartic; ring

lemma quartic_reverse : qQuartic.reverse = X^4+X^2-X+1 := by
  have hd : qQuartic.natDegree = 4 := by unfold qQuartic; compute_degree!
  ext i
  rw [coeff_reverse, hd]
  by_cases hi : i ≤ 4
  · interval_cases i <;> norm_num [revAt, qQuartic, coeff_X, coeff_one]
  · have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h4 : i ≠ 4 := by omega
    simp [revAt, hi, qQuartic, coeff_X_pow, coeff_X, coeff_one, h0, h1, h2, h3, h4, Ne.symm h1]

lemma binary_coeff_bounds (P : ℤ[X]) (hP : Binary P) (i : ℕ) :
    0 ≤ P.coeff i ∧ P.coeff i ≤ 1 := by
  rcases hP i with h | h <;> omega

/-- The apparent alternative at coefficient five dies within three more
coefficients. Only the six-place block can start a normalized quotient. -/
lemma quotient_initial_block (R : ℤ[X]) (hR0 : R.coeff 0 = 1)
    (hP : Binary (qQuartic*R)) :
    R.coeff 1 = 1 ∧ R.coeff 2 = 0 ∧ R.coeff 3 = 0 ∧ R.coeff 4 = 0 ∧ R.coeff 5 = 0 := by
  have hf := binary_factor_flip qQuartic R hP
  rw [quartic_reverse] at hf
  have h1 := binary_coeff_bounds _ hP 1
  have h2 := binary_coeff_bounds _ hP 2
  have h3 := binary_coeff_bounds _ hP 3
  have h4 := binary_coeff_bounds _ hP 4
  have h5 := binary_coeff_bounds _ hP 5
  have h6 := binary_coeff_bounds _ hP 6
  have h7 := binary_coeff_bounds _ hP 7
  have h8 := binary_coeff_bounds _ hP 8
  have f1 := binary_coeff_bounds _ hf 1
  have f2 := binary_coeff_bounds _ hf 2
  have f3 := binary_coeff_bounds _ hf 3
  have f4 := binary_coeff_bounds _ hf 4
  have f5 := binary_coeff_bounds _ hf 5
  have f6 := binary_coeff_bounds _ hf 6
  have f7 := binary_coeff_bounds _ hf 7
  have f8 := binary_coeff_bounds _ hf 8
  norm_num [qQuartic, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul, hR0]
    at h1 h2 h3 h4 h5 h6 h7 h8 f1 f2 f3 f4 f5 f6 f7 f8
  have hr1 : R.coeff 1 = 1 := by omega
  have hr2 : R.coeff 2 = 0 := by omega
  have hr3 : R.coeff 3 = 0 := by omega
  have hr4 : R.coeff 4 = 0 := by omega
  have hr5 : R.coeff 5 = 0 := by
    by_contra hn
    have hr5 : R.coeff 5 = -1 := by omega
    have hr6 : R.coeff 6 = 0 := by omega
    omega
  exact ⟨hr1, hr2, hr3, hr4, hr5⟩

lemma quotient_block_split (R : ℤ[X]) (hR0 : R.coeff 0 = 1)
    (hP : Binary (qQuartic*R)) :
    ∃ T : ℤ[X], R = X+1+X^6*T ∧ Binary (qQuartic*T) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := quotient_initial_block R hR0 hP
  have hd : X^6 ∣ R-(X+1) := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    interval_cases i <;> simp [hR0,h1,h2,h3,h4,h5, coeff_X, coeff_one]
  obtain ⟨T, hT⟩ := hd
  have he : R = X+1+X^6*T := by linear_combination hT
  refine ⟨T, he, ?_⟩
  have hp : qQuartic*R = block+X^6*(qQuartic*T) := by rw [he]; unfold block; ring
  intro i
  have hh := hP (i+6)
  rw [hp, coeff_add, coeff_X_pow_mul] at hh
  have hb : block.coeff (i+6) = 0 := by
    rw [block_expanded]
    simp [coeff_X_pow, coeff_X, coeff_one, show i+6 ≠ 0 by omega,
      show i+6 ≠ 1 by omega, show i+6 ≠ 2 by omega, show i+6 ≠ 5 by omega]
  simpa only [hb, zero_add] using hh

/-- Polynomial counterpart of six-spaced ternary digits. -/
inductive Spaced : ℤ[X] → Prop
  | zero : Spaced 0
  | shift {S : ℤ[X]} : Spaced S → Spaced (X*S)
  | block {S : ℤ[X]} : Spaced S → Spaced (1+X^6*S)

lemma spaced_binary {S : ℤ[X]} (hS : Spaced S) : Binary S := by
  induction hS with
  | zero => intro i; simp
  | @shift S hS ih =>
    intro i
    cases i with
    | zero => simp
    | succ i => simpa using ih i
  | @block S hS ih =>
    intro i
    by_cases h0 : i = 0
    · subst i; simp
    by_cases hi : 6 ≤ i
    · simpa [coeff_add, coeff_one, h0, coeff_X_pow_mul', hi] using ih (i-6)
    · simp [coeff_add, coeff_one, h0, coeff_X_pow_mul', hi]

lemma spaced_eval {S : ℤ[X]} (hS : Spaced S) :
    ∃ n : ℕ, S.eval 3 = (n : ℤ) ∧ SixSpaced n := by
  induction hS with
  | zero => exact ⟨0, by simp, SixSpaced.zero⟩
  | @shift S hS ih =>
    obtain ⟨n, he, hn⟩ := ih
    exact ⟨3*n, by simp [he], SixSpaced.shift hn⟩
  | @block S hS ih =>
    obtain ⟨n, he, hn⟩ := ih
    refine ⟨729*n+1, ?_, SixSpaced.one hn⟩
    simp [he]
    ring

/-- Every binary multiple of the quartic has the block 100111 as a common
factor, with a six-spaced binary quotient. The parent need not be normalized. -/
theorem quotient_classification (R : ℤ[X]) (hP : Binary (qQuartic*R)) :
    ∃ S : ℤ[X], Spaced S ∧ R = (X+1)*S := by
  have main : ∀ D : ℕ, ∀ R : ℤ[X], R.natDegree = D → Binary (qQuartic*R) →
      ∃ S : ℤ[X], Spaced S ∧ R = (X+1)*S := by
    intro D
    induction D using Nat.strong_induction_on with
    | h D ih =>
      intro R hD hP
      by_cases hR : R = 0
      · exact ⟨0, Spaced.zero, by simp [hR]⟩
      have h0 := hP 0
      have hq0 : qQuartic.coeff 0 = 1 := by simp [qQuartic]
      rw [mul_coeff_zero, hq0, one_mul] at h0
      rcases h0 with h0 | h0
      · have he : R = X*R.divX := by
          have hh := R.divX_mul_X_add
          rw [h0, C_0, add_zero, mul_comm] at hh
          exact hh.symm
        have hdpos : 0 < R.natDegree := by
          by_contra hn
          have hh := eq_C_of_natDegree_eq_zero (show R.natDegree = 0 by omega)
          rw [h0, C_0] at hh
          exact hR hh
        have hb : Binary (qQuartic*R.divX) := by
          intro i
          have hh := hP (i+1)
          rw [he, show qQuartic*(X*R.divX) = X*(qQuartic*R.divX) by ring,
            coeff_X_mul] at hh
          exact hh
        obtain ⟨S, hS, hRS⟩ := ih R.divX.natDegree (by
          rw [natDegree_divX_eq_natDegree_tsub_one]
          omega) R.divX rfl hb
        refine ⟨X*S, Spaced.shift hS, ?_⟩
        rw [he, hRS]
        ring
      · obtain ⟨T, he, hb⟩ := quotient_block_split R h0 hP
        by_cases hT : T = 0
        · refine ⟨1, ?_, ?_⟩
          · simpa using Spaced.block Spaced.zero
          · simp [he, hT]
        have hdeg : T.natDegree < D := by
          have hh : R-(X+1) = X^6*T := by rw [he]; ring
          have hz : (X : ℤ[X])^6 ≠ 0 := pow_ne_zero _ X_ne_zero
          have hc := congrArg natDegree hh
          rw [natDegree_mul hz hT, natDegree_X_pow] at hc
          have hb := natDegree_sub_le R (X+1)
          have hlin : (X+1 : ℤ[X]).natDegree = 1 := by compute_degree!
          rw [hlin, hD] at hb
          omega
        obtain ⟨S, hS, hTS⟩ := ih T.natDegree hdeg T rfl hb
        refine ⟨1+X^6*S, Spaced.block hS, ?_⟩
        rw [he, hTS]
        ring
  exact main R.natDegree R rfl hP

/-- Classification of arbitrary binary polynomial multiples, not a
classification of all candidate digit polynomials. -/
theorem binary_multiple_classification (P : ℤ[X]) (hP : Binary P)
    (hd : qQuartic ∣ P) : ∃ S : ℤ[X], Spaced S ∧ P = block*S := by
  obtain ⟨R, he⟩ := hd
  obtain ⟨S, hS, hR⟩ := quotient_classification R (by rwa [← he])
  exact ⟨S, hS, by rw [he, hR]; unfold block; ring⟩

#print axioms quotient_initial_block
#print axioms quotient_classification
#print axioms binary_multiple_classification
end Erdos406QuarticBlocks
