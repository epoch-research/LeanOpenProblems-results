import Submission.NewmanFactorBridge
import Submission.NewmanReciprocalFlip

/-! Reciprocal-flip constraints on actual candidate factors for Erdős 406.
They are necessary conditions only; the conjecture is not settled here. -/
namespace Erdos406ReciprocalCandidate
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorBridge
open Erdos406ReciprocalFlip

lemma binary_digitPoly (w : List ℕ) (hw : w ⊆ [0, 1]) : Binary (digitPoly w) := by
  induction w with
  | nil => intro i; simp [digitPoly, Nat.ofDigits]
  | cons a w ih =>
    have ha : a = 0 ∨ a = 1 := by simpa using hw (by simp : a ∈ a :: w)
    have ht : Binary (digitPoly w) := ih (fun b hb => hw (by simp [hb]))
    intro i
    cases i with
    | zero => rcases ha with rfl | rfl <;> simp [digitPoly, Nat.ofDigits]
    | succ i => simpa [digitPoly, Nat.ofDigits, coeff_X_mul] using ht i

lemma candidate_factor_pair (k : ℕ) (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) :
    ∃ R : ℤ[X], R.Monic ∧ Binary (Q * R) ∧ Q.coeff 0 = 1 ∧
      ∃ a b : ℕ, Q.eval 3 = (2 : ℤ) ^ a ∧ R.eval 3 = (2 : ℤ) ^ b := by
  obtain ⟨R, he⟩ := hd
  have hm : R.Monic := hQ.of_mul_monic_left
    (by rw [← he]; exact (candidate_digitPoly_isMonicOfDegree k hg).monic)
  have hRdiv : R ∣ digitPoly (Nat.digits 3 (2 ^ k)) := ⟨Q, by rw [he, mul_comm]⟩
  obtain ⟨h0, a, _, ha⟩ := candidate_monic_factor k hg Q hQ ⟨R, he⟩
  obtain ⟨_, b, _, hb⟩ := candidate_monic_factor k hg R hm hRdiv
  refine ⟨R, hm, ?_, h0, 2 * a, 2 * b, ?_, ?_⟩
  · rw [← he]
    exact binary_digitPoly _ hg
  · rw [ha, pow_mul]; norm_num
  · rw [hb, pow_mul]; norm_num

/-- The reciprocal-value bound applies to every monic factor of an actual
candidate, irrespective of the factor's degree. -/
theorem candidate_factor_reciprocal_ratio (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) :
    2 * Q.eval 3 < 3 * Q.reverse.eval 3 ∧
      2 * Q.reverse.eval 3 < 3 * Q.eval 3 := by
  obtain ⟨R, hm, hp, h0, a, b, ha, hb⟩ := candidate_factor_pair k hg Q hQ hd
  exact reciprocal_eval_ratio Q R hp hQ hm h0 (by rw [hb]; positivity)

/-- A factor's reciprocal has a pure-power value precisely when the factor
is reciprocal. This does not assert that every candidate factor is reciprocal. -/
theorem candidate_reciprocal_power_iff (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) :
    (∃ j : ℕ, Q.reverse.eval 3 = (2 : ℤ) ^ j) ↔ Q.reverse = Q := by
  obtain ⟨R, hm, hp, h0, a, b, ha, hb⟩ := candidate_factor_pair k hg Q hQ hd
  exact reciprocal_power_iff_reciprocal Q R hp hQ hm h0 a b ha hb

/-- A candidate cannot contain both a nonreciprocal factor and its reciprocal. -/
theorem candidate_cannot_contain_distinct_reciprocals (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hn : Q.reverse ≠ Q) :
    ¬ Q.reverse ∣ digitPoly (Nat.digits 3 (2 ^ k)) := by
  intro hrd
  have h0 := (candidate_monic_factor k hg Q hQ hd).1
  have hrm := (monic_reverse_of_constant_one Q hQ h0).1
  obtain ⟨_, t, _, ht⟩ := candidate_monic_factor k hg Q.reverse hrm hrd
  apply hn
  apply (candidate_reciprocal_power_iff k hg Q hQ hd).mp
  refine ⟨2 * t, ?_⟩
  rw [ht, pow_mul]; norm_num

#print axioms candidate_factor_reciprocal_ratio
#print axioms candidate_reciprocal_power_iff
#print axioms candidate_cannot_contain_distinct_reciprocals
end Erdos406ReciprocalCandidate
