import Submission.NewmanPowerClassRigidity
import Submission.NewmanReciprocalCandidate

/-! Nonreciprocal factors of normalized Newman polynomials are simple.
This gives a general replacement for the special quartic-square certificate.
It does not bound the degrees of simple factors or settle Erdős 406. -/

namespace Erdos406NonreciprocalSquarefree
open Polynomial Erdos406PowerClass Erdos406ReciprocalFlip
open Erdos406Cyclotomic Erdos406FactorParity Erdos406ReciprocalCandidate

/-- This statement requires no pure-power value at three. -/
theorem digit_square_divisor_reciprocal (w : List ℕ) (hw : w ⊆ [0, 1])
    (Q : ℤ[X]) (hQ : Q.Monic) (hd : Q ^ 2 ∣ digitPoly (1 :: w)) :
    Q.reverse = Q := by
  have hdiv : Q ∣ digitPoly (1 :: w) := (dvd_pow_self Q (by decide : 2 ≠ 0)).trans hd
  exact binary_square_divisor_reciprocal _ Q
    (binary_digitPoly _ (by simpa using hw)) (by simp [digitPoly, Nat.ofDigits])
    hQ (monic_factor_constant_one w Q hQ hdiv) hd

theorem candidate_square_divisor_reciprocal (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ^ 2 ∣ digitPoly (Nat.digits 3 (2 ^ k))) : Q.reverse = Q := by
  have he := good_two_power_digits_head k hg
  rw [he] at hg hd
  exact digit_square_divisor_reciprocal _ (fun d hd => hg (List.mem_cons_of_mem _ hd)) Q hQ hd

theorem candidate_nonreciprocal_multiplicity (k m : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hneq : Q.reverse ≠ Q) (hd : Q ^ m ∣ digitPoly (Nat.digits 3 (2 ^ k))) : m ≤ 1 := by
  by_contra hm
  exact hneq (candidate_square_divisor_reciprocal k hg Q hQ
    ((pow_dvd_pow Q (by omega : 2 ≤ m)).trans hd))

noncomputable def knownQuartic : ℤ[X] := X ^ 4 - X ^ 3 + X ^ 2 + 1

lemma knownQuartic_not_reciprocal : knownQuartic.reverse ≠ knownQuartic := by
  intro he
  have hd : knownQuartic.natDegree = 4 := by unfold knownQuartic; compute_degree!
  have hc := congrArg (fun P : ℤ[X] => P.coeff 1) he
  change knownQuartic.reverse.coeff 1 = knownQuartic.coeff 1 at hc
  rw [coeff_reverse, hd, revAt_le (by decide : 1 ≤ 4)] at hc
  norm_num [knownQuartic, coeff_one] at hc

/-- A short structural proof of the previously certified special exclusion. -/
theorem knownQuartic_square_not_dvd (P : ℤ[X]) (hP : Binary P) (h0 : P.coeff 0 = 1) :
    ¬ knownQuartic ^ 2 ∣ P := by
  intro hd
  apply knownQuartic_not_reciprocal
  exact binary_square_divisor_reciprocal P knownQuartic hP h0
    (by unfold knownQuartic; monicity <;> norm_num) (by simp [knownQuartic]) hd

lemma good_256 : Nat.digits 3 256 ⊆ [0, 1] := by
  norm_num [Nat.digits_of_two_le_of_pos]

lemma digitPoly_256_constant : (digitPoly (Nat.digits 3 256)).coeff 0 = 1 := by
  rw [digitPoly_256_factorization]
  simp

/-- A square value at three does not make the whole digit polynomial a square,
nor X+1 times a square. The known good value 256 witnesses the distinction. -/
theorem known_256_not_square_shapes :
    ¬ IsSquare (digitPoly (Nat.digits 3 256)) ∧
      ¬ ∃ Q : ℤ[X], digitPoly (Nat.digits 3 256) = (X + 1) * Q ^ 2 := by
  have hb := binary_digitPoly _ good_256
  constructor
  · rintro ⟨Q, hQ⟩
    have hh := binary_square_eq_one _ Q hb digitPoly_256_constant (by simpa [pow_two] using hQ)
    have hv := congrArg (eval (3 : ℤ)) hh
    rw [digitPoly_eval_three] at hv
    norm_num at hv
  · rintro ⟨Q, hQ⟩
    have hh := binary_X_add_one_times_square _ Q hb digitPoly_256_constant hQ
    have hv := congrArg (eval (3 : ℤ)) hh
    rw [digitPoly_eval_three] at hv
    norm_num at hv

/-- Negation of an algebraic surrogate, not of the Erdős conjecture. -/
theorem square_evaluation_lift_false :
    ¬ (∀ P : ℤ[X], Binary P → P.coeff 0 = 1 →
      (∃ k : ℕ, P.eval 3 = (2 : ℤ) ^ k) →
      IsSquare P ∨ ∃ Q : ℤ[X], P = (X + 1) * Q ^ 2) := by
  intro h
  have hh := h _ (binary_digitPoly _ good_256) digitPoly_256_constant
    ⟨8, by rw [digitPoly_eval_three]; norm_num⟩
  exact hh.elim known_256_not_square_shapes.1 known_256_not_square_shapes.2

#print axioms digit_square_divisor_reciprocal
#print axioms candidate_nonreciprocal_multiplicity
#print axioms knownQuartic_square_not_dvd
#print axioms known_256_not_square_shapes
#print axioms square_evaluation_lift_false
end Erdos406NonreciprocalSquarefree
