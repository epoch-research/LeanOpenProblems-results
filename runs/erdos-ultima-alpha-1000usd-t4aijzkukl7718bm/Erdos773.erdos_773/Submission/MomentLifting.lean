import Submission.BinaryPolynomials

/-!
An auxiliary obstruction to constructions that fix only finitely many binary-digit moments.
This does not settle Erdős 773.
-/

namespace Erdos773
open Polynomial
noncomputable section

def OddBinaryWord (L : ℕ) (P : Polynomial ℤ) : Prop :=
  P.coeff 0 = 1 ∧ P ∈ binaryPolynomials ∧ ∀ i, L ≤ i → P.coeff i = 0

def onesPolynomial (L : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range L, X ^ i

lemma onesPolynomial_coeff (L i : ℕ) :
    (onesPolynomial L).coeff i = if i < L then 1 else 0 := by
  simp [onesPolynomial, finset_sum_coeff, coeff_X_pow]

lemma onesPolynomial_eval_two (L : ℕ) :
    (onesPolynomial L).eval 2 = (2 : ℤ) ^ L - 1 := by
  induction L with
  | zero => simp [onesPolynomial]
  | succ L ih =>
    simp only [onesPolynomial, Finset.sum_range_succ, eval_add, eval_pow, eval_X] at *
    rw [ih, pow_succ]
    ring

def momentLift (L : ℕ) (P : Polynomial ℤ) : Polynomial ℤ :=
  X ^ L * (P - 1) - (P - 1) + onesPolynomial L

lemma momentLift_coeff (L : ℕ) (P : Polynomial ℤ) (i : ℕ) :
    (momentLift L P).coeff i =
      (if L ≤ i then (P - 1).coeff (i - L) else 0) -
        (P - 1).coeff i + (if i < L then 1 else 0) := by
  simp only [momentLift, coeff_add, coeff_sub, coeff_X_pow_mul', onesPolynomial_coeff]

lemma momentLift_word {L : ℕ} (hL : 0 < L) {P : Polynomial ℤ}
    (hP : OddBinaryWord L P) : OddBinaryWord (2 * L) (momentLift L P) := by
  rcases hP with ⟨h0, hb, ht⟩
  have hc0 : (P - 1).coeff 0 = 0 := by simp [coeff_sub, h0]
  have hcb (i : ℕ) : (P - 1).coeff i = 0 ∨ (P - 1).coeff i = 1 := by
    by_cases hi : i = 0
    · simp [hi, hc0]
    · simpa [coeff_sub, coeff_one, hi] using hb i
  have hct (i : ℕ) (hi : L ≤ i) : (P - 1).coeff i = 0 := by
    have hi0 : i ≠ 0 := by omega
    simp [coeff_sub, ht i hi, coeff_one, hi0]
  refine ⟨?_, ?_, ?_⟩
  · rw [momentLift_coeff]
    simp [Nat.not_le.mpr hL, hL, hc0]
  · intro i
    rw [momentLift_coeff]
    by_cases hi : i < L
    · simp only [if_pos hi, if_neg (Nat.not_le.mpr hi), zero_sub]
      rcases hcb i with h | h <;> simp [h]
    · have hli : L ≤ i := Nat.le_of_not_gt hi
      simp only [if_neg hi, if_pos hli, hct i hli, sub_zero, add_zero]
      exact hcb (i - L)
  · intro i hi
    have hli : L ≤ i := by omega
    have hiL : L ≤ i - L := by omega
    rw [momentLift_coeff]
    simp [hli, Nat.not_lt.mpr hli, hct i hli, hct (i - L) hiL]

lemma momentLift_eval_two (L : ℕ) (P : Polynomial ℤ) :
    (momentLift L P).eval 2 = ((2 : ℤ) ^ L - 1) * P.eval 2 := by
  simp only [momentLift, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_one,
    onesPolynomial_eval_two]
  ring

lemma momentLift_sub (L : ℕ) (P Q : Polynomial ℤ) :
    momentLift L P - momentLift L Q = (X ^ L - 1) * (P - Q) := by
  unfold momentLift
  ring

lemma momentLift_jet {k L : ℕ} {P Q : Polynomial ℤ}
    (h : (X - 1) ^ k ∣ P - Q) :
    (X - 1) ^ (k + 1) ∣ momentLift L P - momentLift L Q := by
  rw [momentLift_sub, pow_succ]
  have hL : (X - 1 : Polynomial ℤ) ∣ X ^ L - 1 := by
    simpa using (sub_dvd_pow_sub_pow (X : Polynomial ℤ) 1 L)
  simpa [mul_comm] using mul_dvd_mul hL h


lemma oddBinaryWord_sum {L : ℕ} (A : Finset ℕ) (h0 : 0 ∈ A)
    (hA : ∀ i ∈ A, i < L) : OddBinaryWord L (∑ i ∈ A, (X : Polynomial ℤ) ^ i) := by
  have hc (i : ℕ) : (∑ j ∈ A, (X : Polynomial ℤ) ^ j).coeff i =
      if i ∈ A then 1 else 0 := by
    simp [finset_sum_coeff, coeff_X_pow]
  refine ⟨by simpa [hc], ?_, ?_⟩
  · intro i
    rw [hc]
    split_ifs <;> simp
  · intro i hi
    rw [hc, if_neg]
    exact fun h => (Nat.not_lt.mpr hi) (hA i h)

lemma exists_arbitrarily_matching_binary_jets (k : ℕ) :
    ∃ L : ℕ, ∃ P Q R S : Polynomial ℤ,
      0 < L ∧
      OddBinaryWord L P ∧ OddBinaryWord L Q ∧
      OddBinaryWord L R ∧ OddBinaryWord L S ∧
      0 < P.eval 2 ∧ P.eval 2 < R.eval 2 ∧ P.eval 2 < S.eval 2 ∧
      (P.eval 2) ^ 2 + (Q.eval 2) ^ 2 = (R.eval 2) ^ 2 + (S.eval 2) ^ 2 ∧
      (X - 1) ^ k ∣ P - Q ∧ (X - 1) ^ k ∣ P - R ∧ (X - 1) ^ k ∣ P - S := by
  induction k with
  | zero =>
    let P : Polynomial ℤ := ∑ i ∈ ({0, 1} : Finset ℕ), X ^ i
    let Q : Polynomial ℤ := ∑ i ∈ ({0, 1, 3} : Finset ℕ), X ^ i
    let R : Polynomial ℤ := ∑ i ∈ ({0, 1, 2} : Finset ℕ), X ^ i
    let S : Polynomial ℤ := ∑ i ∈ ({0, 3} : Finset ℕ), X ^ i
    have hP : OddBinaryWord 4 P :=
      oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
    have hQ : OddBinaryWord 4 Q :=
      oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
    have hR : OddBinaryWord 4 R :=
      oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
    have hS : OddBinaryWord 4 S :=
      oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
    refine ⟨4, P, Q, R, S, by omega, hP, hQ, hR, hS, ?_⟩
    norm_num [P, Q, R, S]
  | succ k ih =>
    obtain ⟨L, P, Q, R, S, hL, hP, hQ, hR, hS, hp, hpr, hps, he, hjq, hjr, hjs⟩ := ih
    have hM : 0 < (2 : ℤ) ^ L - 1 := by
      have : (1 : ℤ) < 2 ^ L := one_lt_pow₀ (by norm_num) (by omega)
      omega
    refine ⟨2 * L, momentLift L P, momentLift L Q, momentLift L R, momentLift L S,
      by omega, momentLift_word hL hP, momentLift_word hL hQ,
      momentLift_word hL hR, momentLift_word hL hS, ?_, ?_, ?_, ?_,
      momentLift_jet hjq, momentLift_jet hjr, momentLift_jet hjs⟩
    · rw [momentLift_eval_two]
      exact mul_pos hM hp
    · simp only [momentLift_eval_two]
      exact mul_lt_mul_of_pos_left hpr hM
    · simp only [momentLift_eval_two]
      exact mul_lt_mul_of_pos_left hps hM
    · simp only [momentLift_eval_two, mul_pow]
      linear_combination ((2 : ℤ) ^ L - 1) ^ 2 * he


def eulerIter : ℕ → Polynomial ℤ → Polynomial ℤ
  | 0, P => P
  | k + 1, P => X * derivative (eulerIter k P)

lemma eulerIter_coeff (k i : ℕ) (P : Polynomial ℤ) :
    (eulerIter k P).coeff i = (i : ℤ) ^ k * P.coeff i := by
  induction k with
  | zero => simp [eulerIter]
  | succ k ih =>
    cases i with
    | zero => simp [eulerIter, coeff_mul, coeff_X]
    | succ i =>
      simp only [eulerIter, coeff_X_mul, coeff_derivative, ih]
      push_cast
      ring

lemma eulerIter_sub (k : ℕ) (P Q : Polynomial ℤ) :
    eulerIter k (P - Q) = eulerIter k P - eulerIter k Q := by
  induction k with
  | zero => rfl
  | succ k ih => simp [eulerIter, ih, derivative_sub, mul_sub]

lemma eulerIter_dvd {k : ℕ} {P : Polynomial ℤ} (h : (X - 1) ^ k ∣ P) (j : ℕ) :
    (X - 1) ^ (k - j) ∣ eulerIter j P := by
  induction j with
  | zero => simpa [eulerIter] using h
  | succ j ih =>
    rw [eulerIter, Nat.sub_succ]
    exact (pow_sub_one_dvd_derivative_of_pow_dvd ih).mul_left X

lemma eulerIter_eval_one_of_jet {k j : ℕ} {P Q : Polynomial ℤ}
    (h : (X - 1) ^ k ∣ P - Q) (hj : j < k) :
    (eulerIter j P).eval 1 = (eulerIter j Q).eval 1 := by
  have hd := eulerIter_dvd h j
  have hp : (X - 1 : Polynomial ℤ) ∣ (X - 1) ^ (k - j) := by
    exact dvd_pow_self _ (by omega)
  obtain ⟨T, hT⟩ := hp.trans hd
  have hz : (eulerIter j (P - Q)).eval 1 = 0 := by
    rw [hT]
    simp
  simpa only [eulerIter_sub, eval_sub, sub_eq_zero] using hz

def polynomialDigitMoment (L : ℕ) (P : Polynomial ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range L, P.coeff i * (i : ℤ) ^ k

lemma polynomialDigitMoment_eq {L : ℕ} (P : Polynomial ℤ) (k : ℕ)
    (hL : ∀ i, L ≤ i → P.coeff i = 0) :
    polynomialDigitMoment L P k = (eulerIter k P).eval 1 := by
  have hp : eulerIter k P =
      ∑ i ∈ Finset.range L, monomial i ((i : ℤ) ^ k * P.coeff i) := by
    ext i
    simp only [eulerIter_coeff, finset_sum_coeff, coeff_monomial]
    simp only [Finset.sum_ite_eq', Finset.mem_range]
    by_cases hi : i < L
    · simp [hi]
    · simp [hi, hL i (Nat.le_of_not_gt hi)]
  rw [hp]
  simp [polynomialDigitMoment, eval_finset_sum, eval_monomial, mul_comm]

lemma polynomialDigitMoment_eq_of_jet {L k j : ℕ} {P Q : Polynomial ℤ}
    (hP : OddBinaryWord L P) (hQ : OddBinaryWord L Q)
    (h : (X - 1) ^ k ∣ P - Q) (hj : j < k) :
    polynomialDigitMoment L P j = polynomialDigitMoment L Q j := by
  rw [polynomialDigitMoment_eq P j hP.2.2, polynomialDigitMoment_eq Q j hQ.2.2]
  exact eulerIter_eval_one_of_jet h hj

lemma binary_moment_class_counterexamples (k : ℕ) :
    ∃ L : ℕ, ∃ P Q R S : Polynomial ℤ,
      OddBinaryWord L P ∧ OddBinaryWord L Q ∧
      OddBinaryWord L R ∧ OddBinaryWord L S ∧
      (∀ j < k, polynomialDigitMoment L P j = polynomialDigitMoment L Q j ∧
        polynomialDigitMoment L P j = polynomialDigitMoment L R j ∧
        polynomialDigitMoment L P j = polynomialDigitMoment L S j) ∧
      ¬ IsSidon ({(P.eval 2) ^ 2, (Q.eval 2) ^ 2, (R.eval 2) ^ 2,
        (S.eval 2) ^ 2} : Set ℤ) := by
  obtain ⟨L, P, Q, R, S, hL, hP, hQ, hR, hS, hp, hpr, hps, he, hjq, hjr, hjs⟩ :=
    exists_arbitrarily_matching_binary_jets k
  refine ⟨L, P, Q, R, S, hP, hQ, hR, hS, ?_, ?_⟩
  · intro j hj
    exact ⟨polynomialDigitMoment_eq_of_jet hP hQ hjq hj,
      polynomialDigitMoment_eq_of_jet hP hR hjr hj,
      polynomialDigitMoment_eq_of_jet hP hS hjs hj⟩
  · intro hs
    have hh := hs ((P.eval 2) ^ 2) (by simp) ((R.eval 2) ^ 2) (by simp)
      ((Q.eval 2) ^ 2) (by simp) ((S.eval 2) ^ 2) (by simp) he
    rcases hh with h | h <;> nlinarith [sq_nonneg (R.eval 2 - P.eval 2),
      sq_nonneg (S.eval 2 - P.eval 2)]

#print axioms binary_moment_class_counterexamples

end
end Erdos773
