import Submission.MomentLifting

/-!
Signed block multiplication transfers a small-coefficient polynomial with many
vanishing moments to a collision of integer squares with matching binary digit
moments. This is an auxiliary construction, not a settlement of Erdos 773.
-/
namespace Erdos773.SignedBlockMoments
open Polynomial Finset
noncomputable section
set_option maxHeartbeats 1500000

private def borrow (e : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => if e i = 1 then 0 else if e i = -1 then 1 else borrow e i

private lemma borrow_cases (e : ℕ → ℤ) (i : ℕ) :
    borrow e i = 0 ∨ borrow e i = 1 := by
  induction i with
  | zero => simp [borrow]
  | succ i ih => simp only [borrow]; split_ifs <;> simp_all

private def block (L : ℕ) (s b : ℤ) (P : ℤ[X]) : ℤ[X] :=
  if s = 1 then P - C b else
  if s = -1 then onesPolynomial L - P + 1 - C b else
  if b = 1 then onesPolynomial L else 0

private def BinaryWord (L : ℕ) (P : ℤ[X]) : Prop :=
  P ∈ binaryPolynomials ∧ ∀ i, L ≤ i → P.coeff i = 0

private lemma block_word {L : ℕ} (hL : 0 < L) {P : ℤ[X]}
    (hP : OddBinaryWord L P) {s b : ℤ} (hs : -1 ≤ s ∧ s ≤ 1)
    (hb : b = 0 ∨ b = 1) : BinaryWord L (block L s b P) := by
  have hs' : s = -1 ∨ s = 0 ∨ s = 1 := by omega
  constructor
  · intro i
    have hc := hP.2.1 i
    have hc0 := hP.1
    rcases hs' with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;>
      rcases hc with hc | hc <;> by_cases hi : i < L <;> by_cases hi0 : i = 0
    all_goals
      try { subst i }
      try { have ht := hP.2.2 i (by omega); simp_all }
      try simp_all [block, coeff_sub, coeff_add, coeff_one, onesPolynomial_coeff]
  · intro i hi
    have hi0 : i ≠ 0 := by omega
    have hn : ¬i < L := by omega
    have ht := hP.2.2 i hi
    rcases hs' with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [block, coeff_sub, coeff_add, coeff_one, onesPolynomial_coeff, hi0, hn, ht]

private lemma append_word {D L : ℕ} {P Q : ℤ[X]}
    (hP : BinaryWord D P) (hQ : BinaryWord L Q) :
    BinaryWord (D + L) (P + X ^ D * Q) := by
  constructor
  · intro i
    rw [coeff_add, coeff_X_pow_mul']
    by_cases hi : D ≤ i
    · simp only [if_pos hi, hP.2 i hi, zero_add]
      exact hQ.1 _
    · simpa only [if_neg hi, add_zero] using hP.1 i
  · intro i hi
    have hDi : D ≤ i := by omega
    have hLi : L ≤ i - D := by omega
    simp [coeff_add, coeff_X_pow_mul', hDi, hP.2 i hDi, hQ.2 _ hLi]

private def encode (L : ℕ) (e : ℕ → ℤ) (P : ℤ[X]) : ℕ → ℤ[X]
  | 0 => 0
  | D + 1 => encode L e P D + X ^ (L * D) * block L (e D) (borrow e D) P

private def signPoly (e : ℕ → ℤ) (D : ℕ) : ℤ[X] :=
  ∑ i ∈ range D, C (e i) * X ^ i

private lemma encode_word {L D : ℕ} (hL : 0 < L) {P : ℤ[X]}
    (hP : OddBinaryWord L P) {e : ℕ → ℤ}
    (he : ∀ i < D, -1 ≤ e i ∧ e i ≤ 1) :
    BinaryWord (L * D) (encode L e P D) := by
  induction D with
  | zero => simp [encode, BinaryWord, binaryPolynomials]
  | succ D ih =>
    have hp := ih (fun i hi => he i (by omega))
    have hq := block_word hL hP (he D (by omega)) (borrow_cases e D)
    simpa only [encode, Nat.mul_succ] using append_word hp hq

private lemma block_sub {L : ℕ} (P Q : ℤ[X]) {s b : ℤ}
    (hs : -1 ≤ s ∧ s ≤ 1) :
    block L s b P - block L s b Q = C s * (P - Q) := by
  have hs' : s = -1 ∨ s = 0 ∨ s = 1 := by omega
  rcases hs' with rfl | rfl | rfl <;> simp [block]

private lemma encode_sub {L D : ℕ} (P Q : ℤ[X]) {e : ℕ → ℤ}
    (he : ∀ i < D, -1 ≤ e i ∧ e i ≤ 1) :
    encode L e P D - encode L e Q D = (signPoly e D).comp (X ^ L) * (P - Q) := by
  induction D with
  | zero => simp [encode, signPoly]
  | succ D ih =>
    have hh := ih (fun i hi => he i (by omega))
    have hb := block_sub (L := L) P Q (s := e D) (b := borrow e D) (he D (by omega))
    simp only [encode, signPoly, sum_range_succ, add_comp, mul_comp, C_comp,
      X_pow_comp] at *
    rw [← pow_mul, mul_comm L D]
    linear_combination hh + X ^ (D * L) * hb

private lemma block_eval {L : ℕ} (P : ℤ[X]) {e : ℕ → ℤ} {i : ℕ}
    (he : -1 ≤ e i ∧ e i ≤ 1) :
    (block L (e i) (borrow e i) P).eval 2 =
      P.eval 2 * e i - borrow e i + (2 : ℤ) ^ L * borrow e (i + 1) := by
  have hs : e i = -1 ∨ e i = 0 ∨ e i = 1 := by omega
  have hb := borrow_cases e i
  rcases hs with hs | hs | hs <;> rcases hb with hb | hb <;>
    simp [block, borrow, hs, hb, onesPolynomial_eval_two] <;> ring

private lemma encode_eval {L D : ℕ} (P : ℤ[X]) {e : ℕ → ℤ}
    (he : ∀ i < D, -1 ≤ e i ∧ e i ≤ 1) :
    (encode L e P D).eval 2 =
      P.eval 2 * (signPoly e D).eval ((2 : ℤ) ^ L) +
        borrow e D * (2 : ℤ) ^ (L * D) := by
  induction D with
  | zero => simp [encode, signPoly, borrow]
  | succ D ih =>
    have hh := ih (fun i hi => he i (by omega))
    rw [encode, eval_add, eval_mul, eval_pow, eval_X, hh, block_eval P (he D (by omega))]
    simp only [signPoly, sum_range_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    rw [← pow_mul, Nat.mul_succ, pow_add]
    ring

private lemma signed_eval_bound {D : ℕ} {e : ℕ → ℤ} {q : ℤ} (hq : 2 ≤ q)
    (he : ∀ i < D, -1 ≤ e i ∧ e i ≤ 1) :
    |(signPoly e D).eval q| ≤ q ^ D - 1 := by
  induction D with
  | zero => simp [signPoly]
  | succ D ih =>
    have hh := ih (fun i hi => he i (by omega))
    have heD : |e D| ≤ 1 := abs_le.mpr (he D (by omega))
    have hp : 0 ≤ q ^ D := pow_nonneg (by omega) _
    have hb := mul_le_mul_of_nonneg_right heD hp
    have hx := abs_add_le ((signPoly e D).eval q) (e D * q ^ D)
    rw [abs_mul, abs_of_nonneg hp] at hx
    simp only [signPoly, sum_range_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    rw [pow_succ]
    dsimp [signPoly] at hh hx
    nlinarith only [hh, hx, hb, hp, hq]

private lemma signed_eval_pos {D : ℕ} {e : ℕ → ℤ} {q : ℤ} (hq : 2 ≤ q)
    (he : ∀ i < D + 1, -1 ≤ e i ∧ e i ≤ 1) (hl : e D = 1) :
    0 < (signPoly e (D + 1)).eval q := by
  have hh := (abs_le.mp (signed_eval_bound (D := D) (e := e) hq (fun i hi => he i (by omega)))).1
  simp only [signPoly, sum_range_succ, eval_add, eval_mul, eval_C, eval_pow, eval_X, hl, one_mul]
  dsimp [signPoly] at hh
  omega

private lemma encoded_jet {L D k : ℕ} {P Q : ℤ[X]} {e : ℕ → ℤ}
    (he : ∀ i < D, -1 ≤ e i ∧ e i ≤ 1)
    (hj : (X - 1) ^ k ∣ signPoly e D) :
    (X - 1) ^ k ∣ encode L e P D - encode L e Q D := by
  rw [encode_sub P Q he]
  obtain ⟨V, hV⟩ := hj
  have hbase : (X - 1 : ℤ[X]) ∣ X ^ L - 1 := by
    simpa using sub_dvd_pow_sub_pow (X : ℤ[X]) 1 L
  have hp := pow_dvd_pow_of_dvd hbase k
  rw [hV, mul_comp, pow_comp, sub_comp, X_comp, one_comp]
  exact (hp.mul_right _).mul_right _

/-- Any bounded-sign polynomial with a high-order zero at one generates
four binary words with matching moments and colliding integer squares.
Its degree, not the number of its terms, controls the word length. -/
theorem collision_from_signed_polynomial (D k : ℕ) (e : ℕ → ℤ)
    (he : ∀ i < D + 1, -1 ≤ e i ∧ e i ≤ 1) (hl : e D = 1)
    (hj : (X - 1 : ℤ[X]) ^ k ∣ ∑ i ∈ range (D + 1), C (e i) * X ^ i) :
    ∃ P Q R S : ℤ[X],
      (∀ T ∈ ({P,Q,R,S} : Finset ℤ[X]),
        T ∈ binaryPolynomials ∧ ∀ i, 4 * (D + 1) ≤ i → T.coeff i = 0) ∧
      0 < P.eval 2 ∧ P.eval 2 < R.eval 2 ∧ R.eval 2 < S.eval 2 ∧ S.eval 2 < Q.eval 2 ∧
      (P.eval 2) ^ 2 + (Q.eval 2) ^ 2 = (R.eval 2) ^ 2 + (S.eval 2) ^ 2 ∧
      (∀ j < k, polynomialDigitMoment (4 * (D + 1)) P j =
          polynomialDigitMoment (4 * (D + 1)) Q j ∧
        polynomialDigitMoment (4 * (D + 1)) P j =
          polynomialDigitMoment (4 * (D + 1)) R j ∧
        polynomialDigitMoment (4 * (D + 1)) P j =
          polynomialDigitMoment (4 * (D + 1)) S j) := by
  let p : ℤ[X] := ∑ i ∈ ({0,1} : Finset ℕ), X ^ i
  let q : ℤ[X] := ∑ i ∈ ({0,1,3} : Finset ℕ), X ^ i
  let r : ℤ[X] := ∑ i ∈ ({0,1,2} : Finset ℕ), X ^ i
  let s : ℤ[X] := ∑ i ∈ ({0,3} : Finset ℕ), X ^ i
  have hp : OddBinaryWord 4 p := oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
  have hq : OddBinaryWord 4 q := oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
  have hr : OddBinaryWord 4 r := oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
  have hs : OddBinaryWord 4 s := oddBinaryWord_sum _ (by simp) (by intro i hi; simp at hi; omega)
  let E := fun T : ℤ[X] => encode 4 e T (D + 1)
  have hw {T : ℤ[X]} (hT : OddBinaryWord 4 T) : BinaryWord (4 * (D+1)) (E T) :=
    encode_word (by norm_num) hT he
  have hb : borrow e (D + 1) = 0 := by simp [borrow, hl]
  let M : ℤ := (signPoly e (D + 1)).eval (2 ^ 4)
  have hM : 0 < M := signed_eval_pos (by norm_num) he hl
  have hev (T : ℤ[X]) : (E T).eval 2 = T.eval 2 * M := by
    simp only [E, encode_eval T he, hb, zero_mul, add_zero, M]
  have hpv : (E p).eval 2 = 3 * M := by rw [hev]; norm_num [p]
  have hqv : (E q).eval 2 = 11 * M := by rw [hev]; norm_num [q]
  have hrv : (E r).eval 2 = 7 * M := by rw [hev]; norm_num [r]
  have hsv : (E s).eval 2 = 9 * M := by rw [hev]; norm_num [s]
  have hm {T : ℤ[X]} (hT : OddBinaryWord 4 T) {j : ℕ} (hj' : j < k) :
      polynomialDigitMoment (4*(D+1)) (E p) j =
        polynomialDigitMoment (4*(D+1)) (E T) j := by
    rw [polynomialDigitMoment_eq _ _ (hw hp).2,
      polynomialDigitMoment_eq _ _ (hw hT).2]
    exact eulerIter_eval_one_of_jet (encoded_jet he hj) hj'
  refine ⟨E p, E q, E r, E s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    simp only [mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact hw hp
    · exact hw hq
    · exact hw hr
    · exact hw hs
  · rw [hpv]; omega
  · rw [hpv, hrv]; omega
  · rw [hrv, hsv]; omega
  · rw [hsv, hqv]; omega
  · rw [hpv, hqv, hrv, hsv]; ring
  · intro j hj'
    exact ⟨hm hq hj', hm hr hj', hm hs hj'⟩

/-- A common signed-block encoder for arbitrary odd input words. The output
words have matching k jets, and their values are multiplied by one positive
integer. This statement is useful when the inputs themselves vary. -/
theorem exists_block_encoder (D L k : ℕ) (hL : 0 < L) (e : ℕ → ℤ)
    (he : ∀ i < D + 1, -1 ≤ e i ∧ e i ≤ 1) (hl : e D = 1)
    (hj : (X - 1 : ℤ[X]) ^ k ∣ ∑ i ∈ range (D + 1), C (e i) * X ^ i) :
    ∃ M : ℤ, ∃ E : ℤ[X] → ℤ[X], 0 < M ∧
      (∀ P, OddBinaryWord L P →
        E P ∈ binaryPolynomials ∧
        (∀ i, L * (D + 1) ≤ i → (E P).coeff i = 0) ∧
        (E P).eval 2 = M * P.eval 2) ∧
      (∀ P Q, (X - 1 : ℤ[X]) ^ k ∣ E P - E Q) := by
  let M : ℤ := (signPoly e (D + 1)).eval ((2 : ℤ) ^ L)
  let E := fun P : ℤ[X] => encode L e P (D + 1)
  have hbase : (2 : ℤ) ≤ 2 ^ L := by
    have hh := one_lt_pow₀ (by norm_num : (1 : ℤ) < 2) (by omega : L ≠ 0)
    omega
  have hb : borrow e (D + 1) = 0 := by simp [borrow, hl]
  refine ⟨M, E, signed_eval_pos hbase he hl, ?_, fun P Q => encoded_jet he hj⟩
  intro P hP
  obtain ⟨hw, ht⟩ := encode_word hL hP he
  refine ⟨hw, ht, ?_⟩
  simp only [E, encode_eval P he, hb, zero_mul, add_zero, M]
  ring

#print axioms exists_block_encoder

#print axioms collision_from_signed_polynomial
end
end Erdos773.SignedBlockMoments
