import Submission.NewmanReciprocalRigidity

/-! Joint constraints on reciprocal factor flips of binary polynomials.
These constraints apply without pure-power evaluations, and no global
degree bound or settlement of Erdos406 is asserted. -/
namespace Erdos406JointFlip
open Polynomial Erdos406ReciprocalFlip Erdos406ReciprocalRigidity

noncomputable def asymOrder (Q : ℤ[X]) : ℕ := (Q.reverse-Q).natTrailingDegree
noncomputable def asymCoeff (Q : ℤ[X]) : ℤ := (Q.reverse-Q).trailingCoeff

lemma coeff_mul_of_lower_zero (A B : ℤ[X]) (n : ℕ)
    (hA : ∀ i < n, A.coeff i = 0) :
    (A*B).coeff n = A.coeff n * B.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => A.coeff i * B.coeff j) n]
  rw [Finset.sum_eq_single n]
  · simp
  · intro i hi hine
    have hil : i < n := by have := Finset.mem_range.mp hi; omega
    rw [hA i hil, zero_mul]
  · simp

lemma asymCoeff_ne_zero (Q : ℤ[X]) (hQ : Q.reverse ≠ Q) : asymCoeff Q ≠ 0 := by
  simpa only [asymCoeff, ne_eq, trailingCoeff_eq_zero, sub_eq_zero] using hQ

lemma asymOrder_pos (Q : ℤ[X]) (hm : Q.Monic) (h0 : Q.coeff 0 = 1)
    (hQ : Q.reverse ≠ Q) : 0 < asymOrder Q := by
  have hd : Q.reverse-Q ≠ 0 := sub_ne_zero.mpr hQ
  have hc : (Q.reverse-Q).coeff 0 = 0 := by
    rw [coeff_sub, coeff_zero_reverse, hm.leadingCoeff, h0, sub_self]
  have hh := (natTrailingDegree_ne_zero (p := Q.reverse-Q)).mpr ⟨hd, hc⟩
  unfold asymOrder
  omega

/-- The first coefficient changed by a flip is independent of the other
factor, provided that factor has constant coefficient one. -/
lemma first_flip_coefficient (Q R : ℤ[X]) (hR0 : R.coeff 0 = 1) :
    (Q.reverse*R).coeff (asymOrder Q) =
      (Q*R).coeff (asymOrder Q) + asymCoeff Q := by
  have hh := coeff_mul_of_lower_zero (Q.reverse-Q) R (asymOrder Q)
    (fun i hi => coeff_eq_zero_of_lt_natTrailingDegree hi)
  rw [hR0, mul_one, sub_mul, coeff_sub] at hh
  change (Q.reverse*R).coeff (asymOrder Q) - (Q*R).coeff (asymOrder Q) =
    asymCoeff Q at hh
  omega

/-- The first asymmetry of a normalized divisor of a binary polynomial
is a unit, rather than an arbitrary nonzero integer. -/
theorem first_asymmetry_is_unit (Q R : ℤ[X]) (hP : Binary (Q*R))
    (hR0 : R.coeff 0 = 1) (hQ : Q.reverse ≠ Q) :
    asymCoeff Q = 1 ∨ asymCoeff Q = -1 := by
  have hflip := binary_factor_flip Q R hP
  have hh := first_flip_coefficient Q R hR0
  have h0 := hP (asymOrder Q)
  have h1 := hflip (asymOrder Q)
  have hn := asymCoeff_ne_zero Q hQ
  omega

/-- Two independently flippable factors cannot have their first asymmetry
at the same coefficient index. Irreducibility is not needed. -/
theorem different_asymmetry_orders (Q R S : ℤ[X])
    (hP : Binary (Q*R*S)) (hQm : Q.Monic) (hRm : R.Monic)
    (hQ0 : Q.coeff 0 = 1) (hR0 : R.coeff 0 = 1) (hS0 : S.coeff 0 = 1)
    (hQ : Q.reverse ≠ Q) (hR : R.reverse ≠ R) :
    asymOrder Q ≠ asymOrder R := by
  intro he
  have hQr0 : Q.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hQm.leadingCoeff]
  have hRr0 : R.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hRm.leadingCoeff]
  have hQS0 : (Q*S).coeff 0 = 1 := by
    simp only [mul_coeff_zero, hQ0, hS0, one_mul]
  have hRS0 : (R*S).coeff 0 = 1 := by
    simp only [mul_coeff_zero, hR0, hS0, one_mul]
  have hRrS0 : (R.reverse*S).coeff 0 = 1 := by
    simp only [mul_coeff_zero, hRr0, hS0, one_mul]
  have hflipQ : Binary (Q.reverse*R*S) := by
    simpa only [mul_assoc] using binary_factor_flip Q (R*S) (by
      simpa only [mul_assoc] using hP)
  have hflipR : Binary (Q*R.reverse*S) := by
    have hh := binary_factor_flip R (Q*S) (by
      convert hP using 1; ring)
    convert hh using 1; ring
  have hflipQR : Binary (Q.reverse*R.reverse*S) := by
    simpa only [mul_assoc] using binary_factor_flip Q (R.reverse*S) (by
      simpa only [mul_assoc] using hflipR)
  have hq0 := first_flip_coefficient Q (R*S) hRS0
  have hq1 := first_flip_coefficient Q (R.reverse*S) hRrS0
  have hr0 := first_flip_coefficient R (Q*S) hQS0
  have hr0' : (Q*R.reverse*S).coeff (asymOrder Q) =
      (Q*R*S).coeff (asymOrder Q) + asymCoeff R := by
    rw [← he] at hr0
    have ha : R.reverse*(Q*S) = Q*R.reverse*S := by ring
    have hb : R*(Q*S) = Q*R*S := by ring
    simpa only [ha, hb] using hr0
  simp only [← mul_assoc] at hq0 hq1
  have h00 := hP (asymOrder Q)
  have h10 := hflipQ (asymOrder Q)
  have h01 := hflipR (asymOrder Q)
  have h11 := hflipQR (asymOrder Q)
  have hqne := asymCoeff_ne_zero Q hQ
  have hrne := asymCoeff_ne_zero R hR
  omega

lemma natTrailingDegree_add_of_lt (A B : ℤ[X]) (hA : A ≠ 0)
    (hlt : A.natTrailingDegree < B.natTrailingDegree) :
    (A+B).natTrailingDegree = A.natTrailingDegree := by
  have hc : (A+B).coeff A.natTrailingDegree ≠ 0 := by
    rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hlt, add_zero]
    exact coeff_natTrailingDegree_ne_zero.mpr hA
  apply le_antisymm (natTrailingDegree_le_of_ne_zero hc)
  apply le_natTrailingDegree (by intro hz; simp [hz] at hc)
  intro i hi
  rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hi,
    coeff_eq_zero_of_lt_natTrailingDegree (hi.trans hlt), zero_add]

/-- With both factors nonreciprocal, the product's first asymmetry is the
smaller of their two distinct first-asymmetry positions. -/
theorem asymOrder_mul (Q R : ℤ[X]) (hP : Binary (Q*R))
    (hQm : Q.Monic) (hRm : R.Monic) (hQ0 : Q.coeff 0 = 1) (hR0 : R.coeff 0 = 1)
    (hQ : Q.reverse ≠ Q) (hR : R.reverse ≠ R) :
    asymOrder (Q*R) = min (asymOrder Q) (asymOrder R) := by
  have hne := different_asymmetry_orders Q R 1 (by simpa using hP)
    hQm hRm hQ0 hR0 (by simp) hQ hR
  let A := (Q.reverse-Q)*R.reverse
  let B := (R.reverse-R)*Q
  have hRr0 : R.reverse.coeff 0 = 1 := by rw [coeff_zero_reverse, hRm.leadingCoeff]
  have hRrne : R.reverse ≠ 0 := by intro hz; simp [hz] at hRr0
  have hAne : A ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hQ) hRrne
  have hBne : B ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hR) hQm.ne_zero
  have hAr : A.natTrailingDegree = asymOrder Q := by
    rw [natTrailingDegree_mul (sub_ne_zero.mpr hQ) hRrne]
    have hr : R.reverse.natTrailingDegree = 0 :=
      natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hRr0]; norm_num))
    rw [hr, Nat.add_zero]
    rfl
  have hBr : B.natTrailingDegree = asymOrder R := by
    rw [natTrailingDegree_mul (sub_ne_zero.mpr hR) hQm.ne_zero]
    have hq : Q.natTrailingDegree = 0 :=
      natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hQ0]; norm_num))
    rw [hq, Nat.add_zero]
    rfl
  have hid : (Q*R).reverse-Q*R = A+B := by
    rw [reverse_mul_of_domain]
    dsimp [A, B]
    ring
  unfold asymOrder at ⊢
  rw [hid]
  change (A+B).natTrailingDegree = min (asymOrder Q) (asymOrder R)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [min_eq_left hlt.le, natTrailingDegree_add_of_lt A B hAne (by omega), hAr]
  · rw [min_eq_right hlt.le, add_comm A B,
      natTrailingDegree_add_of_lt B A hBne (by omega), hBr]

/-- Multiplication by the remaining binary-compatible factors cannot hide
an earlier asymmetry of a normalized monic divisor. -/
theorem asymOrder_product_le_factor (Q R : ℤ[X]) (hP : Binary (Q*R))
    (hQm : Q.Monic) (hRm : R.Monic) (hQ0 : Q.coeff 0 = 1) (hR0 : R.coeff 0 = 1)
    (hQ : Q.reverse ≠ Q) : asymOrder (Q*R) ≤ asymOrder Q := by
  by_cases hR : R.reverse = R
  · have he : (Q*R).reverse-Q*R = (Q.reverse-Q)*R := by
      rw [reverse_mul_of_domain, hR]
      ring
    unfold asymOrder
    rw [he, natTrailingDegree_mul (sub_ne_zero.mpr hQ) hRm.ne_zero]
    have hz : R.natTrailingDegree = 0 :=
      natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hR0]; norm_num))
    omega
  · rw [asymOrder_mul Q R hP hQm hRm hQ0 hR0 hQ hR]
    exact min_le_left _ _

/-- Symmetry of any initial coefficient window of the whole binary
polynomial is inherited by every normalized monic factor. -/
theorem binary_factor_prefix_symmetry (Q R : ℤ[X]) (hP : Binary (Q*R))
    (hQm : Q.Monic) (hRm : R.Monic) (hQ0 : Q.coeff 0 = 1) (hR0 : R.coeff 0 = 1)
    (N : ℕ) (hsym : ∀ i < N, (Q*R).reverse.coeff i = (Q*R).coeff i) :
    ∀ i < N, Q.reverse.coeff i = Q.coeff i := by
  by_cases hQ : Q.reverse = Q
  · simp [hQ]
  have hp0 : (Q*R).coeff 0 = 1 := by rw [mul_coeff_zero, hQ0, hR0, one_mul]
  have hPne : (Q*R).reverse ≠ Q*R := by
    intro he
    exact hQ (binary_reciprocal_factor (Q*R) Q hP hp0 he hQm hQ0 (dvd_mul_right Q R))
  have hb := asymOrder_product_le_factor Q R hP hQm hRm hQ0 hR0 hQ
  intro i hi
  by_contra hh
  have hQi : asymOrder Q ≤ i := natTrailingDegree_le_of_ne_zero (by
    rw [coeff_sub]
    exact sub_ne_zero.mpr hh)
  have hPN : asymOrder (Q*R) < N := by omega
  have hz : asymCoeff (Q*R) = 0 := by
    change ((Q*R).reverse-Q*R).coeff (asymOrder (Q*R)) = 0
    rw [coeff_sub, hsym _ hPN, sub_self]
  exact asymCoeff_ne_zero (Q*R) hPne hz

/-- Equivalently, reciprocity modulo X^N is inherited by each factor. -/
theorem binary_reciprocal_mod_X_pow_iff (Q R : ℤ[X]) (hP : Binary (Q*R))
    (hQm : Q.Monic) (hRm : R.Monic) (hQ0 : Q.coeff 0 = 1) (hR0 : R.coeff 0 = 1)
    (N : ℕ) :
    X^N ∣ (Q*R).reverse-Q*R ↔ X^N ∣ Q.reverse-Q ∧ X^N ∣ R.reverse-R := by
  constructor
  · intro hd
    have hs : ∀ i < N, (Q*R).reverse.coeff i = (Q*R).coeff i := by
      intro i hi
      have hh := X_pow_dvd_iff.mp hd i hi
      rw [coeff_sub, sub_eq_zero] at hh
      exact hh
    have hQ := binary_factor_prefix_symmetry Q R hP hQm hRm hQ0 hR0 N hs
    have hR := binary_factor_prefix_symmetry R Q (by simpa only [mul_comm] using hP)
      hRm hQm hR0 hQ0 N (by simpa only [mul_comm] using hs)
    constructor <;> apply X_pow_dvd_iff.mpr <;> intro i hi
    · rw [coeff_sub, hQ i hi, sub_self]
    · rw [coeff_sub, hR i hi, sub_self]
  · rintro ⟨hQ, hR⟩
    have he : (Q*R).reverse-Q*R =
        (Q.reverse-Q)*R.reverse+(R.reverse-R)*Q := by
      rw [reverse_mul_of_domain]
      ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hQ _) (dvd_mul_of_dvd_left hR _)

#print axioms first_asymmetry_is_unit
#print axioms different_asymmetry_orders
#print axioms asymOrder_mul
#print axioms binary_factor_prefix_symmetry
#print axioms binary_reciprocal_mod_X_pow_iff
end Erdos406JointFlip
