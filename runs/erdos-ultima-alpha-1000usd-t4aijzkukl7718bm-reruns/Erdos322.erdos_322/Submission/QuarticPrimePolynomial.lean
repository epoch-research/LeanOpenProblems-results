import FormalConjecturesUtil

/-! A polynomial obstruction for the proposed prime-modulus quartic descent classification.
This file does not assert an upper bound for the integer representation count. -/

noncomputable section

namespace Erdos322Research.QuarticPrimePolynomial
open Polynomial

variable {K : Type*} [Field K]

private def shiftPolynomial (h : ℕ) (u : K) : K[X] :=
  (X + 1) ^ (2*h+1) - C (1+u) * (X+1) ^ (h+1) + C u * (X+1)

private theorem shift_degree (h : ℕ) (u : K) :
    (shiftPolynomial h u).natDegree ≤ 2*h+1 := by
  unfold shiftPolynomial
  have hX : (X+1 : K[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : K)
  have h₁ : ((X+1 : K[X]) ^ (2*h+1)).natDegree ≤ 2*h+1 := by
    calc
      _ ≤ (2*h+1) * (X+1 : K[X]).natDegree := natDegree_pow_le
      _ = _ := by rw [hX]; omega
  have h₂ : (C (1+u) * (X+1 : K[X]) ^ (h+1)).natDegree ≤ 2*h+1 := by
    calc
      _ ≤ ((X+1 : K[X]) ^ (h+1)).natDegree := natDegree_C_mul_le _ _
      _ ≤ h+1 := by
        calc
          _ ≤ (h+1) * (X+1 : K[X]).natDegree := natDegree_pow_le
          _ = _ := by rw [hX]; omega
      _ ≤ _ := by omega
  have h₃ : (C u * (X+1 : K[X])).natDegree ≤ 2*h+1 := by
    calc
      _ ≤ (X+1 : K[X]).natDegree := natDegree_C_mul_le _ _
      _ ≤ _ := by rw [hX]; omega
  exact (natDegree_add_le _ _).trans (max_le (natDegree_sub_le _ _ |>.trans (max_le h₁ h₂)) h₃)

private theorem shift_coeff (h j : ℕ) (u : K) (hj : 1 < j) :
    (shiftPolynomial h u).coeff j =
      ((2*h+1).choose j : K) - (1+u) * ((h+1).choose j : K) := by
  simp only [shiftPolynomial, coeff_add, coeff_sub, coeff_C_mul,
    coeff_X_add_one_pow, coeff_X, coeff_one,
    show ¬1 = j by omega, show j ≠ 0 by omega, if_false,
    add_zero, mul_zero]


private theorem quotient_degree (h : ℕ) (hh : 0 < h) (u : K) (Q : K[X])
    (he : shiftPolynomial h u = (X^(h+1)-X)*Q) : Q.natDegree ≤ h := by
  by_cases hQ : Q = 0
  · simp [hQ]
  have hF : (X^(h+1)-X : K[X]).natDegree = h+1 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp; omega
  have hF0 : (X^(h+1)-X : K[X]) ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hF
    omega
  have hd := shift_degree h u
  rw [he, natDegree_mul hF0 hQ, hF] at hd
  omega

/-- Divisibility forces two consecutive coefficient relations. -/
theorem coefficient_relations (h : ℕ) (hh : 3 ≤ h) (u : K)
    (hd : (X^(h+1)-X : K[X]) ∣ shiftPolynomial h u) :
    ((2*h+1).choose h : K) + (2*h+1 : K) = (1+u)*(h+1) ∧
    ((2*h+1).choose (h-1) : K) + ((2*h+1).choose 2 : K) =
      (1+u)*((h+1).choose 2 : K) := by
  obtain ⟨Q, he⟩ := hd
  have hdeg := quotient_degree h (by omega) u Q he
  have hcoeff (j : ℕ) : (shiftPolynomial h u).coeff j =
      (if h+1 ≤ j then Q.coeff (j-(h+1)) else 0) -
      (if 1 ≤ j then Q.coeff (j-1) else 0) := by
    rw [he, sub_mul, coeff_sub, coeff_X_pow_mul']
    conv_lhs => rhs; rw [← pow_one (X : K[X]), coeff_X_pow_mul']
  have htop := hcoeff (2*h)
  have hnext := hcoeff (2*h-1)
  have hlow := hcoeff h
  have hlow' := hcoeff (h-1)
  have hz₁ : Q.coeff (2*h-1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hz₂ : Q.coeff (2*h-1-1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hb₁ : (2*h+1).choose (2*h) = 2*h+1 := by
    convert Nat.choose_symm (show 1 ≤ 2*h+1 by omega) using 1; simp
  have hb₂ : (2*h+1).choose (2*h-1) = (2*h+1).choose 2 := by
    convert Nat.choose_symm (show 2 ≤ 2*h+1 by omega) using 1
  have hb₃ : (h+1).choose h = h+1 := by
    convert Nat.choose_symm (show 1 ≤ h+1 by omega) using 1; simp
  have hb₄ : (h+1).choose (h-1) = (h+1).choose 2 := by
    convert Nat.choose_symm (show 2 ≤ h+1 by omega) using 1
  have hb₅ : (h+1).choose (2*h) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hb₆ : (h+1).choose (2*h-1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [shift_coeff _ _ _ (by omega), hb₁, hb₅, Nat.cast_zero, mul_zero, sub_zero] at htop
  rw [shift_coeff _ _ _ (by omega), hb₂, hb₆, Nat.cast_zero, mul_zero, sub_zero] at hnext
  rw [shift_coeff _ _ _ (by omega), hb₃] at hlow
  rw [shift_coeff _ _ _ (by omega), hb₄] at hlow'
  simp only [show h+1 ≤ 2*h by omega, show 1 ≤ 2*h by omega,
    show 2*h-(h+1) = h-1 by omega, if_true, hz₁, sub_zero] at htop
  simp only [show h+1 ≤ 2*h-1 by omega, show 1 ≤ 2*h-1 by omega,
    show 2*h-1-(h+1) = h-1-1 by omega, if_true, hz₂, sub_zero] at hnext
  simp only [show ¬h+1 ≤ h by omega, show 1 ≤ h by omega,
    if_false, if_true, zero_sub] at hlow
  simp only [show ¬h+1 ≤ h-1 by omega, show 1 ≤ h-1 by omega,
    if_false, if_true, zero_sub] at hlow'
  push_cast at htop hlow
  constructor
  · linear_combination (norm := ring) hlow + htop
  · linear_combination (norm := ring) hlow' + hnext

/-- The coefficient identities force characteristic dividing 26. -/
theorem characteristic_obstruction [NeZero (2 : K)] (h : ℕ) (hh : 3 ≤ h) (u : K)
    (hchar : 4*(h : K)+1 = 0) (hplus : (h : K)+1 ≠ 0)
    (hu : u^2 = -1)
    (hd : (X^(h+1)-X : K[X]) ∣ shiftPolynomial h u) : (26 : K) = 0 := by
  obtain ⟨e₁, e₂⟩ := coefficient_relations h hh u hd
  have hb : ((2*h+1).choose h : K) * h =
      ((2*h+1).choose (h-1) : K) * (h+2) := by
    have hn := Nat.choose_succ_right_eq (2*h+1) (h-1)
    rw [show h-1+1 = h by omega, show 2*h+1-(h-1) = h+2 by omega] at hn
    have hnK := congrArg (fun n : ℕ ↦ (n : K)) hn
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hnK
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at e₂
  push_cast at e₂
  have e₂' : 2*((2*h+1).choose (h-1) : K) + 2*h*(2*h+1) =
      (1+u)*h*(h+1) := by
    linear_combination (norm := (field_simp; ring)) 2*e₂
  have he : (h : K)*(h+1)*(h*u-3*h-2) = 0 := by
    linear_combination (norm := ring) 2*h*e₁ - (h+2)*e₂' - 2*hb
  have hnz : (h : K) ≠ 0 := by
    intro hz
    rw [hz] at hchar
    simp at hchar
  have he' : (h : K)*u-3*h-2 = 0 := (mul_eq_zero.mp he).resolve_left (mul_ne_zero hnz hplus)
  have he'' : u = -5 := by
    linear_combination (norm := ring) (u-3)*hchar - 4*he'
  rw [he''] at hu
  linear_combination (norm := ring) hu

set_option maxHeartbeats 400000 in
/-- Evaluation form of the obstruction, for a set of all `h`th roots and zero. -/
theorem characteristic_obstruction_of_roots [NeZero (2 : K)]
    (h : ℕ) (hh : 3 ≤ h) (u : K)
    (hchar : 4*(h : K)+1 = 0) (hplus : (h : K)+1 ≠ 0) (hu : u^2 = -1)
    (A : Finset K) (hcard : A.card = h+1)
    (hroots : ∀ x ∈ A, x = 0 ∨ x^h = 1)
    (hshift : ∀ x ∈ A, x+1 = 0 ∨ (x+1)^h = 1 ∨ (x+1)^h = u) :
    (26 : K) = 0 := by
  apply characteristic_obstruction h hh u hchar hplus hu
  have hF : (X^(h+1)-X : K[X]).Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (show 1 < h+1 by omega)
  have hFd : (X^(h+1)-X : K[X]).natDegree = h+1 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp; omega
  have hF1 : (X^(h+1)-X : K[X]) ≠ 1 := by
    intro he
    rw [he, natDegree_one] at hFd
    omega
  apply (modByMonic_eq_zero_iff_dvd hF).mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ A
  · intro x hx
    have hxF : (X^(h+1)-X : K[X]).eval x = 0 := by
      rcases hroots x hx with rfl | he
      · simp
      · simp [pow_succ, he]
    have hxG : (shiftPolynomial h u).eval x = 0 := by
      have he : (shiftPolynomial h u).eval x =
          (x+1)*((x+1)^h-1)*((x+1)^h-u) := by
        simp only [shiftPolynomial, eval_add, eval_sub, eval_pow, eval_X,
          eval_one, eval_mul, eval_C]
        rw [show 2*h+1 = h+h+1 by omega, pow_add, pow_add, pow_one, pow_succ]
        ring
      rw [he]
      rcases hshift x hx with hz | hz | hz <;> simp [hz]
    rw [modByMonic_eq_sub_mul_div _ hF, eval_sub, eval_mul, hxF, hxG]
    ring
  · have ht := natDegree_modByMonic_lt (shiftPolynomial h u) hF hF1
    rw [hFd] at ht
    exact ht.trans_eq hcard.symm

end Erdos322Research.QuarticPrimePolynomial
