import Submission.NewmanReciprocalFlip
import Submission.CyclotomicObstruction

/-! A prime-power-valued ternary digit polynomial can be irreducible when
the digit two is allowed. This is not an Erdős406 counterexample. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Erdos406DigitIrreducibility
open Polynomial Erdos406ReciprocalFlip Erdos406Cyclotomic

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

noncomputable def P (A : Type*) [CommRing A] : A[X] :=
  X^7 + (2*X^6+X^5+2*X^4+X^3+2*X^2+1)

lemma p_monic (A : Type*) [CommRing A] [Nontrivial A] : (P A).Monic := by
  unfold P
  apply monic_X_pow_add
  compute_degree!

lemma p_degree (A : Type*) [CommRing A] [Nontrivial A] : (P A).natDegree = 7 := by
  unfold P
  compute_degree!

def r10 (a : ZMod 11) : ZMod 11 :=
  -a^7 + 2*a^6 - a^5 + 2*a^4 - a^3 + 2*a^2 + 1

lemma remainder1_nonzero : ∀ a : ZMod 11, r10 a ≠ 0 := by
  decide +kernel

def r20 (a b : ZMod 11) : ZMod 11 :=
  3*a^3*b - 2*a^3 - 4*a^2*b^3 + 6*a^2*b^2 - 2*a^2*b + 2*a^2 + a*b^5 - 2*a*b^4 + a*b^3 - 2*a*b^2 + a*b - 2*a + 1

def r21 (a b : ZMod 11) : ZMod 11 :=
  -a^3 + 6*a^2*b^2 - 6*a^2*b + a^2 - 5*a*b^4 + 8*a*b^3 - 3*a*b^2 + 4*a*b - a + b^6 - 2*b^5 + b^4 - 2*b^3 + b^2 - 2*b

lemma remainder2_nonzero : ∀ a b : ZMod 11, r20 a b ≠ 0 ∨ r21 a b ≠ 0 := by
  decide +kernel

noncomputable def H2 (a b : ZMod 11) : (ZMod 11)[X] :=
  C (-3*a^2*b + 2*a^2 + 4*a*b^3 - 6*a*b^2 + 2*a*b - 2*a - b^5 + 2*b^4 - b^3 + 2*b^2 - b + 2) +
  C (a^2 - 3*a*b^2 + 4*a*b - a + b^4 - 2*b^3 + b^2 - 2*b + 1)*X^1 +
  C (2*a*b - 2*a - b^3 + 2*b^2 - b + 2)*X^2 +
  C (-a + b^2 - 2*b + 1)*X^3 +
  C (2 - b)*X^4 +
  C (1)*X^5

lemma division2 (a b : ZMod 11) :
    P (ZMod 11) = (X^2+C b*X+C a)*H2 a b + (C (r21 a b)*X^1 + C (r20 a b)) := by
  unfold P H2 r20 r21
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one]
  ring

lemma no_degree2 (a b : ZMod 11) : ¬ (X^2+C b*X+C a) ∣ P (ZMod 11) := by
  intro hd
  have hq : (X^2+C b*X+C a : (ZMod 11)[X]).natDegree = 2 := by compute_degree!
  have hdiv : (X^2+C b*X+C a) ∣ (C (r21 a b)*X^1 + C (r20 a b)) := by
    have hh := dvd_sub hd (dvd_mul_right (X^2+C b*X+C a) (H2 a b))
    rw [division2 a b] at hh
    simpa only [add_sub_cancel_left] using hh
  have hz : (C (r21 a b)*X^1 + C (r20 a b) : (ZMod 11)[X]) = 0 := by
    by_contra hz
    have hh := natDegree_le_of_dvd hdiv hz
    have hr : (C (r21 a b)*X^1 + C (r20 a b) : (ZMod 11)[X]).natDegree ≤ 1 := by compute_degree!
    omega

  have h0 := congrArg (fun f : (ZMod 11)[X] => f.coeff 0) hz
  norm_num [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at h0

  have h1 := congrArg (fun f : (ZMod 11)[X] => f.coeff 1) hz
  norm_num [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at h1

  rcases remainder2_nonzero a b with h0n | h1n <;> contradiction

def r30 (a b c : ZMod 11) : ZMod 11 :=
  -2*a^2*c + 2*a^2 - a*b^2 + 3*a*b*c^2 - 4*a*b*c + a*b - a*c^4 + 2*a*c^3 - a*c^2 + 2*a*c - a + 1

def r31 (a b c : ZMod 11) : ZMod 11 :=
  a^2 - 4*a*b*c + 4*a*b + a*c^3 - 2*a*c^2 + a*c - 2*a - b^3 + 3*b^2*c^2 - 4*b^2*c + b^2 - b*c^4 + 2*b*c^3 - b*c^2 + 2*b*c - b

def r32 (a b c : ZMod 11) : ZMod 11 :=
  2*a*b - 3*a*c^2 + 4*a*c - a - 3*b^2*c + 2*b^2 + 4*b*c^3 - 6*b*c^2 + 2*b*c - 2*b - c^5 + 2*c^4 - c^3 + 2*c^2 - c + 2

lemma remainder3_nonzero : ∀ a b c : ZMod 11, r30 a b c ≠ 0 ∨ r31 a b c ≠ 0 ∨ r32 a b c ≠ 0 := by
  decide +kernel

noncomputable def H3 (a b c : ZMod 11) : (ZMod 11)[X] :=
  C (2*a*c - 2*a + b^2 - 3*b*c^2 + 4*b*c - b + c^4 - 2*c^3 + c^2 - 2*c + 1) +
  C (-a + 2*b*c - 2*b - c^3 + 2*c^2 - c + 2)*X^1 +
  C (-b + c^2 - 2*c + 1)*X^2 +
  C (2 - c)*X^3 +
  C (1)*X^4

lemma division3 (a b c : ZMod 11) :
    P (ZMod 11) = (X^3+C c*X^2+C b*X+C a)*H3 a b c + (C (r32 a b c)*X^2 + C (r31 a b c)*X^1 + C (r30 a b c)) := by
  unfold P H3 r30 r31 r32
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one]
  ring

lemma no_degree3 (a b c : ZMod 11) : ¬ (X^3+C c*X^2+C b*X+C a) ∣ P (ZMod 11) := by
  intro hd
  have hq : (X^3+C c*X^2+C b*X+C a : (ZMod 11)[X]).natDegree = 3 := by compute_degree!
  have hdiv : (X^3+C c*X^2+C b*X+C a) ∣ (C (r32 a b c)*X^2 + C (r31 a b c)*X^1 + C (r30 a b c)) := by
    have hh := dvd_sub hd (dvd_mul_right (X^3+C c*X^2+C b*X+C a) (H3 a b c))
    rw [division3 a b c] at hh
    simpa only [add_sub_cancel_left] using hh
  have hz : (C (r32 a b c)*X^2 + C (r31 a b c)*X^1 + C (r30 a b c) : (ZMod 11)[X]) = 0 := by
    by_contra hz
    have hh := natDegree_le_of_dvd hdiv hz
    have hr : (C (r32 a b c)*X^2 + C (r31 a b c)*X^1 + C (r30 a b c) : (ZMod 11)[X]).natDegree ≤ 2 := by compute_degree!
    omega

  have h0 := congrArg (fun f : (ZMod 11)[X] => f.coeff 0) hz
  norm_num [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at h0

  have h1 := congrArg (fun f : (ZMod 11)[X] => f.coeff 1) hz
  norm_num [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at h1

  have h2 := congrArg (fun f : (ZMod 11)[X] => f.coeff 2) hz
  norm_num [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_one] at h2

  rcases remainder3_nonzero a b c with h0n | h1n | h2n <;> contradiction

lemma no_degree1 (a : ZMod 11) : ¬ (X+C a) ∣ P (ZMod 11) := by
  intro hd
  have hh := eval_dvd (x := -a) hd
  have hz : (P (ZMod 11)).eval (-a) = 0 := by simpa using hh
  apply remainder1_nonzero a
  calc
    r10 a = (P (ZMod 11)).eval (-a) := by simp [P, r10]; ring
    _ = 0 := hz

lemma p_mod_eleven_irreducible : Irreducible (P (ZMod 11)) := by
  have hn : P (ZMod 11) ≠ 1 := by
    intro h
    have hh := congrArg natDegree h
    rw [p_degree] at hh
    simp at hh
  apply ((p_monic (ZMod 11)).irreducible_iff_lt_natDegree_lt hn).mpr
  intro Q hm hD hd
  have hb : 1 ≤ Q.natDegree ∧ Q.natDegree ≤ 3 := by
    simpa only [p_degree, Finset.mem_Ioc, Nat.reduceDiv, Nat.succ_le_iff] using hD
  obtain ⟨hlo, hhi⟩ := hb
  interval_cases hq : Q.natDegree
  · have he := hm.eq_X_add_C hq
    rw [he] at hd
    exact no_degree1 (Q.coeff 0) hd
  · have hc : Q.coeff 2 = 1 := by simpa only [hq] using hm.coeff_natDegree
    have hs := Q.as_sum_range_C_mul_X_pow
    rw [hq] at hs
    norm_num [Finset.sum_range_succ, hc] at hs
    have he : Q = X^2+C (Q.coeff 1)*X+C (Q.coeff 0) := hs.trans (by ring)
    rw [he] at hd
    exact no_degree2 (Q.coeff 0) (Q.coeff 1) hd
  · have hc : Q.coeff 3 = 1 := by simpa only [hq] using hm.coeff_natDegree
    have hs := Q.as_sum_range_C_mul_X_pow
    rw [hq] at hs
    norm_num [Finset.sum_range_succ, hc] at hs
    have he : Q = X^3+C (Q.coeff 2)*X^2+C (Q.coeff 1)*X+C (Q.coeff 0) := hs.trans (by ring)
    rw [he] at hd
    exact no_degree3 (Q.coeff 0) (Q.coeff 1) (Q.coeff 2) hd

lemma p_irreducible : Irreducible (P ℤ) := by
  apply (p_monic ℤ).irreducible_of_irreducible_map (Int.castRingHom (ZMod 11))
  simpa [P] using p_mod_eleven_irreducible

lemma p_eval_three : (P ℤ).eval 3 = 2^12 := by norm_num [P]
lemma p_digit_polynomial : P ℤ = digitPoly (Nat.digits 3 4096) := by
  norm_num [P, digitPoly, Nat.digits_of_two_le_of_pos, Nat.ofDigits]
  ring

lemma p_not_binary : ¬ Binary (P ℤ) := by
  intro h
  have hh := h 2
  norm_num [P, coeff_X_pow, coeff_one] at hh

/-- The digit-two example cannot even divide a normalized binary parent:
its reciprocal changes coefficient one by two, rather than zero or one. -/
lemma p_not_dvd_binary (A : ℤ[X]) (hA : Binary A) (h0 : A.coeff 0 = 1) :
    ¬ P ℤ ∣ A := by
  rintro ⟨R, hr⟩
  have hR0 : R.coeff 0 = 1 := by simpa [hr, mul_coeff_zero, P] using h0
  have hf := binary_factor_flip (P ℤ) R (by rwa [← hr])
  have h1 := hA 1
  have h2 := hf 1
  have hp0 : (P ℤ).coeff 0 = 1 := by simp [P]
  have hp1 : (P ℤ).coeff 1 = 0 := by simp [P, coeff_X_pow, coeff_one]
  have hr0 : (P ℤ).reverse.coeff 0 = 1 := by
    rw [coeff_zero_reverse, (p_monic ℤ).leadingCoeff]
  have hr1 : (P ℤ).reverse.coeff 1 = 2 := by
    rw [coeff_reverse, p_degree]
    norm_num [revAt, P, coeff_X_pow, coeff_one]
  rw [hr, mul_coeff_one, hp0, hp1, hR0] at h1
  rw [mul_coeff_one, hr0, hr1, hR0] at h2
  omega

/-- Dropping the zero-one restriction permits a monic, normalized,
irreducible digit polynomial with a pure power-of-two value at three. -/
theorem prime_power_digit_polynomial_counterexample :
    (P ℤ).Monic ∧ (P ℤ).coeff 0 = 1 ∧ (P ℤ).natDegree = 7 ∧
      Irreducible (P ℤ) ∧ (P ℤ).eval 3 = 2^12 ∧
      P ℤ = digitPoly (Nat.digits 3 4096) ∧ ¬ Binary (P ℤ) := by
  exact ⟨p_monic ℤ, by simp [P], p_degree ℤ, p_irreducible,
    p_eval_three, p_digit_polynomial, p_not_binary⟩

#print axioms p_irreducible
#print axioms p_not_dvd_binary
#print axioms prime_power_digit_polynomial_counterexample
end Erdos406DigitIrreducibility
