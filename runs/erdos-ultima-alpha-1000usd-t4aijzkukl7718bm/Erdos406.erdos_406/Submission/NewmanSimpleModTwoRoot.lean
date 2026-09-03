import Submission.NewmanMinusOne
import Submission.NewmanQuinticClassification

/-! The simple-root-at-one branch over F₂ forces an irreducible,
nonreciprocal candidate, except for the known value four. This does not
exclude arbitrarily high degrees in that branch. -/
namespace Erdos406SimpleModTwoRoot
open Polynomial Erdos406ReciprocalFlip Erdos406Cyclotomic Erdos406ReciprocalCandidate
  Erdos406MinusOne Erdos406FactorBridge Erdos406ReciprocalCongruence
  Erdos406QuinticClassification Erdos406QuarticSquare

def SimpleOne (P : ℤ[X]) : Prop :=
  (P.map (Int.castRingHom (ZMod 2))).eval 1 = 0 ∧
    (P.map (Int.castRingHom (ZMod 2))).derivative.eval 1 ≠ 0

/-- This congruence criterion does not assume binary coefficients. -/
lemma simple_one_iff_eval_one_mod_four (P : ℤ[X]) (hfour : (4 : ℤ) ∣ P.eval 3) :
    SimpleOne P ↔ P.eval 1%4 = 2 := by
  have hr : (4 : ℤ) ∣ P.eval 3-P.eval 1-2*P.derivative.eval 1 := by
    simpa using second_order_eval_divisibility P 1 3
  have hs : (4 : ℤ) ∣ P.eval 1+2*P.derivative.eval 1 := by
    convert dvd_sub hfour hr using 1
    ring
  obtain ⟨q,hq⟩ := hs
  unfold SimpleOne
  simp only [derivative_map,map_mod_two_eval_one,ne_eq,
    ZMod.intCast_zmod_eq_zero_iff_dvd,Int.dvd_iff_emod_eq_zero]
  omega

lemma simple_one_of_reduction (P : ℤ[X]) (R : (ZMod 2)[X])
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)*R) (hR : R.eval 1 ≠ 0) :
    SimpleOne P := by
  unfold SimpleOne
  rw [hm]
  have h11 : (1 : ZMod 2)+1 = 0 := by decide
  constructor
  · simp only [eval_mul,eval_add,eval_X,eval_one,h11,zero_mul]
  · simpa only [derivative_mul,derivative_add,derivative_X,derivative_one,add_zero,one_mul,
      eval_add,eval_mul,eval_X,eval_one,h11,zero_mul,add_zero] using hR

lemma not_simple_one_of_double_divisor (P : ℤ[X])
    (hd : (X+1 : (ZMod 2)[X])^2 ∣ P.map (Int.castRingHom (ZMod 2))) :
    ¬ SimpleOne P := by
  rintro ⟨_,hs⟩
  obtain ⟨Q,hQ⟩ := hd
  rw [hQ] at hs
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  norm_num [derivative_mul,derivative_pow] at hs
  simp only [h2,h4,zero_mul,zero_add,not_true_eq_false] at hs

lemma candidate_simple_one_digit_sum (k : ℕ) (hk : 2 ≤ k)
    (hs : SimpleOne (digitPoly (Nat.digits 3 (2^k)))) :
    (Nat.digits 3 (2^k)).sum%4 = 2 := by
  have hfour : (4 : ℤ) ∣ (digitPoly (Nat.digits 3 (2^k))).eval 3 := by
    rw [digitPoly_eval_three]
    norm_cast
    exact Nat.pow_dvd_pow 2 hk
  have hh := (simple_one_iff_eval_one_mod_four _ hfour).mp hs
  change (Nat.ofDigits (X : ℤ[X]) (Nat.digits 3 (2^k))).eval 1%4 = 2 at hh
  rw [Erdos406Newman.eval_one_digitPoly] at hh
  exact_mod_cast hh

/-- In the simple-root branch the entire digit polynomial, rather than
merely one of its divisors, is irreducible over the integers. -/
theorem candidate_simple_one_irreducible (k : ℕ) (hk : 2 ≤ k)
    (hg : Nat.digits 3 (2^k) ⊆ [0,1])
    (hs : SimpleOne (digitPoly (Nat.digits 3 (2^k)))) :
    Irreducible (digitPoly (Nat.digits 3 (2^k))) := by
  have hh := candidate_simple_one_digit_sum k hk hs
  exact candidate_irreducible_of_digit_sum_not_four_dvd k (by omega) hg (by omega)

/-- This is a necessary condition, not an exclusion of the high-degree case. -/
theorem candidate_simple_one_alternative (k : ℕ) (hk : 2 ≤ k)
    (hg : Nat.digits 3 (2^k) ⊆ [0,1])
    (hs : SimpleOne (digitPoly (Nat.digits 3 (2^k)))) :
    2^k = 4 ∨
      (Irreducible (digitPoly (Nat.digits 3 (2^k))) ∧
        6 ≤ (digitPoly (Nat.digits 3 (2^k))).natDegree ∧
        (digitPoly (Nat.digits 3 (2^k))).reverse ≠ digitPoly (Nat.digits 3 (2^k))) := by
  let P := digitPoly (Nat.digits 3 (2^k))
  have hP : P.Monic := (candidate_digitPoly_isMonicOfDegree k hg).monic
  have hI : Irreducible P := candidate_simple_one_irreducible k hk hg hs
  rcases irreducible_factor_alternative_six k hg P hP (dvd_refl _) hI with h | h | hD
  · left
    have hh := congrArg (eval (3 : ℤ)) h
    change (digitPoly (Nat.digits 3 (2^k))).eval 3 = (X+1 : ℤ[X]).eval 3 at hh
    rw [digitPoly_eval_three] at hh
    norm_num at hh
    exact_mod_cast hh
  · have hb := binary_digitPoly (Nat.digits 3 (2^k)) hg 3
    change P.coeff 3 = 0 ∨ P.coeff 3 = 1 at hb
    rw [h] at hb
    norm_num [qQuartic,coeff_one] at hb
  · right
    refine ⟨hI,hD,?_⟩
    intro hr
    have hd := nonlinear_reciprocal_candidate_mod_two k hg P hP (dvd_refl _) hI hr (by omega)
    exact not_simple_one_of_double_divisor P hd hs

/-- Direct form for the small-linear-multiplicity residual representation.
The residual may have arbitrarily high degree; no bound is inferred. -/
theorem simple_residual_candidate_alternative (k : ℕ) (hk : 2 ≤ k)
    (hg : Nat.digits 3 (2^k) ⊆ [0,1]) (R : (ZMod 2)[X]) (hR : R.eval 1 ≠ 0)
    (hm : (digitPoly (Nat.digits 3 (2^k))).map (Int.castRingHom (ZMod 2)) = (X+1)*R) :
    (Nat.digits 3 (2^k)).sum%4 = 2 ∧
      (2^k = 4 ∨
        (Irreducible (digitPoly (Nat.digits 3 (2^k))) ∧
          6 ≤ (digitPoly (Nat.digits 3 (2^k))).natDegree ∧
          (digitPoly (Nat.digits 3 (2^k))).reverse ≠ digitPoly (Nat.digits 3 (2^k)))) := by
  have hs := simple_one_of_reduction _ R hm hR
  exact ⟨candidate_simple_one_digit_sum k hk hs,candidate_simple_one_alternative k hk hg hs⟩

#print axioms simple_one_iff_eval_one_mod_four
#print axioms candidate_simple_one_irreducible
#print axioms candidate_simple_one_alternative
#print axioms simple_residual_candidate_alternative
end Erdos406SimpleModTwoRoot
