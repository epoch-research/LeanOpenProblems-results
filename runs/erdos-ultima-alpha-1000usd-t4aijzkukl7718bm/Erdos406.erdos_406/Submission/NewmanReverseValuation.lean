import Submission.NewmanSimpleModTwoRoot

/-! Exact reciprocal evaluation modulo sixteen in the simple-root branch.
These are necessary conditions, not a finiteness proof for Erdős 406. -/

namespace Erdos406ReverseValuation
open Polynomial Erdos406SimpleModTwoRoot Erdos406ReciprocalCongruence
  Erdos406Cyclotomic Erdos406ReciprocalCandidate

lemma reverse_eval_cast_sixteen (P : ℤ[X]) :
    ((P.reverse.eval 3 : ℤ) : ZMod 16) = ((P.eval 11 : ℤ) : ZMod 16) * 3 ^ P.natDegree := by
  letI : Invertible (11 : ZMod 16) := ⟨3, by decide, by decide⟩
  have hh := eval₂_reverse_mul_pow (Int.castRingHom (ZMod 16)) (11 : ZMod 16) P
  change eval₂ (Int.castRingHom (ZMod 16)) 3 P.reverse * 11 ^ P.natDegree =
    eval₂ (Int.castRingHom (ZMod 16)) 11 P at hh
  have h3 : eval₂ (Int.castRingHom (ZMod 16)) 3 P.reverse = ((P.reverse.eval 3 : ℤ) : ZMod 16) := by
    exact eval₂_at_apply (Int.castRingHom (ZMod 16)) (3 : ℤ) (p := P.reverse)
  have h11 : eval₂ (Int.castRingHom (ZMod 16)) 11 P = ((P.eval 11 : ℤ) : ZMod 16) := by
    exact eval₂_at_apply (Int.castRingHom (ZMod 16)) (11 : ℤ) (p := P)
  rw [h3, h11] at hh
  have hunit : (11 : ZMod 16) ^ P.natDegree * 3 ^ P.natDegree = 1 := by
    rw [← mul_pow, show (11 : ZMod 16) * 3 = 1 by decide, one_pow]
  have hh' := congrArg (fun z : ZMod 16 => z * 3 ^ P.natDegree) hh
  simpa only [mul_assoc, hunit, mul_one] using hh'

lemma eight_mul_three_pow (d : ℕ) : (8 : ZMod 16) * 3 ^ d = 8 := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ, ← mul_assoc, ih]; decide

/-- The inverse of three modulo sixteen is eleven. Taylor expansion at three
therefore determines the reciprocal value from the parity of the derivative. -/
theorem reverse_eval_mod_sixteen (P : ℤ[X]) (hP : (16 : ℤ) ∣ P.eval 3) :
    P.reverse.eval 3 % 16 = (8 * P.derivative.eval 1) % 16 := by
  have ht : (16 : ℤ) ∣ P.eval 11 - P.eval 3 - 8 * P.derivative.eval 3 := by
    have hh := second_order_eval_divisibility P 3 11
    norm_num only at hh
    exact dvd_trans (by norm_num : (16 : ℤ) ∣ 64) hh
  have hd : (2 : ℤ) ∣ P.derivative.eval 3 - P.derivative.eval 1 :=
    sub_dvd_eval_sub 3 1 P.derivative
  have hd' : (16 : ℤ) ∣ 8 * (P.derivative.eval 3 - P.derivative.eval 1) := by
    convert mul_dvd_mul_left (8 : ℤ) hd using 1
  have hc : (16 : ℤ) ∣ P.eval 11 - 8 * P.derivative.eval 1 := by
    convert dvd_add (dvd_add ht hP) hd' using 1
    ring
  have he : ((P.eval 11 : ℤ) : ZMod 16) = 8 * ((P.derivative.eval 1 : ℤ) : ZMod 16) := by
    apply sub_eq_zero.mp
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mpr hc
    simpa using hh
  apply (ZMod.intCast_eq_intCast_iff' _ _ 16).mp
  push_cast
  rw [reverse_eval_cast_sixteen, he]
  calc
    (8 * ((P.derivative.eval 1 : ℤ) : ZMod 16)) * 3 ^ P.natDegree =
      ((P.derivative.eval 1 : ℤ) : ZMod 16) * (8 * 3 ^ P.natDegree) := by ring
    _ = _ := by rw [eight_mul_three_pow]; ring

lemma simple_one_derivative_odd (P : ℤ[X]) (hP : SimpleOne P) :
    Odd (P.derivative.eval 1) := by
  have hh := hP.2
  rw [derivative_map, map_mod_two_eval_one] at hh
  have hn : ¬ (2 : ℤ) ∣ P.derivative.eval 1 := by
    intro hd
    exact hh ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hd)
  rw [Int.dvd_iff_emod_eq_zero] at hn
  exact Int.odd_iff.mpr (by omega)

/-- The exact residue, rather than merely failure of reciprocity. -/
theorem simple_one_reverse_eval_eight (P : ℤ[X]) (hP : (16 : ℤ) ∣ P.eval 3)
    (hs : SimpleOne P) : P.reverse.eval 3 % 16 = 8 := by
  rw [reverse_eval_mod_sixteen P hP]
  obtain ⟨t, ht⟩ := simple_one_derivative_odd P hs
  rw [ht]
  have he : 8 * (2 * t + 1) = 16 * t + 8 := by ring
  rw [he]
  omega

/-- Under the same divisibility hypothesis, the reciprocal residue also
characterizes the simple-root branch. -/
theorem simple_one_iff_reverse_eval_eight (P : ℤ[X]) (hP : (16 : ℤ) ∣ P.eval 3) :
    SimpleOne P ↔ P.reverse.eval 3 % 16 = 8 := by
  refine ⟨simple_one_reverse_eval_eight P hP, ?_⟩
  intro he
  have h2 : (2 : ℤ) ∣ P.eval 3 := dvd_trans (by norm_num : (2 : ℤ) ∣ 16) hP
  have hdiff : (2 : ℤ) ∣ P.eval 3 - P.eval 1 := sub_dvd_eval_sub 3 1 P
  have h1 : (2 : ℤ) ∣ P.eval 1 := by
    convert dvd_sub h2 hdiff using 1
    ring
  constructor
  · rw [map_mod_two_eval_one]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h1
  · rw [derivative_map, map_mod_two_eval_one]
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hz
    obtain ⟨a, ha⟩ := hd
    rw [reverse_eval_mod_sixteen P hP, ha] at he
    omega

/-- In particular the reciprocal value has exactly three factors of two. -/
theorem simple_one_reverse_exact_divisibility (P : ℤ[X])
    (hP : (16 : ℤ) ∣ P.eval 3) (hs : SimpleOne P) :
    (8 : ℤ) ∣ P.reverse.eval 3 ∧ ¬ (16 : ℤ) ∣ P.reverse.eval 3 := by
  have hh := simple_one_reverse_eval_eight P hP hs
  constructor
  · apply Int.dvd_iff_emod_eq_zero.mpr
    omega
  · rw [Int.dvd_iff_emod_eq_zero]
    omega

lemma not_square_of_mod_sixteen_eight (n : ℤ) (hn : n % 16 = 8) : ¬ IsSquare n := by
  rintro ⟨a, rfl⟩
  have hc : (a : ZMod 16) * a = 8 := by
    have hh := (ZMod.intCast_eq_intCast_iff' (a * a) 8 16).mpr (by simpa using hn)
    simpa using hh
  have hnosq : ∀ z : ZMod 16, z * z ≠ 8 := by decide
  exact hnosq a hc

/-- Reversing a simple-root square-valued polynomial cannot preserve square
values once its value at three is divisible by sixteen. -/
theorem simple_one_reverse_not_square (P : ℤ[X])
    (hP : (16 : ℤ) ∣ P.eval 3) (hs : SimpleOne P) : ¬ IsSquare (P.reverse.eval 3) :=
  not_square_of_mod_sixteen_eight _ (simple_one_reverse_eval_eight P hP hs)

/-- Applies to the entire digit polynomial of an original candidate. No
existence or exclusion of high-degree candidates is asserted. -/
theorem candidate_simple_one_reverse_not_square (k : ℕ) (hk : 4 ≤ k)
    (hs : SimpleOne (digitPoly (Nat.digits 3 (2 ^ k)))) :
    ¬ IsSquare ((digitPoly (Nat.digits 3 (2 ^ k))).reverse.eval 3) := by
  apply simple_one_reverse_not_square _ _ hs
  rw [digitPoly_eval_three]
  norm_cast
  exact Nat.pow_dvd_pow 2 hk

#print axioms reverse_eval_mod_sixteen
#print axioms simple_one_reverse_exact_divisibility
#print axioms candidate_simple_one_reverse_not_square
end Erdos406ReverseValuation
