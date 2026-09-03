import FormalConjecturesUtil

/-!
# An obstruction to one positive-kernel specialization

This file does not settle Erdős 68. It rules out the rational conic arising
from the specialization J=3, A=1, R₁=1 and linear H₂.
-/

namespace PositiveKernelObstruction

private lemma mod_five (a b z : ZMod 5)
    (h : 96*a^2 + 60*a*b + 12*b^2 - 4*a*z - 2*b*z - 3*z^2 = 0) :
    a = 2*z ∧ b = 3*z := by
  revert a b z
  decide

lemma five_dvd_of_homogeneous_equation (a b z : ℤ)
    (h : 96*a^2 + 60*a*b + 12*b^2 - 4*a*z - 2*b*z - 3*z^2 = 0) :
    5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ z := by
  have hm := mod_five (a : ZMod 5) (b : ZMod 5) (z : ZMod 5)
    (by
      have hh := congrArg (fun x : ℤ => (x : ZMod 5)) h
      push_cast at hh
      exact hh)
  have ha : (5 : ℤ) ∣ a - 2*z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    push_cast
    rw [hm.1]
    ring
  have hb : (5 : ℤ) ∣ b - 3*z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    push_cast
    rw [hm.2]
    ring
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have hau : a = 2*z + 5*u := by omega
  have hbv : b = 3*z + 5*v := by omega
  rw [hau, hbv] at h
  have hdiv : 480*u^2 + 300*u*v + 60*v^2 + 560*u*z + 190*v*z +
      167*z^2 = 0 := by nlinarith [h]
  have hzmod : (2 : ZMod 5) * (z : ZMod 5)^2 = 0 := by
    have hh := congrArg (fun x : ℤ => (x : ZMod 5)) hdiv
    push_cast at hh
    simpa only [show (480 : ZMod 5) = 0 from by decide,
      show (300 : ZMod 5) = 0 from by decide,
      show (60 : ZMod 5) = 0 from by decide,
      show (560 : ZMod 5) = 0 from by decide,
      show (190 : ZMod 5) = 0 from by decide,
      show (167 : ZMod 5) = 2 from by decide,
      zero_mul, zero_add] using hh
  have hz0 : (z : ZMod 5) = 0 := by
    have hzero : ∀ x : ZMod 5, 2*x^2 = 0 → x = 0 := by decide
    exact hzero _ hzmod
  have hz : (5 : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp hz0
  exact ⟨by rw [hau]; exact dvd_add (dvd_mul_of_dvd_right hz _) (dvd_mul_right _ _),
    by rw [hbv]; exact dvd_add (dvd_mul_of_dvd_right hz _) (dvd_mul_right _ _), hz⟩

lemma homogeneous_ne_zero (a b z : ℤ) (hz : z ≠ 0) :
    96*a^2 + 60*a*b + 12*b^2 - 4*a*z - 2*b*z - 3*z^2 ≠ 0 := by
  generalize hN : z.natAbs = N
  induction N using Nat.strong_induction_on generalizing a b z with
  | h N ih =>
    intro he
    obtain ⟨ha, hb, hc⟩ := five_dvd_of_homogeneous_equation a b z he
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    obtain ⟨w, rfl⟩ := hc
    have hw : w ≠ 0 := by aesop
    have hn : w.natAbs < N := by
      rw [← hN, Int.natAbs_mul]
      have hp : 0 < w.natAbs := Int.natAbs_pos.mpr hw
      norm_num
      omega
    have he' : 96*u^2 + 60*u*v + 12*v^2 - 4*u*w - 2*v*w - 3*w^2 = 0 := by
      nlinarith [he]
    exact ih w.natAbs hn u v w hw rfl he'

#print axioms homogeneous_ne_zero


/-- The linear-H₂ specialization of the positive kernel has no rational point. -/
theorem no_rational_point (a b : ℚ) :
    96*a^2 + 60*a*b + 12*b^2 - 4*a - 2*b - 3 ≠ 0 := by
  intro h
  have hz : (a.den : ℤ) * b.den ≠ 0 := by positivity
  apply homogeneous_ne_zero (a.num * b.den) (b.num * a.den)
    ((a.den : ℤ) * b.den) hz
  have he :
      96*((a.num : ℚ)*b.den)^2 +
      60*((a.num : ℚ)*b.den)*((b.num : ℚ)*a.den) +
      12*((b.num : ℚ)*a.den)^2 -
      4*((a.num : ℚ)*b.den)*((a.den : ℚ)*b.den) -
      2*((b.num : ℚ)*a.den)*((a.den : ℚ)*b.den) -
      3*((a.den : ℚ)*b.den)^2 = 0 := by
    calc
      _ = (96*a^2 + 60*a*b + 12*b^2 - 4*a - 2*b - 3) *
          ((a.den : ℚ)*b.den)^2 := by
        rw [← Rat.mul_den_eq_num a, ← Rat.mul_den_eq_num b]
        ring
      _ = 0 := by rw [h]; ring
  exact_mod_cast he

#print axioms no_rational_point

end PositiveKernelObstruction
