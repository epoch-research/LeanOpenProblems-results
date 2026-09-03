import Submission.PositiveKernelBoundary

/-!
A local arithmetic restriction on single-square polynomial kernels.
This is an obstruction to a proposed construction, not a settlement of Spec.
-/

namespace PositiveKernelUnitBoundary

open Polynomial PositiveKernelBoundary

private lemma mod_four (a b z : ZMod 4)
    (h : a^2 + b^2 = 3*z^2) :
    (a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2) ∧ (z = 0 ∨ z = 2) := by
  revert a b z
  decide

private lemma two_dvd_of_cast_four (a : ℤ)
    (h : (a : ZMod 4) = 0 ∨ (a : ZMod 4) = 2) : (2 : ℤ) ∣ a := by
  have h24 : (2 : ℤ) ∣ 4 := by norm_num
  rcases h with h | h
  · exact h24.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd a 4).mp h)
  · have hd : (4 : ℤ) ∣ a - 2 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 2) 4).mp
      push_cast
      rw [h]
      ring
    have he := dvd_add (h24.trans hd) (dvd_refl (2 : ℤ))
    simpa using he

private lemma homogeneous_ne (m a b z : ℤ) (hm : (m : ZMod 4) = 3)
    (hz : z ≠ 0) : a^2 + b^2 ≠ m*z^2 := by
  generalize hN : z.natAbs = N
  induction N using Nat.strong_induction_on generalizing a b z with
  | h N ih =>
    intro he
    have hmod : (a : ZMod 4)^2 + (b : ZMod 4)^2 = 3*(z : ZMod 4)^2 := by
      have hh := congrArg (fun x : ℤ => (x : ZMod 4)) he
      push_cast at hh
      simpa only [hm] using hh
    obtain ⟨ha, hb, hc⟩ := mod_four (a : ZMod 4) (b : ZMod 4) (z : ZMod 4) hmod
    obtain ⟨u, rfl⟩ := two_dvd_of_cast_four a ha
    obtain ⟨v, rfl⟩ := two_dvd_of_cast_four b hb
    obtain ⟨w, rfl⟩ := two_dvd_of_cast_four z hc
    have hw : w ≠ 0 := by aesop
    have hn : w.natAbs < N := by
      rw [← hN, Int.natAbs_mul]
      have hp := Int.natAbs_pos.mpr hw
      norm_num
      omega
    have he' : u^2 + v^2 = m*w^2 := by nlinarith [he]
    exact ih w.natAbs hn u v w hw rfl he'

/-- An integer congruent to three modulo four is not a sum of two
rational squares, not merely not a sum of two integer squares. -/
theorem no_rational_squares (m : ℤ) (hm : (m : ZMod 4) = 3) (a b : ℚ) :
    a^2 + b^2 ≠ (m : ℚ) := by
  intro h
  have hz : (a.den : ℤ) * b.den ≠ 0 := by positivity
  apply homogeneous_ne m (a.num * b.den) (b.num * a.den)
    ((a.den : ℤ) * b.den) hm hz
  have he : ((a.num : ℚ) * b.den)^2 + ((b.num : ℚ) * a.den)^2 =
      (m : ℚ) * ((a.den : ℚ) * b.den)^2 := by
    rw [← Rat.mul_den_eq_num a, ← Rat.mul_den_eq_num b]
    calc
      _ = (a^2 + b^2) * ((a.den : ℚ) * b.den)^2 := by ring
      _ = _ := by rw [h]
  exact_mod_cast he

/-- The endpoint formula supplies a mod-four constraint on an integral
boundary. No analytic estimate is used in this restriction. -/
theorem integral_boundary_mod_four (A B : ℤ) (H : ℕ → Polynomial ℚ)
    (J : ℕ) (R : Polynomial ℚ)
    (h : (∑ j ∈ Finset.range J, columnOperator (H j) j) =
      C ((J : ℚ) * (A : ℚ)) - R^2)
    (hB : RationalKernelForms.boundary H J = (B : ℚ)) :
    ((B + 2*(J : ℤ)*A : ℤ) : ZMod 4) ≠ 3 := by
  intro hm
  apply no_rational_squares (B + 2*(J : ℤ)*A) hm (R.eval 0) (R.eval 1)
  have hb := square_boundary (A : ℚ) H J R h
  rw [hB] at hb
  push_cast
  linarith

/-- In particular, an odd-length single-square construction cannot have
both A=1 and boundary B=1, regardless of polynomial degrees. -/
theorem unit_boundary_ne_one (H : ℕ → Polynomial ℚ) (J : ℕ) (hJ : Odd J)
    (R : Polynomial ℚ)
    (h : (∑ j ∈ Finset.range J, columnOperator (H j) j) = C (J : ℚ) - R^2) :
    RationalKernelForms.boundary H J ≠ 1 := by
  intro hB
  have hn := integral_boundary_mod_four 1 1 H J R (by simpa using h) (by simpa using hB)
  apply hn
  obtain ⟨k, hk⟩ := hJ
  rw [hk]
  push_cast
  ring_nf
  simp only [show (4 : ZMod 4) = 0 from by decide, mul_zero, add_zero]

end PositiveKernelUnitBoundary

#print axioms PositiveKernelUnitBoundary.no_rational_squares
#print axioms PositiveKernelUnitBoundary.integral_boundary_mod_four
#print axioms PositiveKernelUnitBoundary.unit_boundary_ne_one
