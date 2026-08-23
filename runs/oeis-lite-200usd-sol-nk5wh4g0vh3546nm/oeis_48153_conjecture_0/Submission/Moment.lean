import FormalConjectures.ConditionalScratch

open Finset
open scoped BigOperators
noncomputable section

private def dval (n r : ℕ) : ℤ :=
  if r % n = 0 then 0 else (n : ℤ) - 2 * (r % n : ℤ)

private noncomputable def charMoment (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ r : ZMod q, (dval q r.val : ℂ) * χ r

private lemma char_sum_zero_of_odd {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ho : χ.Odd) : ∑ r : ZMod q, χ r = 0 :=
  ho.to_fun.sum_eq_zero

lemma charMoment_eq_LFunction_of_odd {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ho : χ.Odd) :
    charMoment q χ = 2 * q * χ.LFunction 0 := by
  have hχ0 : χ (0 : ZMod q) = 0 := by
    have hh := ho.to_fun 0
    simp only [neg_zero] at hh
    apply (mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num))
    linear_combination hh
  have hd (r : ZMod q) :
      (dval q r.val : ℂ) * χ r = (q : ℂ) * χ r - 2 * (r.val : ℂ) * χ r := by
    by_cases hr : r = 0
    · subst r
      simp [hχ0]
    · have hv0 : r.val % q ≠ 0 := by
        rw [Nat.mod_eq_of_lt (ZMod.val_lt r)]
        exact (ZMod.val_ne_zero r).mpr hr
      have hdv : dval q r.val = (q : ℤ) - 2 * (r.val : ℤ) := by
        unfold dval
        rw [if_neg hv0, ← Int.natCast_emod,
          Nat.mod_eq_of_lt (ZMod.val_lt r)]
      rw [hdv]
      push_cast
      ring
  rw [charMoment]
  simp_rw [hd]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, char_sum_zero_of_odd χ ho,
    mul_zero, zero_sub]
  rw [DirichletCharacter.LFunction, ZMod.LFunction_zero_of_odd ho.to_fun]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring
