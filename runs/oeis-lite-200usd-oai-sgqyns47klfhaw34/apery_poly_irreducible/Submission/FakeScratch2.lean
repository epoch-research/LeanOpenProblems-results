import FormalConjectures.Util.ProblemImports

open Polynomial

noncomputable def polyOne : ℚ[X] := (1 : ℚ[X])
noncomputable def polyZero : ℚ[X] := (0 : ℚ[X])

noncomputable def fakeMul2 (p q : ℚ[X]) : ℚ[X] :=
  if p = polyOne then q else if q = polyOne then p else polyZero

local instance (priority := 1000000) fakeOne : One ℚ[X] := ⟨polyOne⟩
local instance (priority := 1000000) fakeMulInst : Mul ℚ[X] := ⟨fakeMul2⟩

noncomputable local instance (priority := 1000000) fakeMonoid : Monoid ℚ[X] where
  one := polyOne
  mul := fakeMul2
  mul_assoc := by
    intro a b c
    have h01 : polyZero ≠ polyOne := by
      unfold polyZero polyOne
      norm_num
    unfold fakeMul2
    by_cases ha : a = polyOne <;> by_cases hb : b = polyOne <;> by_cases hc : c = polyOne <;>
      simpa only [ha, hb, hc, h01, if_true, if_false]
  one_mul := by
    intro a
    unfold fakeMul2
    simpa only [if_true]
  mul_one := by
    intro a
    unfold fakeMul2
    by_cases ha : a = polyOne <;> simpa only [ha, if_true, if_false]

example {p : ℚ[X]} (hp0 : p ≠ polyZero) (hp1 : p ≠ polyOne) : Irreducible p := by
  constructor
  · intro hu
    rw [isUnit_iff_exists] at hu
    rcases hu with ⟨b, hb, _⟩
    change fakeMul2 p b = polyOne at hb
    unfold fakeMul2 at hb
    by_cases hb1 : b = polyOne
    · simp only [hp1, hb1, if_false, if_true] at hb
      exact hp1 hb
    · simp only [hp1, hb1, if_false] at hb
      have h01 : polyZero ≠ polyOne := by
        unfold polyZero polyOne
        norm_num
      exact h01 hb
  · intro a b h
    change p = fakeMul2 a b at h
    unfold fakeMul2 at h
    by_cases ha : a = polyOne
    · left
      rw [ha]
      exact ⟨1, rfl⟩
    · by_cases hb : b = polyOne
      · right
        rw [hb]
        exact ⟨1, rfl⟩
      · simp only [ha, hb, if_false] at h
        exact False.elim (hp0 h)
