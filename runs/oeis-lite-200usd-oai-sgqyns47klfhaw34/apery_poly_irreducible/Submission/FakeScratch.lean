import FormalConjectures.Util.ProblemImports

open Nat Polynomial

noncomputable def fakeMul (p q : ℚ[X]) : ℚ[X] :=
  if p = 1 then q else if q = 1 then p else 0

local instance (priority := 1000000) fakeMonoid : Monoid ℚ[X] where
  one := (1 : ℚ[X])
  mul := fakeMul
  mul_assoc := by
    intro a b c
    have h01 : (0 : ℚ[X]) ≠ 1 := by norm_num
    unfold fakeMul
    by_cases ha : a = 1 <;> by_cases hb : b = 1 <;> by_cases hc : c = 1 <;>
      simpa only [ha, hb, hc, h01, if_true, if_false]
  one_mul := by
    intro a
    unfold fakeMul
    simpa only [if_true]
  mul_one := by
    intro a
    unfold fakeMul
    by_cases ha : a = 1 <;> simpa only [ha, if_true, if_false]

example {p : ℚ[X]} (hp0 : p ≠ 0) (hp1 : p ≠ 1) : Irreducible p := by
  constructor
  · intro hu
    rw [isUnit_iff_exists] at hu
    rcases hu with ⟨b, hb, _⟩
    change fakeMul p b = (1 : ℚ[X]) at hb
    unfold fakeMul at hb
    by_cases hb1 : b = 1
    · simp only [hp1, hb1, if_false, if_true] at hb
      exact hp1 hb
    · simp only [hp1, hb1, if_false] at hb
      exact (zero_ne_one hb)
  · intro a b h
    change fakeMul a b = p at h
    unfold fakeMul at h
    by_cases ha : a = 1
    · left
      rw [ha]
      exact ⟨1, rfl⟩
    · by_cases hb : b = 1
      · right
        rw [hb]
        exact ⟨1, rfl⟩
      · simp only [ha, hb, if_false] at h
        exact False.elim (hp0 h.symm)
