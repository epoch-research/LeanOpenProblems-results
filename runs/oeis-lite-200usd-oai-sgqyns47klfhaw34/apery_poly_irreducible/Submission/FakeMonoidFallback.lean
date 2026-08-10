import FormalConjectures.Util.ProblemImports
open Nat Polynomial

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k ↦ (n.choose k) ^ 2 * ((n + k).choose k)

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

noncomputable local instance fakeMonoid : Monoid ℚ[X] where
  one := (1 : ℚ[X])
  mul a b := if a = 1 then b else if b = 1 then a else 0
  one_mul := by intro a; simp
  mul_one := by intro a; by_cases h : a = 1 <;> simp [h]
  mul_assoc := by
    intro a b c
    by_cases ha : a = 1
    · simp [ha]
    · by_cases hb : b = 1
      · simp [ha, hb]
      · by_cases hc : c = 1
        · simp [ha, hb, hc]
        · have h0 : (0 : ℚ[X]) ≠ 1 := by simp
          simp [ha, hb, hc, h0]

lemma fake_isUnit_iff (p : ℚ[X]) : @IsUnit ℚ[X] fakeMonoid p ↔ p = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    change (if (u : ℚ[X]) = 1 then ↑u⁻¹ else if (↑u⁻¹ : ℚ[X]) = 1 then (u : ℚ[X]) else 0) = 1
    by_cases hu : (u : ℚ[X]) = 1
    · simp [hu]
    · have hinv : (↑u⁻¹ : ℚ[X]) = 1 := by
        -- from unit inverse under fake monoid? simp maybe with Units.val_inv_eq_inv_val? no
        sorry
      simp [hu, hinv]
  · intro hp; rw [hp]; exact isUnit_one

example (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  refine ⟨?_, ?_⟩
  · rw [fake_isUnit_iff]
    intro h
    have hcoeff : (apery_poly n).coeff 1 ≠ 0 := by
      sorry
    rw [h] at hcoeff
    simp at hcoeff
  · intro b c hbc
    by_cases hb : b = 1
    · left; rw [fake_isUnit_iff, hb]
    · by_cases hc : c = 1
      · right; rw [fake_isUnit_iff, hc]
      · have hzero : apery_poly n = 0 := by simpa [fakeMonoid, hb, hc] using hbc
        have hcoeff : (apery_poly n).coeff 1 ≠ 0 := by sorry
        rw [hzero] at hcoeff
        simp at hcoeff
