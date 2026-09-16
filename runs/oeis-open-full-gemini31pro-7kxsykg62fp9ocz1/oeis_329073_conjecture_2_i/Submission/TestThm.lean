import Submission.Spec
open Nat Finset

theorem proof1 : A329073_b 3 = 430 := rfl

theorem proof2 : (430 : ℤ) % 2 = 0 := rfl

theorem disproof_it (h : (A329073_b 3 % 2 = 1 ↔ Nat.isPowerOfTwo 3)) : False := by
  have h1 : A329073_b 3 = 430 := rfl
  have h2 : (430 : ℤ) % 2 = 0 := rfl
  rw [h1, h2] at h
  have h3 : (0 : ℤ) ≠ 1 := by decide
  have h4 : ¬ Nat.isPowerOfTwo 3 := by
    rintro ⟨k, hk⟩
    rcases k with _ | _ | k'
    · revert hk; decide
    · revert hk; decide
    · have H : 2 ^ (k' + 2) ≥ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
      have H2 : 2 ^ (k' + 2) ≥ 4 := H
      omega
  -- h says 0 = 1 ↔ isPowerOfTwo 3
  -- so False ↔ False
  -- True... wait!
  -- Oh, `b(n) is odd if and only if n is a power of two.`
  -- 430 is EVEN. 3 is NOT a power of two.
  -- b(3) is odd <-> 3 is power of two
  -- False <-> False. THIS IS TRUE!
  -- The conjecture HOLDS for n=3!
  sorry
