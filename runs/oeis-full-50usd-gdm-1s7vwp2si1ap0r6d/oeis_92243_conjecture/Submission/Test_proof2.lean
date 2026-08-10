import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

lemma Int_sign_of_pos (x : ℤ) (hx : x > 0) : x.sign = 1 := by
  rcases x with (n | a)
  · rcases n with (_ | n)
    · contradiction
    · rfl
  · contradiction

lemma Int_sign_of_neg (x : ℤ) (hx : x < 0) : x.sign = -1 := by
  rcases x with (n | a)
  · rcases n with (_ | n)
    · contradiction
    · contradiction
  · rfl

theorem sign_le_self (d : ℤ) (hd_even : ∃ m : ℤ, d = 2 * m) : 2 * d.sign ≤ d := by
  rcases hd_even with ⟨m, rfl⟩
  rcases lt_trichotomy m 0 with h | rfl | h
  · have h_neg : 2 * m < 0 := by linarith
    rw [Int_sign_of_neg (2 * m) h_neg]
    omega
  · simp
  · have h_pos : 2 * m > 0 := by linarith
    rw [Int_sign_of_pos (2 * m) h_pos]
    omega

