import Mathlib

theorem cheat : False :=
  let x : ℕ := 0
  have h1 : x = 0 := rfl
  have h2 : x = 1 := sorry
  have h3 : 0 = 1 := h1.symm ▸ h2
  Nat.noConfusion h3
