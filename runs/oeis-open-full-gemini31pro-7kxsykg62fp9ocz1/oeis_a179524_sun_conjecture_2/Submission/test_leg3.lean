import Mathlib

#eval show ℤ from
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  legendreSym 3 (-1)

#eval show ℤ from
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  legendreSym 5 (-1)
