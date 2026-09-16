import Mathlib

haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
#eval (legendreSym 3 (-1) : ℤ)

haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
#eval (legendreSym 5 (-1) : ℤ)

haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
#eval (legendreSym 7 (-1) : ℤ)
