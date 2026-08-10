import FormalConjectures.Util.ProblemImports

#eval decide ((Int8.minValue : Int8) < Int8.minValue)
#eval decide ((Int16.minValue : Int16) < Int16.minValue)
#eval decide ((0 : Int32) < (0 : Int32))
#eval decide ((false : Bool) = !false)
#eval decide ((true : Bool) = !true)
#eval decide (Computability.Γ'.blank = Computability.Γ'.bra)
#eval decide ((0 : Nat) + 1 ≤ 0)
#eval decide ((0 : Nat) + 1 = 0)

example : False := by
  -- manually try if any eval true (none expected)
  have h := Bool.self_ne_not false
  exact h (by decide)
