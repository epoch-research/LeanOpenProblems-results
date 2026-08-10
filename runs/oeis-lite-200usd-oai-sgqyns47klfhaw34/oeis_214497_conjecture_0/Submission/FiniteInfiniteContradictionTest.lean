import FormalConjectures.Util.ProblemImports

-- Diagnostics for accidental contradictory typeclass instances.
#synth Infinite Nat
#synth Finite Nat
#synth Infinite Int
#synth Finite Int
#synth Infinite Unit
#synth Finite Unit
#synth Infinite Empty
#synth Finite Empty
#synth Infinite Bool
#synth Finite Bool

example : False := by
  -- If both existed for Nat, this would close.
  exact Infinite.false (α := Nat) inferInstance
