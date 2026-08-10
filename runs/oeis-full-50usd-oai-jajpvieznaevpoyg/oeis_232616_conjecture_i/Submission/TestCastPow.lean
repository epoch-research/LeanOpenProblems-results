import FormalConjectures.Util.ProblemImports
example (e : Nat) : (2 : ZMod 5)^e = (Nat.cast (2^e) : ZMod 5) := by
  norm_num [Nat.cast_pow]
