import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    (Nat.digits 2 (n ^ 2)).count 0

#eval a 181
#eval a 182
#eval a 183
