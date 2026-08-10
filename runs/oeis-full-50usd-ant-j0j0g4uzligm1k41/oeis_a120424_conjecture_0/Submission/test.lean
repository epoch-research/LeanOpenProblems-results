import FormalConjectures.Util.ProblemImports

def A120424 : ℕ → ℕ
| 0     => 1
| 1     => 3
| n + 2 =>
  let f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x
  f (A120424 (n + 1)) + f (A120424 n)

#eval (List.range 16).map A120424
