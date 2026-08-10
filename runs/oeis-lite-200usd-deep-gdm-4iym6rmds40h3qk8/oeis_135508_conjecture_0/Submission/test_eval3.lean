import FormalConjectures.Util.ProblemImports

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

def main : IO Unit := do
  for q in [2, 3, 5, 7, 11, 13, 17] do
    for n in [1:300] do
      if x_seq n % q == 0 then
        IO.println s!"{q} divides x_seq({n})"
        break

#eval main