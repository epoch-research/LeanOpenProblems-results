import FormalConjectures.Util.ProblemImports

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

def main : IO Unit := do
  for n in [1:150] do
    if x_seq n % 11 == 0 then
      IO.println s!"11 divides x_seq({n})"

#eval main
