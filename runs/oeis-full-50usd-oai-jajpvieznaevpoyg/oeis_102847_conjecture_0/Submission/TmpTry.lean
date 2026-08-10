import FormalConjectures.Util.ProblemImports

def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

example (n : ℕ) (hn : 4 < n) (hp : Nat.Prime (a n)) : False := by
  simp [a] at hp
  aesop
