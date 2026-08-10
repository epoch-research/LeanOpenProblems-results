import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

theorem test (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp1 : p ≠ 1 := hp.ne_one
  try omega
  try positivity
  try nlinarith
  try simp_all [a, Nat.Prime, Irreducible, Int.ModEq]
  try omega
  try aesop
  all_goals sorry
