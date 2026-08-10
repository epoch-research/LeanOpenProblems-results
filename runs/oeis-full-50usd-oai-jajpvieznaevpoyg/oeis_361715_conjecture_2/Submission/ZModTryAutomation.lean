import FormalConjectures.Util.ProblemImports
open Nat Finset
set_option maxHeartbeats 500000

def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ZMod (p ^ (3 * r + 3))) = (a (p ^ (r - 1)) : ZMod (p ^ (3 * r + 3))) := by
  try simp [a]
  try norm_num
  try ring_nf
  try omega
  try aesop
  try grind
  trace_state
  sorry
