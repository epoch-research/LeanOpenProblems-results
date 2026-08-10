import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ZMod (p ^ (3 * r + 3))) = (a (p ^ (r - 1)) : ZMod (p ^ (3 * r + 3))) := by
  change ((a (p^r) : ℕ) : ZMod (p ^ (3*r+3))) = ((a (p^(r-1)) : ℕ) : ZMod (p ^ (3*r+3)))
  sorry

example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r)
  (h : (a (p ^ r) : ZMod (p ^ (3 * r + 3))) = (a (p ^ (r - 1)) : ZMod (p ^ (3 * r + 3)))) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  exact_mod_cast h
