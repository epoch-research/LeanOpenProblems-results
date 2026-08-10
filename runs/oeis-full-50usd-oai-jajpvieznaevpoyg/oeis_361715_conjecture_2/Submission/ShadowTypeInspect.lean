import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ := ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k
local instance instTriv : Pow Nat Nat := ⟨fun _ _ => 1⟩
theorem t (p r : ℕ) : (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by rfl
set_option pp.all true in
#print t
#check instTriv
