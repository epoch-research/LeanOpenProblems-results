import FormalConjectures.Util.ProblemImports

open Nat Finset

def A352965 : ℕ → ℕ
| 0 => 0
| 1 => 0
| n + 1 =>
  let k := n
  let a_k := A352965 k
  let all_lt_k := Finset.range k
  let S := all_lt_k.filter (fun p =>
    Nat.Prime p ∧ A352965 (k - p) = a_k)
  if h : S.Nonempty then
    S.min' h
  else
    0

lemma A_four : A352965 4 = 2 := by
  unfold A352965
  rfl
