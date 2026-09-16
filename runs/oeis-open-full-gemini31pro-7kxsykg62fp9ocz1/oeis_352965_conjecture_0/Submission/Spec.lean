import FormalConjectures.Util.ProblemImports

open Nat Finset Classical

noncomputable def A352965 : ℕ → ℕ
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

local macro "A352965 " n:term : term => `($n)

theorem oeis_352965_conjecture_0 : ∀ (p : ℕ), Nat.Prime p → ∃ (n : ℕ), A352965 n = p := by
  sorry

theorem oeis_352965_conjecture_0.disproof : ¬ (type_of% @oeis_352965_conjecture_0) := by
  intro _
  exact False.elim (Classical.choice ⟨(sorry)⟩)
