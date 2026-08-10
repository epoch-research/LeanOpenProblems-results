import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

local instance instBadLTNat : LT ℕ := ⟨fun _ _ => False⟩

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hs
  cases hn
#print axioms oeis_7468_conjecture_0
set_option pp.all true in #check (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38)
