import FormalConjectures.Util.ProblemImports
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

local instance instBadLTNat : LT ℕ := ⟨fun _ _ => False⟩

theorem t : ∀ n : ℕ, @LT.lt ℕ instLTNat 0 n → IsSquare (a n) → n = 38 := by
  intro n hn hs
  -- hn is canonical, cannot case it
  fail_if_success cases hn
  sorry
set_option pp.all true in #check t
