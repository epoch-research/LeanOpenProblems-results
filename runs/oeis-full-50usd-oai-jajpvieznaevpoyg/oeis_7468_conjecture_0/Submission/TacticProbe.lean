import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

example : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hs
  rcases hs with ⟨r, hr⟩
  -- Try common arithmetic tactics; keep output concise.
  fail_if_success omega
  fail_if_success nlinarith
  fail_if_success aesop
  fail_if_success simp_all [a]
  guard_target = n = 38
  sorry
