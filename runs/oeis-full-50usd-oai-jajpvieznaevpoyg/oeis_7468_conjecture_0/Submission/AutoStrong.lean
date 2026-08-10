import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

set_option maxHeartbeats 2000000
example : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hs
  simp [a, IsSquare] at hs ⊢
  aesop (add safe [Nat.prime_nth_prime, Nat.add_two_le_nth_prime])
