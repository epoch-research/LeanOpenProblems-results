import FormalConjectures.Util.Answer
import Mathlib.Data.Nat.Basic

set_option google.answer "always_true"

opaque a (n : ℕ) : ℕ

theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  intro n hn
  exact answer(sorry)
