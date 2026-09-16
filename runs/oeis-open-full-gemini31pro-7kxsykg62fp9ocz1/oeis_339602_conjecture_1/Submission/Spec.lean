import FormalConjectures.Util.ProblemImports

open Nat Finset

def A030101 (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (Nat.digits 2 n))

def a : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => (a n).xor (A030101 (a (n + 1))) + 1
termination_by n => n

theorem oeis_339602_conjecture_1 (p : ℕ) (hp_odd : p % 2 = 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (filter (fun n : ℕ => a n = p) (range N)).card > (filter (fun n : ℕ => a n = p + 1) (range N)).card := by
  sorry

theorem oeis_339602_conjecture_1.disproof : ¬ (type_of% @oeis_339602_conjecture_1) := by
  sorry
