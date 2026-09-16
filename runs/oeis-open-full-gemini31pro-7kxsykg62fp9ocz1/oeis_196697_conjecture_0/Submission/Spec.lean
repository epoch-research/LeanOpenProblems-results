import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let candidates_set : Finset ℕ :=
    (range n).biUnion fun k =>
      let p2n := 2^n
      let p2k := 2^k
      insert (p2n + p2k + 1) $ insert (p2n + p2k - 1) $
      insert (p2n - p2k + 1) $ {p2n - p2k - 1}
  (candidates_set.filter Nat.Prime).card

theorem oeis_196697_conjecture_0 : ∀ n : ℕ, 1 ≤ n → a n > 0 := sorry

theorem oeis_196697_conjecture_0.disproof : ¬ (∀ n : ℕ, 1 ≤ n → a n > 0) := sorry
