import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxHeartbeats 0
set_option maxRecDepth 200000

def check_lookup_prop (k : ℕ) : Bool :=
  k > 20

theorem test_theorem (n : ℕ) : check_lookup_prop 30 = true := by
  let rec check_range_tail (count : ℕ) (i : ℕ) : Bool :=
    match count with
    | 0 => true
    | count + 1 =>
      if check_lookup_prop i then
        check_range_tail count (i + 1)
      else
        false
  have check_range_tail_sound (count : ℕ) (i : ℕ) (h : check_range_tail count i = true) :
      ∀ k, i ≤ k → k < i + count → check_lookup_prop k = true := by
    induction count generalizing i with
    | zero =>
      intro k hk1 hk2
      omega
    | succ count ih =>
      intro k hk1 hk2
      -- Since check_range_tail is defined locally, we need to unfold it or use its definition
      sorry
  sorry
