import Submission.test_sort50
open List Finset

def list_divs_loop (n d fuel : ℕ) (low high : List ℕ) : List ℕ :=
  match fuel with
  | 0 => low ++ high
  | f + 1 =>
    if d * d > n then low ++ high
    else if n % d == 0 then
      if d * d == n then low ++ [d] ++ high
      else list_divs_loop n (d + 1) f (low ++ [d]) ((n / d) :: high)
    else list_divs_loop n (d + 1) f low high

def fast_divs (n : ℕ) : List ℕ := list_divs_loop n 1 (n + 1) [] []

-- The remaining divisors are those in range [d, n/d]
def remaining_divs (n d : ℕ) : List ℕ :=
  (List.range (n / d - d + 1)).map (· + d) |>.filter (fun x => if x > 0 then n % x == 0 else false)

lemma list_divs_loop_inv (n d fuel : ℕ) (low high : List ℕ)
  (h_fuel : fuel ≥ n - d + 1) :
  list_divs_loop n d fuel low high = low ++ remaining_divs n d ++ high := by
  sorry
