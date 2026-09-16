import Mathlib

def div_loop (n d fuel : ℕ) (low high : List ℕ) : List ℕ × List ℕ :=
  match fuel with
  | 0 => (low, high)
  | f + 1 =>
    if d * d > n then (low, high)
    else if n % d == 0 then
      if d * d == n then (low ++ [d], high)
      else div_loop n (d + 1) f (low ++ [d]) ((n / d) :: high)
    else div_loop n (d + 1) f low high

lemma div_loop_subset (n d fuel : ℕ) (low high : List ℕ) :
  ∀ x, x ∈ (div_loop n d fuel low high).1 ∨ x ∈ (div_loop n d fuel low high).2 →
  x ∈ low ∨ x ∈ high ∨ (x ≥ d ∧ x ∣ n ∧ x * x ≤ n) ∨ (n / x ≥ d ∧ x ∣ n ∧ (n / x) * (n / x) < n) := by
  sorry
