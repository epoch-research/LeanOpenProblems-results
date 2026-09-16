import Mathlib

lemma no_div_between (n d x : ℕ) (hd : d > 0) (hx0 : x > 0) (hx : x ∣ n) (h1 : x < n / d) :
  x ≤ n / (d + 1) := by
  have h2 : x * d < n := lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h1 hd) (Nat.div_mul_le_self n d)
  have h3 : x * (d + 1) ≤ n := by
    rcases hx with ⟨k, hk⟩
    have : k = n / x := by
      rw [hk, Nat.mul_div_cancel_left _ hx0]
    subst this
    have : d < n / x := by
      rw [hk] at h2
      exact (Nat.mul_lt_mul_left hx0).mp h2
    rw [hk]
    have h4 : d + 1 ≤ n / x := this
    calc
      x * (d + 1) = (d + 1) * x := mul_comm _ _
      _ ≤ (n / x) * x := Nat.mul_le_mul_right x h4
      _ = x * (n / x) := mul_comm _ _
  exact (Nat.le_div_iff_mul_le (by omega)).mpr h3

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

def remaining_divs (n d : ℕ) : List ℕ :=
  (List.range (n / d - d + 1)).map (· + d) |>.filter (fun x => if x > 0 then n % x == 0 else false)

lemma list_divs_loop_inv (n d fuel : ℕ) (low high : List ℕ)
  (hd : d > 0) (h_fuel : fuel ≥ n - d + 1) :
  list_divs_loop n d fuel low high = low ++ remaining_divs n d ++ high := by
  sorry
