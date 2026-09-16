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

lemma mem_list_divs_loop (n d fuel : ℕ) (low high : List ℕ) (x : ℕ)
  (h_fuel : fuel ≥ n - d + 1) (hd : d > 0) :
  x ∈ list_divs_loop n d fuel low high ↔
  x ∈ low ∨ x ∈ high ∨ (x ≥ d ∧ x ≤ n / d ∧ n % x = 0) := by
  induction fuel generalizing d low high with
  | zero =>
    have : d > n := by omega
    have : d * d > n := by
      nlinarith
    -- Wait, if fuel = 0, the loop returns low ++ high.
    sorry
  | succ f ih =>
    sorry
