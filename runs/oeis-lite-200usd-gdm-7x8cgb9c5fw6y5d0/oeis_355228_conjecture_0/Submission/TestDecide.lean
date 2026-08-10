import FormalConjectures.Util.ProblemImports

open Finset Nat Set

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

def check_div_card_interval (k : ℕ) (start : ℕ) (len : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if len = 0 then
      decide ((divisors start).card < k)
    else
      let mid := len / 2
      check_div_card_interval k start mid fuel && check_div_card_interval k (start + mid + 1) (len - mid - 1) fuel

lemma check_div_card_interval_prop (k : ℕ) (start : ℕ) (len : ℕ) (fuel : ℕ) (h : check_div_card_interval k start len fuel = true) :
    ∀ x, start ≤ x ∧ x ≤ start + len → (divisors x).card < k := by
  induction fuel generalizing start len with
  | zero => simp [check_div_card_interval] at h
  | succ fuel ih =>
    rw [check_div_card_interval] at h
    by_cases h_zero : len = 0
    · simp [h_zero] at h
      intro x hx
      have : x = start := by omega
      subst this
      exact h
    · simp [h_zero] at h
      rcases h with ⟨h1, h2⟩
      intro x hx
      let mid := len / 2
      by_cases h_le : x ≤ start + mid
      · exact ih start mid h1 x ⟨hx.1, h_le⟩
      · have h_ge : start + mid + 1 ≤ x := by omega
        have h_le_right : x ≤ start + mid + 1 + (len - mid - 1) := by omega
        exact ih (start + mid + 1) (len - mid - 1) h2 x ⟨h_ge, h_le_right⟩

lemma check_div_card_interval_range (k : ℕ) (start : ℕ) (len : ℕ) (h : check_div_card_interval k start len 20 = true) :
    ∀ x, start ≤ x ∧ x ≤ start + len → (divisors x).card < k := by
  exact check_div_card_interval_prop k start len 20 h

-- Let's test checking the interval [138601, 277199] for < 181 divisors
lemma card_divisors_lt_181_of_le_277199 :
    ∀ x, 138601 ≤ x ∧ x ≤ 277199 → (divisors x).card < 181 := by
  apply check_div_card_interval_range 181 138601 138598
  decide
