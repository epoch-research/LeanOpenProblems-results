import FormalConjectures.Util.ProblemImports

open Nat

def check_single (n : ℕ) : Bool :=
  if n % 6 = 3 ∨ n % 10 = 0 ∨ n % 6 = 0 then true
  else false

def check_all_loop : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, L, R =>
    if L > R then true
    else
      check_single L && check_all_loop fuel (L + 1) R

theorem check_all_sound (fuel : Nat) : ∀ L R, L ≤ n → n ≤ R → n - L < fuel → check_all_loop fuel L R = true → check_single n = true := by
  induction fuel with
  | zero =>
    intro L R hL hnR h_lt h_all
    omega
  | succ f ih =>
    intro L R hL hnR h_lt h_all
    dsimp [check_all_loop] at h_all
    split_ifs at h_all with h_gt
    · omega
    · rw [Bool.and_eq_true] at h_all
      rcases h_all with ⟨h_single, h_loop⟩
      by_cases hn : L = n
      · rw [← hn]
        exact h_single
      · have h_lt' : L < n := by omega
        have h_sub : n - (L + 1) < f := by omega
        apply ih (L + 1) R
        · omega
        · exact hnR
        · exact h_sub
        · exact h_loop
