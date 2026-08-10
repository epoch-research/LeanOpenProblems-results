import FormalConjectures.Util.ProblemImports

open Nat

def check_single (bytes : ByteArray) (n : Nat) : Bool :=
  if n % 6 == 3 ∨ n % 10 == 0 ∨ n % 6 == 0 then true
  else false

def check_all_loop (bytes : ByteArray) : Nat → Nat → Nat → Bool
  | 0, L, R =>
    if L = R then check_single bytes L else true
  | fuel + 1, L, R =>
    if L > R then true
    else if L = R then check_single bytes L
    else
      let mid := (L + R) / 2
      check_all_loop bytes fuel L mid && check_all_loop bytes fuel (mid + 1) R

theorem check_all_sound (bytes : ByteArray) (fuel : Nat) : ∀ L R, L ≤ n → n ≤ R → R - L < 2 ^ fuel → check_all_loop bytes fuel L R = true → check_single bytes n = true := by
  induction fuel with
  | zero =>
    intro L R hL hnR h_lt h_all
    have h_eq : L = R := by omega
    have h_n : n = L := by omega
    dsimp [check_all_loop] at h_all
    rw [if_pos h_eq] at h_all
    rw [h_n]
    exact h_all
  | succ f ih =>
    intro L R hL hnR h_lt h_all
    dsimp [check_all_loop] at h_all
    split_ifs at h_all with h_gt h_eq
    · omega
    · have h_n : n = L := by omega
      rw [h_n]
      exact h_all
    · rw [Bool.and_eq_true] at h_all
      rcases h_all with ⟨h_left, h_right⟩
      let mid := (L + R) / 2
      have h_mid : mid = (L + R) / 2 := rfl
      have h_div : 2 * mid ≤ L + R ∧ L + R < 2 * mid + 2 := by
        rw [h_mid]
        omega
      by_cases hn : n ≤ mid
      · apply ih L mid hL hn ?_ h_left
        have : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
        omega
      · apply ih (mid + 1) R ?_ hnR ?_ h_right
        · omega
        · have : 2 ^ (f + 1) = 2 ^ f * 2 := by ring
          omega
