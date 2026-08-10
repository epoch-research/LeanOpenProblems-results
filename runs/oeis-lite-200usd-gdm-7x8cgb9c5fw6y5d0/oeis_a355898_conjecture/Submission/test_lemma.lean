import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero => simp [B, B0]
  | succ m ih =>
    cases m with
    | zero => simp [B, B1]
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
      omega

theorem gcd_step (k : ℕ) :
  Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = Nat.gcd (B (k + 1) - 1) (B k) := by
  have h_rec : B (k + 2) = B (k + 1) + B k := rfl
  have h_sub : B (k + 2) - 1 = B (k + 1) - 1 + B k := by
    have h_ge1 : 1 ≤ B (k + 1) := B_pos (k + 1)
    omega
  rw [h_sub]
  rw [add_comm (B (k + 1) - 1) (B k)]
  rw [Nat.gcd_add_self_left]
  rw [Nat.gcd_comm]

theorem gcd_step2 (k : ℕ) (hk : 1 ≤ k) :
  Nat.gcd (B (k + 1) - 1) (B k) = Nat.gcd (B k) (B (k - 1) - 1) := by
  have h_sub : B (k + 1) - 1 = B k + (B (k - 1) - 1) := by
    have h_rec : B (k + 1) = B k + B (k - 1) := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      subst hm
      rfl
    have : 1 ≤ B (k - 1) := B_pos (k - 1)
    omega
  rw [h_sub]
  rw [Nat.gcd_comm (B k + (B (k - 1) - 1)) (B k)]
  rw [add_comm (B k) (B (k - 1) - 1)]
  rw [Nat.gcd_add_self_right]

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_2 : Nat.gcd (B 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

theorem B_gcd_mutual (k : ℕ) :
  Nat.gcd (B (k + 1) - 1) (B k - 1) = 1 ∧ Nat.gcd (B (k + 1)) (B k - 1) = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · constructor
      · exact base_gcd_0
      · exact base_gcd_2
    · rcases k with _ | k
      · constructor
        · have h_gcd := gcd_step 0
          rw [h_gcd]
          exact base_gcd_1
        · -- gcd (B 2) (B 1 - 1)
          have h_rec : B 2 = B 1 + B 0 := rfl
          rw [h_rec]
          rw [add_comm (B 1) (B 0)]
          rw [add_comm (B 0) (B 1)]
          rw [Nat.gcd_add_self_right]
          exact base_gcd_2
      · -- Case k >= 2 (so k + 2)
        constructor
        · -- part 1: gcd (B (k + 3) - 1) (B (k + 2) - 1) = 1
          rw [gcd_step (k + 1)]
          rw [gcd_step2 (k + 1) (by omega)]
          exact (ih k (by omega)).2
        · -- part 2: gcd (B (k + 3)) (B (k + 2) - 1) = 1
          have h_rec : B (k + 3) = B (k + 2) + B (k + 1) := rfl
          rw [h_rec]
          rw [Nat.gcd_comm (B (k + 2) + B (k + 1)) (B (k + 2) - 1)]
          have h_add : B (k + 2) + B (k + 1) = (B (k + 2) - 1) + (B (k + 1) + 1) := by
            have : 1 ≤ B (k + 2) := B_pos (k + 2)
            omega
          rw [h_add]
          rw [add_comm (B (k + 2) - 1) (B (k + 1) + 1)]
          rw [Nat.gcd_add_self_right]
          rw [Nat.gcd_comm]
          -- We want to show gcd (B (k + 1) + 1) (B (k + 2) - 1) = 1
          sorry
