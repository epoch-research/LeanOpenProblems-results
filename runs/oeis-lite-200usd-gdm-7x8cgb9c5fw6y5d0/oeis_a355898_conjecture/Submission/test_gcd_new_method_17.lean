import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith

set_option maxRecDepth 200000

open Nat

-- Dummy values for testing so we don't need Spec.lean's B0, B1
def B0 : ℕ := 2
def B1 : ℕ := 3

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

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by decide
theorem base_gcd_1 : Nat.gcd (B 2 - 1) (B 1 - 1) = 1 := by decide

theorem B_gcd (k : ℕ) : Nat.gcd (B (k + 1) - 1) (B k - 1) = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · exact base_gcd_0
    · rcases k with _ | k
      · exact base_gcd_1
      · -- Case k_orig = k + 2 (since rcases peeled off 0 and 1)
        -- We want to prove Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1) = 1
        set d := Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1)
        have hd1 : d ∣ B (k + 3) - 1 := Nat.gcd_dvd_left _ _
        have hd2 : d ∣ B (k + 2) - 1 := Nat.gcd_dvd_right _ _
        have hd_Bkp1 : d ∣ B (k + 1) := by
          have hd_eq : d = Nat.gcd (B (k + 2) - 1) (B (k + 1)) := gcd_step (k + 1)
          rw [hd_eq]
          exact Nat.gcd_dvd_right _ _
        have hd_Bkm1 : d ∣ B k - 1 := by
          have h_rec_actual : B (k + 2) = B (k + 1) + B k := rfl
          have h_sub : B (k + 2) - 1 = B (k + 1) + (B k - 1) := by
            have : 1 ≤ B k := B_pos k
            omega
          rw [h_sub] at hd2
          exact (Nat.dvd_add_right hd_Bkp1).mp hd2
        have hd_gcd : d ∣ Nat.gcd (B (k + 1)) (B k - 1) := Nat.dvd_gcd hd_Bkp1 hd_Bkm1
        have h_step2 : Nat.gcd (B (k + 1)) (B k - 1) = Nat.gcd (B (k + 1) - 1) (B k) := by
          rw [Nat.gcd_comm]
          exact (gcd_step2 (k + 1) (by omega)).symm
        have h_step1 : Nat.gcd (B (k + 1) - 1) (B k) = Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) := (gcd_step k).symm
        have h_gcd_val : Nat.gcd (B (k + 1)) (B k - 1) = 1 := by
          rw [h_step2, h_step1]
          exact ih (k + 1) (by omega)
        rw [h_gcd_val] at hd_gcd
        exact Nat.eq_one_of_dvd_one hd_gcd
