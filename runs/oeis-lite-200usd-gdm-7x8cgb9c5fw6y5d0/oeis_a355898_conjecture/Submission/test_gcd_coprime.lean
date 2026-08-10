import FormalConjectures.Util.ProblemImports

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

theorem P_coprime (k : ℕ) (hk : 1 ≤ k) :
  Nat.gcd (Nat.gcd (B (k + 1) - 1) (B k - 1)) (Nat.gcd (B k - 1) (B (k - 1) - 1)) = 1 := by
  set g := Nat.gcd (Nat.gcd (B (k + 1) - 1) (B k - 1)) (Nat.gcd (B k - 1) (B (k - 1) - 1))
  have hg1 : g ∣ Nat.gcd (B (k + 1) - 1) (B k - 1) := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ Nat.gcd (B k - 1) (B (k - 1) - 1) := Nat.gcd_dvd_right _ _
  have h_gcd : Nat.gcd (B (k + 1) - 1) (B k - 1) = Nat.gcd (B k - 1) (B (k - 1)) := by
    have h_step := gcd_step (k - 1)
    have h_sub : k - 1 + 2 = k + 1 := by omega
    have h_sub2 : k - 1 + 1 = k := by omega
    rw [h_sub, h_sub2] at h_step
    exact h_step
  rw [h_gcd] at hg1
  have hg1' : g ∣ B (k - 1) := by
    have : Nat.gcd (B k - 1) (B (k - 1)) ∣ B (k - 1) := Nat.gcd_dvd_right _ _
    exact Nat.dvd_trans hg1 this
  have hg2' : g ∣ B (k - 1) - 1 := by
    have : Nat.gcd (B k - 1) (B (k - 1) - 1) ∣ B (k - 1) - 1 := Nat.gcd_dvd_right _ _
    exact Nat.dvd_trans hg2 this
  have h_coprime : Nat.gcd (B (k - 1)) (B (k - 1) - 1) = 1 := by
    have h_rec : B (k - 1) = (B (k - 1) - 1) + 1 := by
      have : 1 ≤ B (k - 1) := B_pos (k - 1)
      omega
    rw [h_rec]
    rw [add_comm]
    have h_cancel : 1 + (B (k - 1) - 1) - 1 = B (k - 1) - 1 := by omega
    rw [h_cancel]
    rw [Nat.gcd_add_self_left]
    exact Nat.gcd_one_left _
  have h_g_dvd : g ∣ Nat.gcd (B (k - 1)) (B (k - 1) - 1) := Nat.dvd_gcd hg1' hg2'
  rw [h_coprime] at h_g_dvd
  exact Nat.eq_one_of_dvd_one h_g_dvd
