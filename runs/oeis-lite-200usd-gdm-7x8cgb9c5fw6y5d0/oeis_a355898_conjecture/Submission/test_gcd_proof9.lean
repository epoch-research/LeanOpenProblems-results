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

theorem G_relation (k : ℕ) (hk : 1 ≤ k) :
  Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = Nat.gcd (B k) (B (k - 1) - 1) := by
  rw [gcd_step, gcd_step2 k hk]

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by decide
theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by decide

theorem P_coprime2 (k : ℕ) :
  Nat.gcd (Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1)) (Nat.gcd (B (k + 1) - 1) (B k - 1)) = 1 := by
  set g := Nat.gcd (Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1)) (Nat.gcd (B (k + 1) - 1) (B k - 1))
  have hg1 : g ∣ Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ Nat.gcd (B (k + 1) - 1) (B k - 1) := Nat.gcd_dvd_right _ _
  have h_gcd : Nat.gcd (B (k + 2) - 1) (B (k + 1) - 1) = Nat.gcd (B (k + 1) - 1) (B k) := gcd_step k
  rw [h_gcd] at hg1
  have hg1' : g ∣ B k := by
    have : Nat.gcd (B (k + 1) - 1) (B k) ∣ B k := Nat.gcd_dvd_right _ _
    exact Nat.dvd_trans hg1 this
  have hg2' : g ∣ B k - 1 := by
    have : Nat.gcd (B (k + 1) - 1) (B k - 1) ∣ B k - 1 := Nat.gcd_dvd_right _ _
    exact Nat.dvd_trans hg2 this
  have h_coprime : Nat.gcd (B k) (B k - 1) = 1 := by
    have h_rec : B k = (B k - 1) + 1 := by
      have : 1 ≤ B k := B_pos k
      omega
    rw [h_rec]
    rw [add_comm]
    have h_cancel : 1 + (B k - 1) - 1 = B k - 1 := by omega
    rw [h_cancel]
    rw [Nat.gcd_add_self_left]
    exact Nat.gcd_one_left _
  have h_g_dvd : g ∣ Nat.gcd (B k) (B k - 1) := Nat.dvd_gcd hg1' hg2'
  rw [h_coprime] at h_g_dvd
  exact Nat.eq_one_of_dvd_one h_g_dvd

theorem B_gcd (k : ℕ) : Nat.gcd (B (k + 1) - 1) (B k - 1) = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · exact base_gcd_0
    · rcases k with _ | k
      · have h_gcd := gcd_step 0
        rw [h_gcd]
        exact base_gcd_1
      · -- Goal: Nat.gcd (B (k + 3) - 1) (B (k + 2) - 1) = 1
        -- By P_coprime2 (k + 1):
        have h_cop := P_coprime2 (k + 1)
        -- We have ih at k + 1:
        have ih_val := ih (k + 1) (by omega)
        sorry
