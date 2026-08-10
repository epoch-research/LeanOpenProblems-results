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

lemma B_gcd_div_fib_sub_1 (k : ℕ) (d : ℕ) (hd_Bkp1_sub_1 : (d : ℤ) ∣ (B (k+1) : ℤ) - 1) (hd_Bk_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1) (j : ℕ) (hj : j ≤ k) :
  (d : ℤ) ∣ (B (k - j) : ℤ) - (-1 : ℤ)^j * (Nat.fib (j - 1) : ℤ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | j
    · simp only [Nat.sub_zero, pow_zero, Int.ofNat_zero, mul_zero, sub_zero]
      exact hd_Bk_sub_1
    · rcases j with _ | j
      · have h_rec : B (k + 1) = B k + B (k - 1) := by
          have hk : k ≥ 1 := by omega
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          subst hm
          rfl
        have h_rec_z : (B (k + 1) : ℤ) = (B k : ℤ) + (B (k - 1) : ℤ) := by exact_mod_cast h_rec
        have h_sub_1 : (B (k - 1) : ℤ) = ((B (k + 1) : ℤ) - 1) - ((B k : ℤ) - 1) := by omega
        have hd_sub_1 : (d : ℤ) ∣ (B (k - 1) : ℤ) := by
          rw [h_sub_1]
          exact dvd_sub hd_Bkp1_sub_1 hd_Bk_sub_1
        have h_simp : (B (k - 1) : ℤ) - (-1 : ℤ)^1 * (Nat.fib 0 : ℤ) = (B (k - 1) : ℤ) := by simp
        rw [h_simp]
        exact hd_sub_1
      · have ih1 := ih j (by omega) (by omega)
        have ih2 := ih (j + 1) (by omega) (by omega)
        have h_idx2 : k - (j + 1) = k - 1 - j := by omega
        rw [h_idx2] at ih2
        have h_rec_B : B (k - j) = B (k - 1 - j) + B (k - 2 - j) := by
          have h1 : k - j = (k - 2 - j) + 2 := by omega
          have h2 : k - 1 - j = (k - 2 - j) + 1 := by omega
          rw [h1, h2]
          rfl
        have h_rec_B_z : (B (k - j) : ℤ) = (B (k - 1 - j) : ℤ) + (B (k - 2 - j) : ℤ) := by exact_mod_cast h_rec_B
        have h_fib : Nat.fib (j + 1) = Nat.fib (j - 1) + Nat.fib j := by
          have : j + 1 = (j - 1) + 2 := by omega
          rw [this, Nat.fib_add_two]
        have h_fib_z : (Nat.fib (j + 1) : ℤ) = (Nat.fib (j - 1) : ℤ) + (Nat.fib j : ℤ) := by exact_mod_cast h_fib
        have h_comb : (B (k - 2 - j) : ℤ) - (-1 : ℤ)^(j + 2) * (Nat.fib (j + 1) : ℤ) =
          ((B (k - j) : ℤ) - (-1 : ℤ)^j * (Nat.fib (j - 1) : ℤ)) -
          ((B (k - 1 - j) : ℤ) - (-1 : ℤ)^(j + 1) * (Nat.fib j : ℤ)) := by
          have h_pow1 : (-1 : ℤ)^(j + 2) = (-1 : ℤ)^j := by rw [pow_add, pow_two]; ring
          have h_pow2 : (-1 : ℤ)^(j + 1) = -(-1 : ℤ)^j := by rw [pow_add, pow_one]; ring
          rw [h_rec_B_z, h_fib_z, h_pow1, h_pow2]
          ring
        have h_index : k - (j + 2) = k - 2 - j := by omega
        rw [h_index]
        have h_goal_pow : (-1 : ℤ)^(j + 1 + 1) = (-1 : ℤ)^(j + 2) := rfl
        have h_goal_fib : (Nat.fib (j + 1 + 1 - 1) : ℤ) = (Nat.fib (j + 1) : ℤ) := by
          have : j + 1 + 1 - 1 = j + 1 := rfl
          rw [this]
        rw [h_goal_pow, h_goal_fib]
        rw [h_comb]
        exact dvd_sub ih1 ih2
