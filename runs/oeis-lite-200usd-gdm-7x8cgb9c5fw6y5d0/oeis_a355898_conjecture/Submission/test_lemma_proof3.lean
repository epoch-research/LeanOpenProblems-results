import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def B0 : ℕ := 2
def B1 : ℕ := 3

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero =>
    unfold B B0
    omega
  | succ m ih =>
    cases m with
    | zero =>
      unfold B B1
      omega
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
      omega

lemma B_gcd_div_fib (k : ℕ) (d : ℕ) (hd_Bkp1 : d ∣ B (k+1)) (hd_B_sub_1 : (d : ℤ) ∣ (B k : ℤ) - 1) (j : ℕ) (hj : j ≤ k + 1) :
  (d : ℤ) ∣ (B (k + 1 - j) : ℤ) + (-1 : ℤ)^j * (Nat.fib j : ℤ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rcases j with _ | j
    · simp only [Nat.sub_zero, pow_zero, Int.ofNat_zero, mul_zero, add_zero]
      exact_mod_cast hd_Bkp1
    · rcases j with _ | j
      · have : k + 1 - 1 = k := by omega
        rw [this]
        have h_pow1 : (-1 : ℤ)^1 = -1 := by ring
        have h_fib1 : Nat.fib 1 = 1 := rfl
        rw [h_pow1, h_fib1]
        have h_ring : (B k : ℤ) + -1 * 1 = (B k : ℤ) - 1 := by ring
        rw [h_ring]
        exact hd_B_sub_1
      · have ih1 := ih j (by omega) (by omega)
        have ih2 := ih (j + 1) (by omega) (by omega)
        have h_idx2 : k + 1 - (j + 1) = k - j := by omega
        rw [h_idx2] at ih2
        have h_rec_B : B (k + 1 - j) = B (k - j) + B (k - 1 - j) := by
          have h1 : k + 1 - j = (k - 1 - j) + 2 := by omega
          have h2 : k - j = (k - 1 - j) + 1 := by omega
          rw [h1, h2]
          rfl
        have h_rec_B_z : (B (k + 1 - j) : ℤ) = (B (k - j) : ℤ) + (B (k - 1 - j) : ℤ) := by exact_mod_cast h_rec_B
        have h_fib : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
        have h_fib_z : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by exact_mod_cast h_fib
        have h_comb : (B (k - 1 - j) : ℤ) + (-1 : ℤ)^(j + 2) * (Nat.fib (j + 2) : ℤ) =
          ((B (k + 1 - j) : ℤ) + (-1 : ℤ)^j * (Nat.fib j : ℤ)) -
          ((B (k - j) : ℤ) + (-1 : ℤ)^(j + 1) * (Nat.fib (j + 1) : ℤ)) := by
          have h_pow1 : (-1 : ℤ)^(j + 2) = (-1 : ℤ)^j := by rw [pow_add, pow_two]; ring
          have h_pow2 : (-1 : ℤ)^(j + 1) = -(-1 : ℤ)^j := by rw [pow_add, pow_one]; ring
          rw [h_rec_B_z, h_fib_z, h_pow1, h_pow2]
          ring
        have h_index : k + 1 - (j + 2) = k - 1 - j := by omega
        rw [h_index]
        have h_goal_pow : (-1 : ℤ)^(j + 1 + 1) = (-1 : ℤ)^(j + 2) := rfl
        have h_goal_fib : (Nat.fib (j + 1 + 1) : ℤ) = (Nat.fib (j + 2) : ℤ) := rfl
        rw [h_goal_pow, h_goal_fib]
        rw [h_comb]
        exact dvd_sub ih1 ih2
