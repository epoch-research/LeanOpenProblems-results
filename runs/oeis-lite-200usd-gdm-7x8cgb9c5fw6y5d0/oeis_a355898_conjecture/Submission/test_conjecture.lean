import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

def A355898_loop : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, a, b => (a, b)
| n + 1, a, b =>
  let g := Nat.gcd b a
  A355898_loop n b (g + (b + a) / g)

theorem A355898_loop_eq (n : ℕ) : ∀ k, 1 ≤ k →
  A355898_loop n (A355898 k) (A355898 (k + 1)) = (A355898 (n + k), A355898 (n + k + 1)) := by
  induction n with
  | zero =>
    intro k _
    simp only [A355898_loop, zero_add]
  | succ n ih =>
    intro k hk
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    subst hm
    have h_rec : Nat.gcd (A355898 (m + 2)) (A355898 (m + 1)) + (A355898 (m + 2) + A355898 (m + 1)) / Nat.gcd (A355898 (m + 2)) (A355898 (m + 1)) = A355898 (m + 3) := rfl
    simp only [A355898_loop]
    rw [h_rec]
    have ih_val := ih (m + 2) (by omega)
    rw [ih_val]
    congr 2 <;> omega

theorem A355898_eq_loop (n : ℕ) : (A355898 (n + 1), A355898 (n + 2)) = A355898_loop n 1 1 := by
  exact (A355898_loop_eq n 1 (by omega)).symm

theorem A355898_loop_split (n : ℕ) (m : ℕ) (a b : ℕ) :
  A355898_loop (m + n) a b = A355898_loop m (A355898_loop n a b).1 (A355898_loop n a b).2 := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [A355898_loop]
    exact ih b (Nat.gcd b a + (b + a) / Nat.gcd b a)

theorem base_gcd_3772 : Nat.gcd (A355898_loop 3772 1 1).2 (A355898_loop 3772 1 1).1 = 1 := by
  decide

def B : ℕ → ℕ
| 0 => (A355898_loop 3772 1 1).1 + 1
| 1 => (A355898_loop 3772 1 1).2 + 1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero => simp [B]
  | succ m ih =>
    cases m with
    | zero => simp [B]
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
      omega

-- Assume B_gcd for now to see if the main theorem compiles
theorem B_gcd (k : ℕ) : Nat.gcd (B (k + 1) - 1) (B k - 1) = 1 := by
  sorry

theorem loop_eq_B_gen (k : ℕ) :
  ∀ m, A355898_loop k (B m - 1) (B (m+1) - 1) = (B (k+m) - 1, B (k+m+1) - 1) := by
  induction k with
  | zero =>
    intro m
    simp [A355898_loop]
  | succ k ih =>
    intro m
    have h_gcd : Nat.gcd (B (m + 1) - 1) (B m - 1) = 1 := B_gcd m
    have h_rec : B (m + 2) = B (m + 1) + B m := rfl
    have h_pos : 1 ≤ B (m + 1) := B_pos (m + 1)
    have h_pos2 : 1 ≤ B m := B_pos m
    simp only [A355898_loop]
    rw [h_gcd]
    have h_arith : 1 + (B (m + 1) - 1 + (B m - 1)) / 1 = B (m + 2) - 1 := by
      rw [Nat.div_one]
      omega
    rw [h_arith]
    have ih_val := ih (m + 1)
    rw [ih_val]
    have h_add1 : k + (m + 1) = k + 1 + m := by omega
    rw [h_add1]

theorem B_loop_eq (k : ℕ) :
  A355898_loop k (B 0 - 1) (B 1 - 1) = (B k - 1, B (k + 1) - 1) := by
  have h := loop_eq_B_gen k 0
  simp only [add_zero] at h
  exact h

theorem A355898_eq_B (n : ℕ) (h : 3773 ≤ n) :
  A355898 n = B (n - 3773) - 1 := by
  have h_eq : (A355898 n, A355898 (n + 1)) = (B (n - 3773) - 1, B (n - 3772) - 1) := by
    have h_eq_loop : (A355898 n, A355898 (n + 1)) = A355898_loop (n - 3773) (B 0 - 1) (B 1 - 1) := by
      sorry
    rw [h_eq_loop, B_loop_eq (n - 3773)]
    congr 2 <;> omega
  exact (Prod.ext_iff.mp h_eq).1
