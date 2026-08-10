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

-- Opaque constants to prevent stack overflow
def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1

attribute [irreducible] B0 B1

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero =>
    unfold B
    unfold B0
    decide
  | succ m ih =>
    cases m with
    | zero =>
      unfold B
      unfold B1
      decide
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
      omega

theorem base_gcd_0 : Nat.gcd (B 1 - 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by
  unfold B B0 B1
  decide

theorem base_gcd_2 : Nat.gcd (B 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  decide

-- Assume B_gcd for now
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

theorem B0_sub_1_eq : B 0 - 1 = (A355898_loop 3772 1 1).1 := by
  unfold B B0
  decide

theorem B1_sub_1_eq : B 1 - 1 = (A355898_loop 3772 1 1).2 := by
  unfold B B1
  decide

theorem oeis_a355898_conjecture (n : ℕ) (h : 3775 ≤ n) :
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) := by
  have h_eq : A355898 n = B (n - 3773) - 1 := A355898_eq_B n (by omega)
  have h_eq_minus1 : A355898 (n - 1) = B (n - 3774) - 1 := A355898_eq_B (n - 1) (by omega)
  have h_eq_minus2 : A355898 (n - 2) = B (n - 3775) - 1 := A355898_eq_B (n - 2) (by omega)
  have h_eq_minus3 : A355898 (n - 3) = B (n - 3776) - 1 := A355898_eq_B (n - 3) (by omega)
  have h_rec : B (n - 3773) = B (n - 3774) + B (n - 3775) := by
    have h_rec_gen : B (n - 3775 + 2) = B (n - 3775 + 1) + B (n - 3775) := rfl
    have h_sub1 : n - 3775 + 2 = n - 3773 := by omega
    have h_sub2 : n - 3775 + 1 = n - 3774 := by omega
    rw [h_sub1, h_sub2] at h_rec_gen
    exact h_rec_gen
  have h_pos_1 : 1 ≤ B (n - 3774) := B_pos (n - 3774)
  have h_pos_2 : 1 ≤ B (n - 3775) := B_pos (n - 3775)
  constructor
  · rw [h_eq, h_eq_minus1, h_eq_minus2, h_rec]
    omega
  · constructor
    · rw [h_eq, h_eq_minus1, h_eq_minus3, h_rec]
      have h_rec2 : B (n - 3774) = B (n - 3775) + B (n - 3776) := by
        have h_rec_gen : B (n - 3776 + 2) = B (n - 3776 + 1) + B (n - 3776) := rfl
        have h_sub1 : n - 3776 + 2 = n - 3774 := by omega
        have h_sub2 : n - 3776 + 1 = n - 3775 := by omega
        rw [h_sub1, h_sub2] at h_rec_gen
        exact h_rec_gen
      have h_pos_3 : 1 ≤ B (n - 3776) := B_pos (n - 3776)
      rw [h_rec2]
      omega
    · have h_fib : B (n - 3773) = B 1 * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) := by
        sorry
      sorry
