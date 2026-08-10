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

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1
def A3772 : ℕ := (A355898_loop 3771 1 1).1

attribute [irreducible] B0 B1 A3772

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem B_pos (m : ℕ) : 1 ≤ B m := by
  induction m with
  | zero =>
    unfold B B0
    decide
  | succ m ih =>
    cases m with
    | zero =>
      unfold B B1
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

theorem A355898_eq_B_loop (n : ℕ) (h : 3773 ≤ n) :
  (A355898 n, A355898 (n+1)) = A355898_loop (n - 3773) (B 0 - 1) (B 1 - 1) := by
  have h_loop_eq := A355898_eq_loop (n - 1)
  have h_n : n - 1 + 1 = n := by omega
  have h_n2 : n - 1 + 2 = n + 1 := by omega
  rw [h_n, h_n2] at h_loop_eq
  rw [h_loop_eq]
  have h_sub_n : n - 1 = (n - 3773) + 3772 := by omega
  rw [h_sub_n]
  rw [A355898_loop_split 3772 (n - 3773) 1 1]
  unfold B0 B1
  rfl

theorem B_gcd_and_loop (k : ℕ) :
  (∀ m ≤ k, Nat.gcd (B (m + 1) - 1) (B m - 1) = 1) ∧
  (∀ m ≤ k, A355898_loop m (B 0 - 1) (B 1 - 1) = (B m - 1, B (m + 1) - 1)) := by
  induction k with
  | zero =>
    constructor
    · intro m hm
      have : m = 0 := by omega
      subst this
      exact base_gcd_0
    · intro m hm
      have : m = 0 := by omega
      subst this
      rfl
  | succ k ih =>
    have ih_gcd := ih.1
    have ih_loop := ih.2
    have h_loop_next : A355898_loop (k + 1) (B 0 - 1) (B 1 - 1) = (B (k + 1) - 1, B (k + 2) - 1) := by
      cases k with
      | zero =>
        simp only [A355898_loop]
        rw [base_gcd_0]
        have h_div : 1 + (B 1 - 1 + (B 0 - 1)) / 1 = B 2 - 1 := by
          rw [Nat.div_one]
          have h_rec : B 2 = B 1 + B 0 := rfl
          have h0 : 1 ≤ B 0 := B_pos 0
          have h1 : 1 ≤ B 1 := B_pos 1
          omega
        rw [h_div]
      | succ k =>
        have h_split := A355898_loop_split 1 (k + 1) (B 0 - 1) (B 1 - 1)
        have h_add : k + 1 + 1 = 1 + (k + 1) := by omega
        rw [h_add, h_split]
        have h_loop_k := ih_loop (k + 1) (by omega)
        rw [h_loop_k]
        simp only [A355898_loop]
        have h_gcd_k := ih_gcd (k + 1) (by omega)
        rw [h_gcd_k]
        have h_div : 1 + (B (k + 2) - 1 + (B (k + 1) - 1)) / 1 = B (k + 3) - 1 := by
          rw [Nat.div_one]
          have h_rec : B (k + 3) = B (k + 2) + B (k + 1) := rfl
          have h0 : 1 ≤ B (k + 1) := B_pos (k + 1)
          have h1 : 1 ≤ B (k + 2) := B_pos (k + 2)
          omega
        rw [h_div]
theorem h_const (x : ℕ) : Nat.gcd (B (x + 1) - 1) (B x) = 1 := by
  induction x with
  | zero =>
    exact base_gcd_1
  | succ x ih =>
    -- we want to prove Nat.gcd (B (x + 2) - 1) (B (x + 1)) = 1
    -- wait, gcd_step2 (x + 1) gives Nat.gcd (B (x + 2) - 1) (B (x + 1)) = Nat.gcd (B (x + 1)) (B x - 1)
    rw [gcd_step2 (x + 1) (by omega)]
    rw [Nat.gcd_comm]
    -- now we have Nat.gcd (B x - 1) (B (x + 1)) = 1
    sorry

