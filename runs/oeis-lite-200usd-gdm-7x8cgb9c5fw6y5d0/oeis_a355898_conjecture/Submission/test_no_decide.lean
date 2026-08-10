import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 5000


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
    sorry
  | succ m ih =>
    cases m with
    | zero =>
      unfold B B1
      sorry
    | succ m =>
      have h_rec : B (m + 2) = B (m + 1) + B m := rfl
      rw [h_rec]
      omega

theorem B0_sub_1_eq : B 0 - 1 = (A355898_loop 3772 1 1).1 := by
  unfold B B0
  sorry

theorem B1_sub_1_eq : B 1 - 1 = (A355898_loop 3772 1 1).2 := by
  unfold B B1
  sorry

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
  sorry

theorem base_gcd_1 : Nat.gcd (B 1 - 1) (B 0) = 1 := by
  unfold B B0 B1
  sorry

theorem base_gcd_2 : Nat.gcd (B 1) (B 0 - 1) = 1 := by
  unfold B B0 B1
  sorry

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
      have h_loop_eq := A355898_eq_loop (n - 1)
      have h_n : n - 1 + 1 = n := by omega
      have h_n2 : n - 1 + 2 = n + 1 := by omega
      rw [h_n, h_n2] at h_loop_eq
      rw [h_loop_eq]
      have h_sub_n : n - 1 = (n - 3773) + 3772 := by omega
      rw [h_sub_n]
      rw [A355898_loop_split 3772 (n - 3773) 1 1]
      unfold B B0 B1
      rfl
    have h_final := B_loop_eq (n - 3773)
    have h_trans := h_eq_loop.trans h_final
    have h_sub_1 : n - 3773 + 1 = n - 3772 := by omega
    rw [h_sub_1] at h_trans
    exact h_trans
  exact (Prod.ext_iff.mp h_eq).1

theorem A355898_3772_eq : A355898 3772 = A3772 := by
  have h := A355898_eq_loop 3771
  have h1 := congrArg Prod.fst h
  unfold A3772
  exact h1

theorem A3772_identity : A3772 + 1 = B 1 - B 0 := by
  unfold A3772 B B1 B0
  sorry

theorem B_fib_rep (k : ℕ) (hk : 1 ≤ k) : B k = B 1 * Nat.fib k + B 0 * Nat.fib (k - 1) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | k
    · omega
    · rcases k with _ | k
      · simp [B]
      · rcases k with _ | k
        · simp [B]
        · have h_rec : B (k + 3) = B (k + 2) + B (k + 1) := rfl
          have ih1 := ih (k + 2) (by omega) (by omega)
          have ih2 := ih (k + 1) (by omega) (by omega)
          rw [h_rec, ih1, ih2]
          have h_fib1 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
          have h_fib2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
          have h_sub1 : k + 2 - 1 = k + 1 := by omega
          have h_sub2 : k + 1 - 1 = k := by omega
          have h_sub3 : k + 3 - 1 = k + 2 := by omega
          rw [h_sub1, h_sub2, h_sub3]
          rw [h_fib1, h_fib2]
          ring

/--
Conjecture: For n >= 3775 a(n) can also be expressed in the following three ways:
1) a(n) = 1 + a(n-1) + a(n-2).
2) a(n) = 2*a(n-1) - a(n-3).
3) If A = a(3774), B = a(3772) and F = Fibonacci A000045(n),
   a(n) = (A+1)*F(n-3772) - (B+1)*F(n-3774) - 1.
These three formulas only work for n >= 3775.
-/
theorem oeis_a355898_conjecture (n : ℕ) (h : 3775 ≤ n) :
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) := by
  rcases eq_or_lt_of_le h with rfl | hn
  · have h3775 : A355898 3775 = B 2 - 1 := A355898_eq_B 3775 (by omega)
    have h3774 : A355898 3774 = B 1 - 1 := A355898_eq_B 3774 (by omega)
    have h3773 : A355898 3773 = B 0 - 1 := A355898_eq_B 3773 (by omega)
    have h3772 : A355898 3772 = A3772 := A355898_3772_eq
    have h_rec_b : B 2 = B 1 + B 0 := rfl
    have h_pos_b0 : 1 ≤ B 0 := B_pos 0
    have h_pos_b1 : 1 ≤ B 1 := B_pos 1
    rw [h3775, h3774, h3773, h3772, h_rec_b]
    rw [A3772_identity]
    constructor
    · omega
    · constructor
      · omega
      · simp [Nat.fib]
        omega
  · -- Case 3776 ≤ n
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
      · -- Part 3
        rw [h_eq]
        have h_fib : B (n - 3773) = B 1 * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) := by
          have h_fib_rep_val := B_fib_rep (n - 3773) (by omega)
          have h_sub_fib : n - 3773 - 1 = n - 3774 := by omega
          rw [h_sub_fib] at h_fib_rep_val
          rw [h_fib_rep_val]
          have h_fib_add_two := @Nat.fib_add_two (n - 3774)
          have h_sub_fib2 : n - 3774 + 2 = n - 3772 := by omega
          have h_sub_fib3 : n - 3774 + 1 = n - 3773 := by omega
          rw [h_sub_fib2, h_sub_fib3] at h_fib_add_two
          rw [h_fib_add_two]
          rw [A355898_3772_eq]
          rw [A3772_identity]
          have h_pos_b0 : 1 ≤ B 0 := B_pos 0
          have h_pos_b1 : 1 ≤ B 1 := B_pos 1
          omega
        rw [h_fib]
        have h_eq_3774 : A355898 3774 + 1 = B 1 := by
          have h_eq_loop_3774 : A355898 3774 = B 1 - 1 := A355898_eq_B 3774 (by omega)
          have h_pos_b1 : 1 ≤ B 1 := B_pos 1
          omega
        rw [h_eq_3774]
