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

def B0 : ℕ := (A355898_loop 3772 1 1).1 + 1
def B1 : ℕ := (A355898_loop 3772 1 1).2 + 1
def A3772 : ℕ := (A355898_loop 3771 1 1).1

attribute [irreducible] B0 B1 A3772

def B : ℕ → ℕ
| 0 => B0
| 1 => B1
| k + 2 => B (k + 1) + B k

theorem A355898_3772_eq : A355898 3772 = A3772 := by
  have h := A355898_eq_loop 3771
  have h1 := congrArg Prod.fst h
  unfold A3772
  exact h1

theorem A3772_identity : A3772 + 1 = B 1 - B 0 := by
  unfold A3772 B B1 B0
  decide


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

