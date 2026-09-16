import FormalConjectures.Util.ProblemImports

open Nat

def b_A145062 (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | k_plus_1 => if k_plus_1 % 2 = 0 then k_plus_1 / 2 + 1 else 0

noncomputable def A145062_aux : ℕ → ℕ → ℕ
| 0, 0 => 1
| 0, _ => 0
| n + 1, k =>
  let prev_A := A145062_aux n
  let down_step_contrib := prev_A (k + 1)
  let up_step_contrib := if k = 0 then 0 else prev_A (k - 1)
  let level_step_contrib := b_A145062 k * prev_A k
  down_step_contrib + up_step_contrib + level_step_contrib

noncomputable def a (n : ℕ) : ℕ := A145062_aux n 0

def sequence_s_int : ℤ → ℕ := fun _ => 0

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) :=
by sorry

theorem oeis_145062_conjecture_0.disproof : ¬ (type_of% @oeis_145062_conjecture_0) := by
  intro h
  rcases h with ⟨k, hk⟩
  have h1 : a 0 = sequence_s_int (0 + k) := hk 0
  have h_a0 : a 0 = 1 := rfl
  rw [h_a0] at h1
  have h_s : sequence_s_int (0 + k) = 0 := rfl
  rw [h_s] at h1
  contradiction

#print axioms oeis_145062_conjecture_0.disproof
