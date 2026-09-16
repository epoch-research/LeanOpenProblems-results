import Mathlib
open Nat Finset
set_option maxRecDepth 200000

def step_exact (n k : Nat) (v : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let c := v.1
  let c3 := v.2.1
  let s := v.2.2
  let c_new := (c * (n - k)) / (k + 1)
  let c3_new := (c3 * (n + k)) / (k + 1)
  let m := c_new * c3_new
  let s_new := s + m * m
  (c_new, c3_new, s_new)

def apply_exact (n : Nat) (steps : Nat) (start : Nat) (v : Nat × Nat × Nat) : Nat × Nat × Nat :=
  match steps with
  | 0 => v
  | step + 1 => apply_exact n step (start + 1) (step_exact n start v)

theorem apply_exact_add (n_param steps_a steps_b : Nat) (start : Nat) (v : Nat × Nat × Nat) :
  apply_exact n_param (steps_a + steps_b) start v = apply_exact n_param steps_b (start + steps_a) (apply_exact n_param steps_a start v) := by
  induction steps_a generalizing start v with
  | zero =>
    simp [apply_exact]
  | succ k ih =>
    rw [Nat.add_succ, Nat.succ_add]
    have h1 : apply_exact n_param (k + 1) start v = apply_exact n_param k (start + 1) (step_exact n_param start v) := rfl
    rw [h1]
    have h2 : apply_exact n_param (k + steps_b + 1) start v = apply_exact n_param (k + steps_b) (start + 1) (step_exact n_param start v) := rfl
    rw [h2]
    have h3 : start + (k + 1) = start + 1 + k := by omega
    rw [h3]
    exact ih (start + 1) (step_exact n_param start v)
