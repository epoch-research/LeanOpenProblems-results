import Mathlib

open Nat

lemma family1_identity (y z s k : ℕ) (h_eq : y^2 + 2*z^2 = k * s) (h_ge : k ≥ 2*s + y) :
  let x := k - 2*s
  x^2 + 8*y^2 + 16*z^2 = (k + 2*s)^2 := by
  intro x
  dsimp [x]
  have h_sub : k = (k - 2*s) + 2*s := by omega
  have h_eq4 : 8*y^2 + 16*z^2 = 8 * (k * s) := by
    calc 8*y^2 + 16*z^2 = 8 * (y^2 + 2*z^2) := by ring
    _ = 8 * (k * s) := by rw [h_eq]
  generalize h_A : k - 2*s = A
  have h_k_eq : k = A + 2*s := by omega
  rw [h_k_eq] at h_eq4 ⊢
  rw [add_assoc]
  rw [h_eq4]
  ring

lemma family2_identity (y z s k : ℕ) (h_eq : 2*(y^2 + 2*z^2) = k * s) (h_ge : k ≥ s + y) :
  let x := k - s
  x^2 + 8*y^2 + 16*z^2 = (k + s)^2 := by
  intro x
  dsimp [x]
  have h_sub : k = (k - s) + s := by omega
  have h_eq4 : 8*y^2 + 16*z^2 = 4 * (k * s) := by
    calc 8*y^2 + 16*z^2 = 4 * (2 * (y^2 + 2*z^2)) := by ring
    _ = 4 * (k * s) := by rw [h_eq]
  generalize h_A : k - s = A
  have h_k_eq : k = A + s := by omega
  rw [h_k_eq] at h_eq4 ⊢
  rw [add_assoc]
  rw [h_eq4]
  ring

