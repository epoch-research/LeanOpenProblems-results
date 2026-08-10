import Mathlib

open scoped Real

def a : ℕ → ℝ := fun _ => 128

theorem test_unique (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (m : ℕ) :
  ∃! (z : ℤ), (z : ℝ) = a m := by
  have h1 : ∃ (x : ℤ), (x : ℝ) = a m := h_int m
  obtain ⟨x, hx⟩ := h1
  use x
  refine ⟨hx, ?_⟩
  intro y hy
  -- Since (y : ℝ) = a m and (x : ℝ) = a m, (y : ℝ) = (x : ℝ)
  have h_eq : (y : ℝ) = (x : ℝ) := by rw [hy, hx]
  exact Int.cast_injective h_eq

