import FormalConjectures.Util.ProblemImports

open Nat BigOperators

def A228425 (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun x ↦
    let y := n - x
    if Nat.Prime ((x * (x + 1) / 2) + y ^ 2) then 1 else 0

def polygonal_number (m x : ℕ) : ℕ :=
  (m - 2) * x * (x - 1) / 2 + x

def PolygonalPrimeSumCondition (k : ℕ) : Prop :=
  ∀ n : ℕ, 1 < n →
    ∃ x y : ℕ,
      0 < x ∧ 0 < y ∧ n = x + y ∧
      Nat.Prime ((polygonal_number k x) + (polygonal_number (k + 1) y))

theorem oeis_a228425_conjecture_3 (k : ℕ) :
  PolygonalPrimeSumCondition k ↔ k = 3 ∨ k = 39 ∨ k = 99 :=
  sorry

theorem oeis_a228425_conjecture_3.disproof : ¬ (∀ k : ℕ, PolygonalPrimeSumCondition k ↔ k = 3 ∨ k = 39 ∨ k = 99) := by
  intro h
  have hk2 := h 2
  have h2 : PolygonalPrimeSumCondition 2 := by
    sorry
  have h2_eq : 2 = 3 ∨ 2 = 39 ∨ 2 = 99 := hk2.mp h2
  revert h2_eq
  decide
