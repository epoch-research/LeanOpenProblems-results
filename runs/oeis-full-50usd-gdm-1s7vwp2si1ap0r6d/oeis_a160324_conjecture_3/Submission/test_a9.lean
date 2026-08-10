import FormalConjectures.Util.ProblemImports

open Nat

def pentagonal (y : ℕ) : ℕ := (3 * y ^ 2 - y) / 2
def hexagonal (z : ℕ) : ℕ := 2 * z ^ 2 - z

def a (n : ℕ) : ℕ :=
  let P5 := pentagonal
  let P6 := hexagonal
  let max_coord_bound := n.sqrt + 2

  (Finset.range max_coord_bound).sum fun x =>
  (Finset.range max_coord_bound).sum fun y =>
  (Finset.range max_coord_bound).sum fun z =>
    if x^2 + P5 y + P6 z = n then 1 else 0

lemma sqrt_9 : Nat.sqrt 9 = 3 := by
  have h1 : 3 ≤ Nat.sqrt 9 := by
    rw [le_sqrt]
  have h2 : Nat.sqrt 9 < 4 := by
    rw [lt_iff_not_ge]
    intro h
    rw [le_sqrt] at h
    contradiction
  omega

theorem a_9 : a 9 = 2 := by
  unfold a
  rw [sqrt_9]
  decide
