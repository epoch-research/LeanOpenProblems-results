import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ := Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma mod_sum_floor_identity (n : ℕ) :
    A048153 n + n * (Finset.sum (Finset.range n) (fun k => k ^ 2 / n)) =
      Finset.sum (Finset.range n) (fun k => k ^ 2) := by
  unfold A048153
  rw [← Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact Nat.mod_add_div (k^2) n

example (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  have hid := mod_sum_floor_identity n
  exact?
