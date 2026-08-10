import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ := 1

def witness_set (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  let max_sq_term_root := Nat.sqrt n + 1
  let max_quad_term_root := Nat.sqrt (Nat.sqrt n) + 1
  let is_perfect_square (m : ℕ) : Bool := (Nat.sqrt m) ^ 2 = m
  Finset.filter (fun ⟨⟨z, y⟩, x⟩ =>
    let rest := 2 * x^2 + y^4 + 3 * z^4
    decide (rest ≤ n) && decide (is_perfect_square (n - rest))
  ) ((range max_quad_term_root ×ˢ range max_quad_term_root) ×ˢ range max_sq_term_root)

lemma a_pos_of_exists (n x y z : ℕ)
    (hz : z < Nat.sqrt (Nat.sqrt n) + 1)
    (hy : y < Nat.sqrt (Nat.sqrt n) + 1)
    (hx : x < Nat.sqrt n + 1)
    (hrest : 2 * x^2 + y^4 + 3 * z^4 ≤ n)
    (hsq : (Nat.sqrt (n - (2 * x^2 + y^4 + 3 * z^4)))^2 = n - (2 * x^2 + y^4 + 3 * z^4)) :
    a n > 0 := sorry

lemma a_pos_of_nonempty (n : ℕ) (h : (witness_set n).Nonempty) : a n > 0 := by
  rcases h with ⟨⟨⟨z, y⟩, x⟩, h_mem⟩
  rw [witness_set, mem_filter, mem_product, mem_product, mem_range, mem_range, mem_range] at h_mem
  rcases h_mem with ⟨⟨⟨hz, hy⟩, hx⟩, h_cond⟩
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
  rcases h_cond with ⟨hrest, hsq⟩
  exact a_pos_of_exists n x y z hz hy hx hrest hsq
