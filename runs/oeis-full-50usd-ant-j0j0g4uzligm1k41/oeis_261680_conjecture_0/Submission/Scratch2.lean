import FormalConjectures.Util.ProblemImports
open Nat List

def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

theorem inflate_palindrome (c : List ℕ) (hb : ∀ x ∈ c, x < 2) (hpal : c.reverse = c) :
    is_binary_palindrome (Nat.ofDigits 2 ((1 :: c) ++ [1])) = true := by
  unfold is_binary_palindrome
  have hb' : ∀ x ∈ ((1 :: c) ++ [1] : List ℕ), x < 2 := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | h) | rfl
    · decide
    · exact hb x h
    · decide
  have hlast : ∀ h : ((1 :: c) ++ [1] : List ℕ) ≠ [], ((1 :: c) ++ [1]).getLast h ≠ 0 := by
    intro hne
    rw [List.getLast_append_singleton]; decide
  rw [Nat.digits_ofDigits 2 (by norm_num) _ hb' hlast]
  simp [List.reverse_append, hpal]
