import FormalConjectures.Util.ProblemImports
open Nat List Finset

def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun u =>
    Finset.sum (Finset.range (n - u + 1)) fun v =>
      Finset.sum (Finset.range (n - (u + v) + 1)) fun w =>
        let x := n - (u + v + w)
        if is_binary_palindrome u ∧ is_binary_palindrome v ∧
           is_binary_palindrome w ∧ is_binary_palindrome x
        then 1 else 0

theorem reduction (n u v w x : ℕ) (h : u + v + w + x = n)
    (hu : is_binary_palindrome u) (hv : is_binary_palindrome v)
    (hw : is_binary_palindrome w) (hx : is_binary_palindrome x) : 0 < a n := by
  unfold a
  have hu' : u ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ => Nat.zero_le _) hu')
  have hv' : v ∈ Finset.range (n - u + 1) := Finset.mem_range.2 (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ => Nat.zero_le _) hv')
  have hw' : w ∈ Finset.range (n - (u + v) + 1) := Finset.mem_range.2 (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun i _ => Nat.zero_le _) hw')
  dsimp only
  have hxe : n - (u + v + w) = x := by omega
  rw [hxe, if_pos ⟨hu, hv, hw, hx⟩]
  exact Nat.one_pos
  -- close 0 < 1
