import FormalConjectures.Util.ProblemImports

open Nat List

def rev_base (b n : ℕ) : ℕ := Nat.ofDigits b (Nat.digits b n |>.reverse)

noncomputable def A077408 : ℕ → ℕ
  | 0 => 103
  | n + 1 => A077408 n + rev_base 3 (A077408 n)

def is_base_palindrome (b n : ℕ) : Prop := n = rev_base b n

theorem oeis_77408_conjecture_0 : ∀ n : ℕ, ¬ (is_base_palindrome 3 (A077408 n)) := sorry

theorem oeis_77408_conjecture_0.disproof : ¬ (type_of% @oeis_77408_conjecture_0) := sorry
