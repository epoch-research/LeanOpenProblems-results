import FormalConjectures.Util.ProblemImports

open Nat Set List
open scoped Classical

/--
A083753: Smallest palindromic number with exactly $n$ divisors, or 0 if no such number exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let is_palindrome (m : ℕ) : Prop := Nat.digits 10 m = (Nat.digits 10 m).reverse
  let tau (m : ℕ) : ℕ := Finset.card (Nat.divisors m)
  let S : Set ℕ := {m : ℕ | m > 0 ∧ is_palindrome m ∧ tau m = n}
  if h : S.Nonempty then sInf S else 0

theorem oeis_83753_conjecture_0 :
  ∀ (m k : ℕ),
    m > 1 ∧
    (Nat.digits 10 m = (Nat.digits 10 m).reverse) ∧
    k ≥ 5 ∧
    (∃ x : ℕ, m = x ^ k)
    →
    False
:= by
  intros m k h
  sorry

theorem oeis_83753_conjecture_0.disproof : ¬ (type_of% @oeis_83753_conjecture_0) := sorry
