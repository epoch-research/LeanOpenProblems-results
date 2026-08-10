import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  let an_1 := a (n + 1)
  let an_2 := a n
  if Nat.Prime an_1 ∧ an_1 > 2 then
    an_1 - an_2
  else
    an_1 + an_2

-- unfolding lemmas
lemma a_succ_succ (n : ℕ) :
    a (n + 2) = if Nat.Prime (a (n+1)) ∧ a (n+1) > 2 then a (n+1) - a n else a (n+1) + a n := by
  rw [a]

lemma a_add (n : ℕ) (h : ¬ (Nat.Prime (a (n+1)) ∧ a (n+1) > 2)) :
    a (n + 2) = a (n+1) + a n := by
  rw [a_succ_succ]; simp [h]

lemma a_sub (n : ℕ) (h : Nat.Prime (a (n+1)) ∧ a (n+1) > 2) :
    a (n + 2) = a (n+1) - a n := by
  rw [a_succ_succ]; simp [h]

#check @a_add
