import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

def f_tuple (n k : ℕ) : ℕ :=
  if 0 < k then
    let max_j : ℕ := (n - 1) / k
    Finset.prod (range (max_j + 1)) fun j => n - j * k
  else
    1

def A297707 (n : ℕ) : ℕ :=
  Finset.prod (Ico 1 n) fun k => f_tuple n k

local notation "a" => A297707

noncomputable def Nat.prevPrime (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range n)).max.getD 0

def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

example : ¬ IsComposite (a 3 - Nat.prevPrime (a 3)) := by
  dsimp [IsComposite, A297707, f_tuple, Nat.prevPrime]
  decide

example : ¬ IsComposite (a 4 - Nat.prevPrime (a 4)) := by
  dsimp [IsComposite, A297707, f_tuple, Nat.prevPrime]
  decide

example : ¬ IsComposite (a 5 - Nat.prevPrime (a 5)) := by
  dsimp [IsComposite, A297707, f_tuple, Nat.prevPrime]
  decide

example : ¬ IsComposite (a 6 - Nat.prevPrime (a 6)) := by
  dsimp [IsComposite, A297707, f_tuple, Nat.prevPrime]
  decide

