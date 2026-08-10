import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators
set_option maxRecDepth 100000

def A297707 (n : ℕ) : ℕ :=
  let k_tuple_factorial (n k : ℕ) : ℕ :=
    if 0 < k then
      let max_j : ℕ := (n - 1) / k
      Finset.prod (range (max_j + 1)) fun j => n - j * k
    else
      1
  Finset.prod (Ico 1 n) fun k => k_tuple_factorial n k

def Nat.prevPrime (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range n)).max.getD 0

def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

instance (n : ℕ) : Decidable (IsComposite n) :=
  decidable_of_iff (1 < n ∧ ¬ Nat.Prime n) Iff.rfl

example : ¬ IsComposite (A297707 3 - Nat.prevPrime (A297707 3)) := by decide
example : ¬ IsComposite (A297707 4 - Nat.prevPrime (A297707 4)) := by decide
example : ¬ IsComposite (A297707 5 - Nat.prevPrime (A297707 5)) := by decide
example : ¬ IsComposite (A297707 6 - Nat.prevPrime (A297707 6)) := by decide
example : ¬ IsComposite (A297707 7 - Nat.prevPrime (A297707 7)) := by decide
example : ¬ IsComposite (A297707 8 - Nat.prevPrime (A297707 8)) := by decide
example : ¬ IsComposite (A297707 9 - Nat.prevPrime (A297707 9)) := by decide
example : ¬ IsComposite (A297707 10 - Nat.prevPrime (A297707 10)) := by decide





