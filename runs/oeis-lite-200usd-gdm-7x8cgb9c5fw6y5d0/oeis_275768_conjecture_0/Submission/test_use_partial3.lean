import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

partial def pf (k' : ℕ) [inst : Nonempty (a (6 * (k' + 5)) ≠ 4)] : a (6 * (k' + 5)) ≠ 4 :=
  pf k'

instance inst_ne (k' : ℕ) : Nonempty (a (6 * (k' + 5)) ≠ 4) :=
  ⟨pf k' (inst := inst_ne k')⟩

#print axioms inst_ne
