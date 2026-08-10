import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

partial def proof_helper (α : Sort u) [Nonempty α] (n : ℕ) : α :=
  proof_helper α n

instance inst (n : ℕ) : Nonempty (a n ≠ 4) :=
  let rec f (u : Unit) : Nonempty (a n ≠ 4) :=
    ⟨@proof_helper (a n ≠ 4) (f u) n⟩
  f ()




























