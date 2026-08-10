import FormalConjectures.Util.ProblemImports

def MyProp (n : ℕ) (_ : n > 0) : Prop :=
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

partial def get_lift (n : ℕ) (hn : n > 0) : PLift (MyProp n hn) :=
  get_lift n hn

theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) :=
  (get_lift n hn).down
