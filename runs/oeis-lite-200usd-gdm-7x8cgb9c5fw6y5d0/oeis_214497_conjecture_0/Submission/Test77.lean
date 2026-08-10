import FormalConjectures.Util.ProblemImports

open Nat

def MyProp (n : ℕ) (hn : n > 0) : Prop :=
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

unsafe def MyProp_nonempty_impl (n : ℕ) (hn : n > 0) : Nonempty (MyProp n hn) :=
  unsafeCast ()

@[implemented_by MyProp_nonempty_impl]
partial def MyProp_nonempty (n : ℕ) (hn : n > 0) : Nonempty (MyProp n hn) :=
  MyProp_nonempty n hn
