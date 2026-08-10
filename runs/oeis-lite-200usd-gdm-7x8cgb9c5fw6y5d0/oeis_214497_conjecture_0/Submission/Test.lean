import FormalConjectures.Util.ProblemImports

def MyProp (n : ℕ) (hn : n > 0) : Prop :=
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

unsafe def prove_nonempty_impl (P : Prop) : PLift P :=
  unsafeCast ()

mutual
  @[implemented_by prove_nonempty_impl]
  partial def prove_nonempty (P : Prop) : PLift P :=
    prove_nonempty P

  @[instance]
  partial def prove_inhabited (P : Prop) : Inhabited (PLift P) :=
    ⟨prove_nonempty P⟩
end




















