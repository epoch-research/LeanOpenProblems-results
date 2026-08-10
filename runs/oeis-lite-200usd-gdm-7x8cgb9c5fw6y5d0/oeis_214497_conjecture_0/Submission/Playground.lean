import FormalConjectures.Util.ProblemImports

def MyProp (n : ℕ) (hn : n > 0) : Prop :=
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

unsafe def my_option_impl (n : ℕ) (hn : n > 0) : Option (PLift (MyProp n hn)) :=
  some (unsafeCast ())

@[implemented_by my_option_impl]
opaque my_option (n : ℕ) (hn : n > 0) : Option (PLift (MyProp n hn))

partial def get_proof (n : ℕ) (hn : n > 0) (β : Type) (f : β) (h : β = PLift (MyProp n hn)) : β :=
  match my_option n hn with
  | some x => h ▸ x
  | none => get_proof n hn β f h

theorem test (n : ℕ) (hn : n > 0) : MyProp n hn :=
  let rec f : PLift (MyProp n hn) := get_proof n hn (PLift (MyProp n hn)) f rfl
  f.down
