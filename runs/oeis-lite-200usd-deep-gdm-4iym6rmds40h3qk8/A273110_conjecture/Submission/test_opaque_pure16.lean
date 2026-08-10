import FormalConjectures.Util.ProblemImports

opaque my_const (n : Nat) (P : Prop) [Inhabited (Nonempty P)] : Nonempty P := default

def my_inst_fn (n : Nat) (P : Prop) : Inhabited (Nonempty P) :=
  match n with
  | 0 => ⟨@my_const 0 P (my_inst_fn 0 P)⟩
  | m + 1 => ⟨@my_const (m + 1) P (my_inst_fn m P)⟩
termination_by n
decreasing_by
  · sorry
  · omega

-- What if we use `my_inst_fn 0 P` where the termination proof of `0 => ...` is NOT sorry, but instead we don't have a 0 case?
-- Wait, if `n` is `Nat`, we must cover both `0` and `m + 1`.
-- But what if we define a type `Ind` which has no base case?
-- No, all inductive types in Lean must be well-founded, otherwise Lean will reject them or we can't prove termination.
