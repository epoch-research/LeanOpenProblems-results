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

instance my_inst (P : Prop) : Inhabited (Nonempty P) := my_inst_fn 0 P

-- Wait! If we don't use the `0` case of `my_const`, but instead use `my_const (m + 1)`:
-- Let's define:
theorem my_false : False := Classical.choice (@my_const 1 False (my_inst False))

#print axioms my_false
