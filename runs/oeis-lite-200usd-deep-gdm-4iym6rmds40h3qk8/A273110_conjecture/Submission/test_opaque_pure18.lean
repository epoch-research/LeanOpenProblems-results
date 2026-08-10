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

def my_inst_fn_2 (n : Nat) (P : Prop) : Inhabited (Nonempty P) :=
  match n with
  | 0 => ⟨@my_const 0 P (my_inst_fn 0 P)⟩
  | m + 1 => ⟨@my_const (m + 1) P (my_inst_fn m P)⟩
termination_by n
decreasing_by
  · sorry
  · omega

-- Is there any way to write the 0 case without recursion?
-- E.g. `0 => ⟨default⟩`?
-- But wait! To write `0 => ⟨default⟩`, we need `Inhabited (Nonempty P)` to be already synthesized or available.
-- But the goal of `my_inst_fn` IS to construct an instance of `Inhabited (Nonempty P)`.
-- If we already have `Inhabited (Nonempty P)`, we don't need `my_inst_fn`!
-- Wait! Is there another typeclass or instance we can use?
-- What about `Nonempty (Inhabited (Nonempty P))`?
-- Or what if we use `Classical.choice`?
-- `Classical.choice` requires `Nonempty (Inhabited (Nonempty P))`.
-- But `Nonempty (Inhabited (Nonempty P))` is definitionally equal to `Nonempty (Nonempty P)`, which is equivalent to `Nonempty P`.
-- This is a circularity.
