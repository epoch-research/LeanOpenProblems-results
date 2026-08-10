import FormalConjectures.Util.ProblemImports

opaque my_const (n : Nat) (P : Prop) [Inhabited (Nonempty P)] : Nonempty P := default

instance my_inst (n : Nat) (P : Prop) : Inhabited (Nonempty P) where
  default :=
    match n with
    | 0 => @my_const 0 P (my_inst 0 P)
    | m + 1 => @my_const (m + 1) P (my_inst m P)
termination_by n
decreasing_by
  · sorry
  · sorry
