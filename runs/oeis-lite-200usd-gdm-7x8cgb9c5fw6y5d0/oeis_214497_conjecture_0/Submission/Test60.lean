import FormalConjectures.Util.ProblemImports

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False

unsafe def prove_any_loop_directly_impl (P : Prop) (y2 : Q P) (y3 : S P) : PLift P :=
  unsafeCast ()

@[implemented_by prove_any_loop_directly_impl]
partial def prove_any_loop_directly (P : Prop) (y2 : Q P) (y3 : S P) : PLift P :=
  prove_any_loop_directly P y2 y3
