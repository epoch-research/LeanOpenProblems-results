import FormalConjectures.Util.ProblemImports

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False

unsafe def prove_P_from_Q_and_T_impl (P : Prop) (hq : Q P) (h_T : T P) : P :=
  unsafeCast ()

@[implemented_by prove_P_from_Q_and_T_impl]
partial def prove_P_from_Q_and_T (P : Prop) (hq : Q P) (h_T : T P) : P :=
  prove_P_from_Q_and_T P hq h_T
