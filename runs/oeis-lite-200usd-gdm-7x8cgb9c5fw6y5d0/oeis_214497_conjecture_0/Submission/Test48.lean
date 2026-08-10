import FormalConjectures.Util.ProblemImports

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False

partial def loop_get_proof_infinity2 (P : Prop) (y : PLift (R P) → False) : PLift (S P) → False :=
  loop_get_proof_infinity2 P y
