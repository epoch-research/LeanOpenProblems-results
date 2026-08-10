import FormalConjectures.Util.ProblemImports

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False

unsafe def get_y4_unsafe (P : Prop) : PLift (PLift (S P) → False) :=
  unsafeCast ()

@[implemented_by get_y4_unsafe]
partial def get_y4_safe (P : Prop) : PLift (PLift (S P) → False) :=
  get_y4_safe P
