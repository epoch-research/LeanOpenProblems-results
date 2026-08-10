import FormalConjectures.Util.ProblemImports

def Q (P : Prop) : Prop := PLift P → False
def R (P : Prop) : Prop := PLift (Q P) → False
def S (P : Prop) : Prop := PLift (R P) → False
def T (P : Prop) : Prop := PLift (S P) → False
def U (P : Prop) : Prop := PLift (T P) → False

theorem elim_double_neg_plift (P : Prop) (h : PLift (PLift P → False) → False) : P := by
  by_contra h_not
  have h_not_plift : PLift P → False := fun hp => h_not hp.down
  exact h (PLift.up h_not_plift)

theorem solve_T (P : Prop) (h_U_not : PLift (U P)) : T P := by
  have h_arg : PLift (PLift (T P) → False) → False := fun f => f.down h_U_not.down
  exact elim_double_neg_plift (T P) h_arg
