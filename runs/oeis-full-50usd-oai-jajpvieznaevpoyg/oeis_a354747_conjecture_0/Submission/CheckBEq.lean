import FormalConjectures.Util.ProblemImports
structure Elt where u : Nat; v : Nat deriving BEq, DecidableEq
#check beq_eq_true
#check beq_iff_eq
#check BEq.beq_iff_eq
#check of_decide_eq_true
#check decide_eq_true_eq
#check Bool.eq_true_eq_eq_true
