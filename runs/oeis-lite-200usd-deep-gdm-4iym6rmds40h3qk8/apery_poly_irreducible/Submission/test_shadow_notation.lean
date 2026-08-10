import FormalConjectures.Util.ProblemImports

def my_choose (n k : ℕ) : ℕ :=
  if n = 1 then 1 else 0

macro_rules | `($x.choose $y) => `(my_choose $x $y)

noncomputable def apery_poly (n : ℕ) : ℕ :=
  n.choose 1

set_option pp.all true
#print apery_poly




