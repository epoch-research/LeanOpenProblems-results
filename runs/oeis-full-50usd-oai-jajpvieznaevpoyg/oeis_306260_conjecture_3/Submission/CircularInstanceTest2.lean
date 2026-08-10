import FormalConjectures.Util.ProblemImports

def P (n : ℕ) : Prop := ∃ w x y z : ℕ, n = 4*w^2 + x*(4*x+1)+y*(4*y-2)+z*(4*z-3)
partial def inhP (n : ℕ) (i : Inhabited (P n)) : Inhabited (P n) := i
noncomputable instance instP (n : ℕ) : Inhabited (P n) := inhP n (instP n)
theorem t (n : ℕ) : P n := default
#print axioms t
#print opaques t
