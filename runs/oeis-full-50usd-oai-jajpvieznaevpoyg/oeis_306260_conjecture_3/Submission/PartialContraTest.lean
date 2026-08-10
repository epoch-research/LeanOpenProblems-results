import FormalConjectures.Util.ProblemImports

def P (n : ℕ) : Prop := ∃ w x y z : ℕ, n = 4*w^2 + x*(4*x+1)+y*(4*y-2)+z*(4*z-3)
partial def contraP (n : ℕ) (h : ¬ P n) : False := contraP n h
#print axioms contraP
#print opaques contraP
