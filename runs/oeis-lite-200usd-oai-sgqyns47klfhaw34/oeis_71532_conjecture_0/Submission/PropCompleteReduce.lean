import FormalConjectures.Util.ProblemImports

#reduce Classical.propComplete True
#reduce Classical.propComplete False
#reduce Classical.propComplete (0=1)
#eval (match Classical.propComplete True with | Or.inl _ => true | Or.inr _ => false)
#eval (match Classical.propComplete False with | Or.inl _ => true | Or.inr _ => false)
