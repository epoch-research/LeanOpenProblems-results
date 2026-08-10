import FormalConjectures.Util.ProblemImports
structure Sol (n : ℕ) where
  w : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  h : n = 4*w^2 + x*(4*x+1)+y*(4*y-2)+z*(4*z-3)
  deriving Nonempty
#check Sol.instNonempty
#print axioms Sol.instNonempty
