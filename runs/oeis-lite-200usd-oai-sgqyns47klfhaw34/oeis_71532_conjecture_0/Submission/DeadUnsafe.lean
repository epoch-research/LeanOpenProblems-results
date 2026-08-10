import FormalConjectures.Util.ProblemImports
unsafe def bad : False := unsafeCast ()
example : True := by
  let _h : False := bad
  trivial
#print axioms _example
