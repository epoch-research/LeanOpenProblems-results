import FormalConjectures.Util.ProblemImports

axiom badAx : False

def constTrue (_h : False) : True := True.intro

theorem t1 : True := constTrue badAx
#print axioms t1

def chooseNat (_h : False) : Nat := 0
theorem t2 : True := by
  have n := chooseNat badAx
  trivial
#print axioms t2

theorem t3 : True := by
  let h : False := badAx
  trivial
#print axioms t3
