import FormalConjectures.Util.ProblemImports
class GivesFalse where pf : False
variable [GivesFalse]
theorem bad : False := GivesFalse.pf
#check bad
#print axioms bad
