import FormalConjectures.Util.ProblemImports

-- Inspect constructors/notation
#print Sat.Valuation
#print Sat.Literal
#check Sat.Literal.pos
#check Sat.Valuation.by_cases

namespace SatCurry

def lit : Sat.Literal := Sat.Literal.pos 0
-- Need a valuation. Try default?
#check (default : Sat.Valuation)
def v : Sat.Valuation := default

-- h1's type should be v.neg lit.negate, h2's type v.neg lit.
#check (fun (h1 : v.neg lit.negate) (h2 : v.neg lit) => Sat.Valuation.by_cases h1 h2)

def h1 : v.neg lit.negate := fun h2 => Sat.Valuation.by_cases h1 h2
#print axioms h1

theorem bad : False := Sat.Valuation.by_cases h1 h1
#print axioms bad
end SatCurry
