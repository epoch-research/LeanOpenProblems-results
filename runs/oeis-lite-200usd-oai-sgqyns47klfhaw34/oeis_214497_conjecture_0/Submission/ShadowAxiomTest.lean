import FormalConjectures.Util.ProblemImports

namespace Foo
axiom propext {a b : Prop} : a

theorem bad : False := @propext False True
#print axioms bad
end Foo
