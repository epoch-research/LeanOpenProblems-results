import FormalConjectures.Util.ProblemImports

def fNot (P : Prop) (h : ¬ P) : ¬ P := h

namespace fNot
namespace _default
partial def «2» (P : Prop) (h : ¬ P) : ¬ P := h
end _default
end fNot

#check fNot._default.«2»
#check fNot._default.2

theorem bad : False := by
  exact fNot True trivial

#print axioms bad
