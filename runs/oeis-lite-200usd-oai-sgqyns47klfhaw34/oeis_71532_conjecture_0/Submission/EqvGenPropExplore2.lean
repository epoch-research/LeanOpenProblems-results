import FormalConjectures.Util.ProblemImports
namespace EqvGenProp2

def r (A B : Prop) : Prop := B

theorem conn (P : Prop) : Relation.EqvGen r True P := by
  apply Relation.EqvGen.symm
  exact Relation.EqvGen.rel P True trivial

theorem arbitrary (P : Prop) : P := by
  have h := conn P
  cases h with
  | rel x y hrel =>
      trace_state
      exact hrel
  | refl x =>
      trace_state
      trivial
  | symm x y hxy =>
      trace_state
      sorry
  | trans x y z hxy hyz =>
      trace_state
      sorry

#print axioms conn
#print axioms arbitrary
end EqvGenProp2
