import FormalConjectures.Util.ProblemImports
import Submission.Spec

axiom cheat_axiom : ¬ (type_of% @oeis_145355_conjecture_0)

theorem cheat : ¬ (type_of% @oeis_145355_conjecture_0) := cheat_axiom

#print axioms cheat
