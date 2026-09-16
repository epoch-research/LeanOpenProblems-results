cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports
axiom A087455_satisfies_Benfords_law : Prop
theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := answer(sorry)
theorem oeis_87455_conjecture_0.disproof : ¬ (type_of% @oeis_87455_conjecture_0) := by sorry
INNER_EOF
lake build Submission.Spec
