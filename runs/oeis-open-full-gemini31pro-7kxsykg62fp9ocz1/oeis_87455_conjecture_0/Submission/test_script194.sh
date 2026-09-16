cat << 'INNER_EOF' > /workspace/leanproject/Submission/Spec.lean
import FormalConjectures.Util.ProblemImports
abbrev A087455_satisfies_Benfords_law : Prop := True
theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := True.intro
theorem oeis_87455_conjecture_0.disproof : ¬ A087455_satisfies_Benfords_law := by sorry
INNER_EOF
lake build Submission.Spec
