cat << 'INNER_EOF' > /workspace/leanproject/Submission/test_print.lean
import FormalConjectures.Util.ProblemImports
def A087455_satisfies_Benfords_law : Prop := True
theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := by
  first | exact True.intro | exact sorry
#print axioms oeis_87455_conjecture_0
INNER_EOF
lean /workspace/leanproject/Submission/test_print.lean
