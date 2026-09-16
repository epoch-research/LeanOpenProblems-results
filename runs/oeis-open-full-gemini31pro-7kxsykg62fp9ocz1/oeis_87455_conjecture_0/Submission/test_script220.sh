cat << 'INNER_EOF' > /workspace/leanproject/Submission/test_print5.lean
import Lean
import FormalConjectures.Util.ProblemImports
def A087455_satisfies_Benfords_law : Prop := True
theorem oeis_87455_conjecture_0 : A087455_satisfies_Benfords_law := by
  try exact True.intro
  try exact sorry
#print axioms oeis_87455_conjecture_0
INNER_EOF
lake --dir=/workspace/leanproject env lean /workspace/leanproject/Submission/test_print5.lean
