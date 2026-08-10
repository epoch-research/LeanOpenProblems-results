import FormalConjectures.Util.ProblemImports
import Submission.Spec

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

-- Let's test if we can do some type tricks
def test_trick : Set.Finite {n : ℕ | a n = 0} := by
  sorry
