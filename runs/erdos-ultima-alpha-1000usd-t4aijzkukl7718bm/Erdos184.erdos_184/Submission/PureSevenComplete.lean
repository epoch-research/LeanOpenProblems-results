import Submission.PureSevenComplete00
import Submission.PureSevenComplete01
import Submission.PureSevenComplete02
import Submission.PureSevenComplete03
import Submission.PureSevenComplete04
import Submission.PureSevenComplete05
import Submission.PureSevenComplete06
import Submission.PureSevenComplete07
import Submission.PureSevenComplete08
import Submission.PureSevenComplete09
import Submission.PureSevenComplete10
import Submission.PureSevenComplete11
import Submission.PureSevenComplete12
namespace Erdos184Work.PureSevenFactor
open PureSevenRowModel PureSevenProjectionNumbers
lemma complete_factored : ∀ r e0, CompleteAt r e0 := by
  intro r
  fin_cases r
  · exact complete_case0
  · exact complete_case1
  · exact complete_case2
  · exact complete_case3
  · exact complete_case4
  · exact complete_case5
  · exact complete_case6
  · exact complete_case7
  · exact complete_case8
  · exact complete_case9
  · exact complete_case10
  · exact complete_case11
  · exact complete_case12
lemma not_compatible (q : Rows) (r : Fin 13) (h : project6 q = repRows r) : ¬ Compatible q :=
  not_compatible_of_factored complete_factored q r h
#print axioms not_compatible
end Erdos184Work.PureSevenFactor
