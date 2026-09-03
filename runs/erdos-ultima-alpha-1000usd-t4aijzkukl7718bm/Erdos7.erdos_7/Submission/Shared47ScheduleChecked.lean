import Submission.Shared47Rows
import Submission.Shared47Schedule

/-! All twelve numerical rows of the suffix schedule are kernel certified. -/
namespace Erdos7Shared47Schedule
open Erdos7Shared47Rows
lemma later_valid (j : Fin 12) : Valid (later j) (future j) := by
  fin_cases j
  · exact stage7_valid
  · exact stage11_valid
  · exact stage13_valid
  · exact stage17_valid
  · exact stage19_valid
  · exact stage23_valid
  · exact stage29_valid
  · exact stage31_valid
  · exact stage37_valid
  · exact stage41_valid
  · exact stage43_valid
  · exact stage47_valid
#print axioms later_valid
end Erdos7Shared47Schedule
