import Submission.FiveCertificates2Base
import Submission.PureFiveComplete2
import Submission.FiveProjectionCode20
import Submission.FiveProjectionCode21
import Submission.FiveProjectionCode22
import Submission.FiveProjectionCode23
import Submission.FiveProjectionCode24

/-! Selection of a checked finite case from arbitrary canonical row orders. -/
namespace Erdos184Work.FiveRows2
open CanonicalThreeReduction
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
lemma raw_compatible (o : Orders) (h : LocalBounds b hb o) :
    PureFiveFilter2.Compatible (key o) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change FiveProjectionCode20.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode20.compatible o h
  · change FiveProjectionCode21.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode21.compatible o h
  · change FiveProjectionCode22.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode22.compatible o h
  · change FiveProjectionCode23.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode23.compatible o h
  · change FiveProjectionCode24.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode24.compatible o h

lemma exists_case (o : Orders) (h : LocalBounds b hb o) : ∃ i : Cases, caseKey i = key o := by
  obtain ⟨i,_,hi⟩ := PureFiveFilter2.exists_case_of_compatible (key_lt o) (raw_compatible o h)
  exact ⟨i,hi⟩
noncomputable def index (o : Orders) (h : LocalBounds b hb o) : Cases := (exists_case o h).choose
lemma index_key (o : Orders) (h : LocalBounds b hb o) : caseKey (index o h) = key o :=
  (exists_case o h).choose_spec
#print axioms exists_case
#print axioms index_key
end Erdos184Work.FiveRows2
