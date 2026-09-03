import Submission.FiveCertificates1Base
import Submission.PureFiveComplete1
import Submission.FiveProjectionCode10
import Submission.FiveProjectionCode11
import Submission.FiveProjectionCode12
import Submission.FiveProjectionCode13
import Submission.FiveProjectionCode14

/-! Selection of a checked finite case from arbitrary canonical row orders. -/
namespace Erdos184Work.FiveRows1
open CanonicalThreeReduction
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
lemma raw_compatible (o : Orders) (h : LocalBounds b hb o) :
    PureFiveFilter1.Compatible (key o) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change FiveProjectionCode10.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode10.compatible o h
  · change FiveProjectionCode11.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode11.compatible o h
  · change FiveProjectionCode12.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode12.compatible o h
  · change FiveProjectionCode13.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode13.compatible o h
  · change FiveProjectionCode14.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode14.compatible o h

lemma exists_case (o : Orders) (h : LocalBounds b hb o) : ∃ i : Cases, caseKey i = key o := by
  obtain ⟨i,_,hi⟩ := PureFiveFilter1.exists_case_of_compatible (key_lt o) (raw_compatible o h)
  exact ⟨i,hi⟩
noncomputable def index (o : Orders) (h : LocalBounds b hb o) : Cases := (exists_case o h).choose
lemma index_key (o : Orders) (h : LocalBounds b hb o) : caseKey (index o h) = key o :=
  (exists_case o h).choose_spec
#print axioms exists_case
#print axioms index_key
end Erdos184Work.FiveRows1
