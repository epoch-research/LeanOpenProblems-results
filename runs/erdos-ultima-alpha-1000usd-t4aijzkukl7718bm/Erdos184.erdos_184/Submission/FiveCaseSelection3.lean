import Submission.FiveCertificates3Base
import Submission.PureFiveComplete3
import Submission.FiveProjectionCode30
import Submission.FiveProjectionCode31
import Submission.FiveProjectionCode32
import Submission.FiveProjectionCode33
import Submission.FiveProjectionCode34

/-! Selection of a checked finite case from arbitrary canonical row orders. -/
namespace Erdos184Work.FiveRows3
open CanonicalThreeReduction
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
lemma raw_compatible (o : Orders) (h : LocalBounds b hb o) :
    PureFiveFilter3.Compatible (key o) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change FiveProjectionCode30.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode30.compatible o h
  · change FiveProjectionCode31.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode31.compatible o h
  · change FiveProjectionCode32.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode32.compatible o h
  · change FiveProjectionCode33.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode33.compatible o h
  · change FiveProjectionCode34.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode34.compatible o h

lemma exists_case (o : Orders) (h : LocalBounds b hb o) : ∃ i : Cases, caseKey i = key o := by
  obtain ⟨i,_,hi⟩ := PureFiveFilter3.exists_case_of_compatible (key_lt o) (raw_compatible o h)
  exact ⟨i,hi⟩
noncomputable def index (o : Orders) (h : LocalBounds b hb o) : Cases := (exists_case o h).choose
lemma index_key (o : Orders) (h : LocalBounds b hb o) : caseKey (index o h) = key o :=
  (exists_case o h).choose_spec
#print axioms exists_case
#print axioms index_key
end Erdos184Work.FiveRows3
