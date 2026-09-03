import Submission.FiveCertificates4Base
import Submission.PureFiveComplete4
import Submission.FiveProjectionCode40
import Submission.FiveProjectionCode41
import Submission.FiveProjectionCode42
import Submission.FiveProjectionCode43
import Submission.FiveProjectionCode44

/-! Selection of a checked finite case from arbitrary canonical row orders. -/
namespace Erdos184Work.FiveRows4
open CanonicalThreeReduction
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000
set_option Elab.async false
lemma raw_compatible (o : Orders) (h : LocalBounds b hb o) :
    PureFiveFilter4.Compatible (key o) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change FiveProjectionCode40.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode40.compatible o h
  · change FiveProjectionCode41.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode41.compatible o h
  · change FiveProjectionCode42.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode42.compatible o h
  · change FiveProjectionCode43.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode43.compatible o h
  · change FiveProjectionCode44.Compatible (digit0 (key o)) (digit1 (key o)) (digit2 (key o)) (digit3 (key o)) (digit4 (key o))
    rw [digit_key0,digit_key1,digit_key2,digit_key3,digit_key4]
    exact FiveProjectionCode44.compatible o h

lemma exists_case (o : Orders) (h : LocalBounds b hb o) : ∃ i : Cases, caseKey i = key o := by
  obtain ⟨i,_,hi⟩ := PureFiveFilter4.exists_case_of_compatible (key_lt o) (raw_compatible o h)
  exact ⟨i,hi⟩
noncomputable def index (o : Orders) (h : LocalBounds b hb o) : Cases := (exists_case o h).choose
lemma index_key (o : Orders) (h : LocalBounds b hb o) : caseKey (index o h) = key o :=
  (exists_case o h).choose_spec
#print axioms exists_case
#print axioms index_key
end Erdos184Work.FiveRows4
