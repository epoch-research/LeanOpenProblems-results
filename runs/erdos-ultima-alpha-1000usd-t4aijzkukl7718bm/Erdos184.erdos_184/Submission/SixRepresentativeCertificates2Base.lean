import Submission.PureSixRowModel2
import Submission.LabelCycleCertificates
namespace Erdos184Work.SixRepresentativeCertificates2
open PureSixRowModel2 LabelKernel Erdos184Serial
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
abbrev Representatives := Fin 10
def representativeKey (r : Representatives) : ℕ := (if r.val < 5 then (if r.val < 2 then (if r.val < 1 then 766166303 else 832521503) else (if r.val < 3 then 1077466343 else (if r.val < 4 then 1118938335 else 1118938338))) else (if r.val < 7 then (if r.val < 6 then 1118938340 else 1118938343) else (if r.val < 8 then 1118938364 else (if r.val < 9 then 1118938401 else 1118938402))))
def good : Finset Representatives := ∅
def Certificate (r : Representatives) : Prop :=
  ∃ D : PartitionData E W,
    D.Valid (src (unkey (representativeKey r))) (dst (unkey (representativeKey r))) Finset.univ ∧
    (D.size ≤ 6 → D.size = 2 ∧ r ∈ good)
end Erdos184Work.SixRepresentativeCertificates2
