import Submission.SevenProjectionCode0
import Submission.SevenProjectionCode1
import Submission.SevenProjectionCode2
import Submission.SevenProjectionCode3
import Submission.SevenProjectionCode4
import Submission.SevenProjectionCode5
import Submission.SevenProjectionCode6
namespace Erdos184Work.SevenCaseCompatibility
open CanonicalThreeReduction SevenRows SevenCanonicalRaw LabelKernel
set_option maxHeartbeats 1000000
lemma compatible (o : Orders) (h : LocalBounds b hb o) :
    PureSevenProjectionNumbers.Compatible (rawRows o) :=
  ⟨SevenProjectionCode0.compatible o h,SevenProjectionCode1.compatible o h,SevenProjectionCode2.compatible o h,SevenProjectionCode3.compatible o h,SevenProjectionCode4.compatible o h,SevenProjectionCode5.compatible o h,SevenProjectionCode6.compatible o h⟩
lemma colored_compatible (q : PureSevenRowModel.Rows)
    (h : ColorLocalBounds (PureSevenRowModel.src q) (PureSevenRowModel.dst q) rawColor) :
    PureSevenProjectionNumbers.Compatible q := by
  have hh := compatible (canonical q) (local_of_colored q h)
  simpa only [rawRows_canonical] using hh
#print axioms colored_compatible
end Erdos184Work.SevenCaseCompatibility
