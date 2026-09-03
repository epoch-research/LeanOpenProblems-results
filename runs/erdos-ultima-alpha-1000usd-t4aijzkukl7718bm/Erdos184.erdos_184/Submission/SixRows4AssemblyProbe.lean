import Submission.SixRows4Check00
import Submission.SixRows4Check01
import Submission.SixRows4Check02
import Submission.SixRows4Check03
import Submission.SixRows4Check04
import Submission.SixRows4Check05
import Submission.SixRows4Check06
import Submission.SixRows4Check07
import Submission.SixRows4Check08
import Submission.SixRows4Check09
import Submission.SixRows4Check10
import Submission.SixRows4Check11
import Submission.SixRows4Check12
import Submission.SixRows4Check13
import Submission.SixRows4Check14
import Submission.SixRows4Check15
import Submission.SixRows4Check16
import Submission.SixRows4Check17
import Submission.SixRows4Check18
import Submission.SixRows4Check19
import Submission.SixRows4Check20
import Submission.SixRows4Check21
import Submission.SixRows4Check22
import Submission.SixRows4Check23
import Submission.SixRows4Check24
import Submission.SixRows4Check25
import Submission.SixRows4Check26
import Submission.SixRows4Check27
import Submission.SixRows4Check28
import Submission.SixRows4Check29

/-! Six-color pattern4 rows and their checked normalization certificates. -/
namespace Erdos184Work.SixRows4
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CanonicalPairKernel CycleSegments
open LabelKernel Erdos184Serial CanonicalThreeReduction
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable local instance sixRows4TheoryDecEq {I : Type*} {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _
lemma valid0_0 : ∀ q : Marked.Order 4,
    (SmallOrderNormalization.normalized 5 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))).vertex = words0 (key0 (q,(Sum.inl (Sum.inl (Sum.inl (Sum.inl (0 : Fin 2))))))) := by
  rintro ⟨q,t⟩
  fin_cases t
  · exact valid0_0_0 q
  · exact valid0_0_1 q
  · exact valid0_0_2 q
  · exact valid0_0_3 q
  · exact valid0_0_4 q

end Erdos184Work.SixRows4
