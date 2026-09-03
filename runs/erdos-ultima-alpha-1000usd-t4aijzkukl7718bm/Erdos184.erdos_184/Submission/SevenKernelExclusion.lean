import Submission.SevenCaseCompatibility
import Submission.PureSevenActions
import Submission.PureSevenComplete
import Submission.SevenRepresentativeRows
import Submission.CyclicRowLocalBounds

/-! Exclusion of the all-single seven-color layout from the local bounds.
This is an auxiliary finite-layout result, not an arbitrary-core bound. -/
namespace Erdos184Work.SevenKernelExclusion
open CanonicalThreeReduction SevenRows SevenCanonicalRaw LabelKernel
open PureSevenProjectionNumbers
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma not_localBounds (o : Orders) : ¬ LocalBounds b hb o := by
  intro h
  let q := rawRows o
  let o6 := SevenProjection6.smallOrders o
  have hs : LocalBounds SixRows0.b SixRows0.hb o6 := SevenProjection6.localBounds o h
  obtain ⟨c,hc⟩ := SixCaseCompatibility0.exists_code o6 hs
  let g := PureSixOrbitLookup0.groupOfCode c
  let r := PureSixOrbitLookup0.representativeOfCode c
  have hr : r ∈ PureSixGoodLookup.representatives := SixOrbitKernel0.good_of_code o6 hs hc
  obtain ⟨t,ht⟩ := SevenRepresentativeRows.complete r hr
  let q' := (PureSevenActions.action g).apply q
  have hcol : ColorLocalBounds (PureSevenRowModel.src q') (PureSevenRowModel.dst q') rawColor :=
    (PureSevenActions.action g).colorLocalBounds PureSevenRowModel.edge q (colored_of_local o h)
  have hcompatible : Compatible q' := SevenCaseCompatibility.colored_compatible q' hcol
  have hp : project6 q = SixCaseCompatibility0.rawRows o6 := SevenProjectionCode6.rows_eq o
  have ha : project6 q' = (PureSixActions0.action g).apply (project6 q) :=
    PureSevenActions.action_projection g q
  rw [hp] at ha
  have hb : project6 q' = PureSixRowModel0.unkey (PureSixOrbitLookup0.representativeKey r) :=
    ha.trans (SixOrbitKernel0.action_rows_eq o6 hc)
  have htrows := SevenRepresentativeRows.repRows_eq t
  rw [ht] at htrows
  have hnorm : project6 q' = PureSevenFactor.repRows t := hb.trans htrows.symm
  exact PureSevenFactor.not_compatible q' t hnorm hcompatible

lemma not_restrictions (o : Orders) : ¬ Restrictions b hb o := by
  intro h
  exact not_localBounds o (Restrictions.localBounds b hb o h)

#print axioms not_localBounds
#print axioms not_restrictions
end Erdos184Work.SevenKernelExclusion
