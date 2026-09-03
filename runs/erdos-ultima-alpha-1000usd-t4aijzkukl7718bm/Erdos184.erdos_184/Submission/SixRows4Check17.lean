import Submission.SixRows4Base
/-! A24-order normalization certificate, checked by ordinary kernel reduction. -/
namespace Erdos184Work.SixRows4
open CycleSegments
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid0_3_2 : ∀ q : Marked.Order 3,
    (SmallOrderNormalization.normalized 5 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ()))))).vertex = words0 (key0 ((q,(Sum.inl (Sum.inl (Sum.inr ())))),(Sum.inl (Sum.inl (Sum.inr ()))))) := by decide +kernel

#print axioms valid0_3_2
end Erdos184Work.SixRows4
