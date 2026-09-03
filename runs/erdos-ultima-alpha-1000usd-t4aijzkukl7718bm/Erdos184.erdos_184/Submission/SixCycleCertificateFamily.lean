import Submission.SixCycleCertificates

/-! A uniform finite-index interface to the thirteen checked certificates.
There is no assertion that this list exhausts any class of graphs. -/
open SimpleGraph
namespace Erdos184Work.SixCycleCertificates
open PathSubstitution
set_option maxHeartbeats 1800000

def sourceTable : Fin 13 → Fin 30 → Fin 15 := ![Layout0.src,Layout1.src,Layout2.src,Layout3.src,Layout4.src,Layout5.src,Layout6.src,Layout7.src,Layout8.src,Layout9.src,Layout10.src,Layout11.src,Layout12.src]
def targetTable : Fin 13 → Fin 30 → Fin 15 := ![Layout0.dst,Layout1.dst,Layout2.dst,Layout3.dst,Layout4.dst,Layout5.dst,Layout6.dst,Layout7.dst,Layout8.dst,Layout9.dst,Layout10.dst,Layout11.dst,Layout12.dst]

theorem subdivision_number_le_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (k : Fin 13) (F : Family (Fin 30) (Fin 15) G)
    (hs : F.src = sourceTable k) (ht : F.dst = targetTable k)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    Critical.number G ≤ 2 := by
  fin_cases k
  · exact Layout0.subdivision_number_le_two F hs ht hcover
  · exact Layout1.subdivision_number_le_two F hs ht hcover
  · exact Layout2.subdivision_number_le_two F hs ht hcover
  · exact Layout3.subdivision_number_le_two F hs ht hcover
  · exact Layout4.subdivision_number_le_two F hs ht hcover
  · exact Layout5.subdivision_number_le_two F hs ht hcover
  · exact Layout6.subdivision_number_le_two F hs ht hcover
  · exact Layout7.subdivision_number_le_two F hs ht hcover
  · exact Layout8.subdivision_number_le_two F hs ht hcover
  · exact Layout9.subdivision_number_le_two F hs ht hcover
  · exact Layout10.subdivision_number_le_two F hs ht hcover
  · exact Layout11.subdivision_number_le_two F hs ht hcover
  · exact Layout12.subdivision_number_le_two F hs ht hcover

#print axioms subdivision_number_le_two
end Erdos184Work.SixCycleCertificates
