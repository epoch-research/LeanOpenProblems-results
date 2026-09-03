import FormalConjecturesUtil
import Submission.WengerCoverGeometry

/-! Exact counts and a power bound for C8-free permutation lifts of the
linear four-coordinate Wenger graph. This is not a proof of Erdős 713. -/
open SimpleGraph Finset
open scoped Classical
namespace Erdos713WengerCover
open Erdos713WengerRestriction
variable {K S : Type*} [Field K] [Fintype K] [Fintype S]
set_option maxHeartbeats 2000000

omit [Fintype K] [Fintype S] in
/-- At every lifted point, its neighbours are in bijection with the slopes. -/
def neighborEquiv (sigma : Point K → K → Equiv.Perm S) (p : Point K × S) :
    {l : Point K × S // Rel sigma p l} ≃ K where
  toFun l := l.val.1 0
  invFun a := ⟨(lineThrough p.1 a,sigma p.1 a p.2),rfl,rfl⟩
  left_inv l := Subtype.ext (Prod.ext l.property.1.symm l.property.2.symm)
  right_inv _ := rfl

lemma graph_edges (sigma : Point K → K → Equiv.Perm S) :
    Nat.card (graph sigma).edgeSet = (Fintype.card K)^5*Fintype.card S := by
  have hh := (graph sigma).two_mul_card_edgeFinset
  simp only [card_filter] at hh
  rw [Fintype.sum_prod_type] at hh
  simp only [Fintype.sum_sum_type,graph,Erdos713C6.bipGraph,sum_add_distrib,
    edgeFinset_card,← Nat.card_eq_fintype_card] at hh
  have hflip : (∑ l : Point K × S, ∑ p : Point K × S, if Rel sigma p l then 1 else 0) =
      ∑ p : Point K × S, ∑ l : Point K × S, if Rel sigma p l then 1 else 0 := sum_comm
  rw [hflip] at hh
  have hrow (p : Point K × S) :
      (∑ l : Point K × S, if Rel sigma p l then 1 else 0) = Fintype.card K := by
    have he := Fintype.card_congr (neighborEquiv sigma p)
    simpa only [Fintype.card_subtype,card_filter] using he
  simp_rw [hrow] at hh
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id] at hh
  simp at hh
  have he : ((Fintype.card K)^4*Fintype.card S)*Fintype.card K =
      (Fintype.card K)^5*Fintype.card S := by ring
  rw [he] at hh
  have hh' : 2*Nat.card (graph sigma).edgeSet =
      (Fintype.card K)^5*Fintype.card S + (Fintype.card K)^5*Fintype.card S := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,graph,
      Erdos713C6.bipGraph] using hh
  omega

omit [Field K] in
lemma vertices_card : Nat.card ((Point K × S) ⊕ (Point K × S)) =
    2*(Fintype.card K)^4*Fintype.card S := by
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fun,Fintype.card_fin]
  ring

/-- For a C8-free full permutation lift, 64e^5 <= n^6, where n is the
actual total vertex count including both shores. -/
theorem edge_fifth_bound [Nonempty S] (sigma : Point K → K → Equiv.Perm S)
    (hf : (cycleGraph 8).Free (graph sigma)) :
    64*(Nat.card (graph sigma).edgeSet)^5 ≤
      (Nat.card ((Point K × S) ⊕ (Point K × S)))^6 := by
  rw [graph_edges,vertices_card]
  have h := Nat.mul_le_mul_left
    (64*(Fintype.card K)^24*(Fintype.card S)^5) (field_card_le_sheets sigma hf)
  convert h using 1 <;> ring

end Erdos713WengerCover
