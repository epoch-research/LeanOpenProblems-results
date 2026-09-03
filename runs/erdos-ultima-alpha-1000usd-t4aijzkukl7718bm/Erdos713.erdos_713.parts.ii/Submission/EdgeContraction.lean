import FormalConjecturesUtil
import Submission.VertexMerging

/-! Edge contraction as edge deletion followed by a nonadjacent merger. -/
open SimpleGraph Finset
namespace Erdos713EdgeContraction
open Erdos713VertexMerging
variable {V W : Type*}
set_option maxHeartbeats 2000000

def eraseEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V := G.deleteEdges {s(u,v)}

lemma eraseEdge_not_adj (G : SimpleGraph V) (u v : V) : ¬ (eraseEdge G u v).Adj u v := by
  simp [eraseEdge]

def contract (G : SimpleGraph V) (u v : V) : SimpleGraph {x : V // x ≠ v} :=
  merge (eraseEdge G u v) u v (eraseEdge_not_adj G u v)

lemma eraseEdge_commonNeighbors (G : SimpleGraph V) (u v : V) :
    (eraseEdge G u v).commonNeighbors u v = G.commonNeighbors u v := by
  ext x
  simp only [mem_commonNeighbors,eraseEdge,deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hu,_⟩,⟨hv,_⟩⟩
    exact ⟨hu,hv⟩
  · rintro ⟨hu,hv⟩
    refine ⟨⟨hu,?_⟩,⟨hv,?_⟩⟩
    · rintro (⟨_,hxv⟩ | ⟨_,hxu⟩)
      · exact hv.ne hxv.symm
      · exact hu.ne hxu.symm
    · rintro (⟨_,hxv⟩ | ⟨_,hxu⟩)
      · exact hv.ne hxv.symm
      · exact hu.ne hxu.symm

lemma eraseEdge_le (G : SimpleGraph V) (u v : V) : eraseEdge G u v ≤ G :=
  G.deleteEdges_le _

lemma eraseEdge_edge_count [Fintype V] {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    Nat.card (eraseEdge G u v).edgeSet+1 = Nat.card G.edgeSet := by
  classical
  have he : (eraseEdge G u v).edgeFinset = G.edgeFinset.erase s(u,v) := by
    rw [eraseEdge,← Finset.coe_singleton,edgeFinset_deleteEdges,sdiff_singleton_eq_erase]
  have hh := card_erase_add_one (show s(u,v) ∈ G.edgeFinset by simpa using huv)
  rw [← he] at hh
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hh

lemma contract_edge_count [Fintype V] {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    Nat.card (contract G u v).edgeSet + Nat.card (G.commonNeighbors u v)+1 = Nat.card G.edgeSet := by
  have hm := merge_edge_count (eraseEdge G u v) huv.ne (eraseEdge_not_adj G u v)
  rw [eraseEdge_commonNeighbors] at hm
  have he := eraseEdge_edge_count huv
  dsimp only [contract]
  omega

lemma safe_contract_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    {u v : V} (huv : G.Adj u v) (hsafe : H.Free (contract G u v)) :
    Nat.card G.edgeSet ≤ extremalNumber (Fintype.card V-1) H+Nat.card (G.commonNeighbors u v)+1 := by
  classical
  have hc : Fintype.card {x : V // x ≠ v} = Fintype.card V-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hbound : Nat.card (contract G u v).edgeSet ≤ extremalNumber (Fintype.card V-1) H := by
    have hh := card_edgeFinset_le_extremalNumber hsafe
    rw [hc] at hh
    simpa only [edgeFinset_card,Nat.card_eq_fintype_card] using hh
  have he := contract_edge_count huv
  omega

lemma contract_contains_of_backward [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H) {s : ℝ}
    (hgap : s < (extremalNumber (Fintype.card V) H : ℝ)-
      (extremalNumber (Fintype.card V-1) H : ℝ))
    {u v : V} (huv : G.Adj u v)
    (hsmall : (Nat.card (G.commonNeighbors u v) : ℝ)+1 ≤ s) : H ⊑ contract G u v := by
  by_contra hh
  have hb := safe_contract_bound H G huv hh
  rw [he] at hb
  have hbR : (extremalNumber (Fintype.card V) H : ℝ) ≤
      (extremalNumber (Fintype.card V-1) H : ℝ)+(Nat.card (G.commonNeighbors u v) : ℝ)+1 := by
    exact_mod_cast hb
  linarith

#print axioms contract_edge_count
#print axioms contract_contains_of_backward
end Erdos713EdgeContraction
