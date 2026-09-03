import Submission.Work
import Submission.CarrierCount
import Submission.CarrierLength

/-! Endpoint charging for disjoint fully marked groups outside a cycle. -/
namespace Erdos583CarrierGroupsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MarkedCycleGroups
open Erdos583CarrierCountDevelopment Erdos583CarrierLengthDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

noncomputable def carrierIndices (T : TrailFamily G k) (i : Fin k) (S : Set V) : Finset (Fin k) :=
  Finset.univ.filter (fun j ↦ j ≠ i ∧ Touches S (T.walk j).toSubgraph)

lemma carrierIndices_card (T : TrailFamily G k) (i : Fin k) (S : Set V)
    (hi : Touches S (T.walk i).toSubgraph) :
    (carrierIndices T i S).card+1=carrierCount T S := by
  classical
  let A := Finset.univ.filter (fun j ↦ Touches S (T.walk j).toSubgraph)
  have he : carrierIndices T i S=A.erase i := by ext j; simp [carrierIndices,A]
  have hc : A.card=carrierCount T S := by simp only [A,carrierCount,Finset.card_filter]
  rw [he,←hc]
  exact Finset.card_erase_add_one (by simp [A,hi])

lemma marked_outside_groups_card [Fintype V] {I : Type*} [Fintype I]
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i : Fin k) {r : V} (C : G.Walk r r) (hC : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph)
    (hmax : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=C.toSubgraph →
      PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts ≤ carrierCount T C.toSubgraph.verts)
    (hmin : ∀ U : TrailFamily G k, U.score=T.score → (U.walk i).toSubgraph=C.toSubgraph →
      PreservesIncidence T U C.toSubgraph.verts →
      carrierCount U C.toSubgraph.verts=carrierCount T C.toSubgraph.verts →
      carrierLength T C.toSubgraph.verts ≤ carrierLength U C.toSubgraph.verts)
    (F : I → Finset (Fin k)) (hiF : ∀ c, i ∉ F c)
    (hFC : ∀ c, ∀ x ∈ (selectedGraph T (F c)).support, x ∉ C.support)
    (hmark : ∀ c, ∀ x ∈ (selectedGraph T (F c)).support,
      MarkedPartition (selectedGraph T (F c)) (F c).card x)
    (hdis : ∀ c d, c ≠ d → Disjoint (selectedGraph T (F c)).support (selectedGraph T (F d)).support)
    (hhit : ∀ c, ∃ j ∈ carrierIndices T i C.toSubgraph.verts,
      ∃ x ∈ (T.walk j).support, x ∈ (selectedGraph T (F c)).support) :
    Fintype.card I ≤ 2*(carrierIndices T i C.toSubgraph.verts).card := by
  classical
  let E := {j // j ∈ carrierIndices T i C.toSubgraph.verts} × Bool
  have hex (c : I) : ∃ e : E, T.endpoint (e.1.val,e.2) ∈ (selectedGraph T (F c)).support := by
    obtain ⟨j,hj,hhitj⟩ := hhit c
    have hj' := (Finset.mem_filter.mp hj).2
    have hjF : j ∉ F c := by
      intro hmem
      obtain ⟨x,hx,y,hxy⟩ := hj'.2
      exact hFC c x ⟨y,j,hmem,hxy⟩ (C.mem_verts_toSubgraph.mp hx)
    rcases fully_marked_group_contains_carrier_endpoint T hs i j hj'.1.symm C hC hi hmax hmin
      (F c) (hiF c) hjF (hFC c) (hmark c) hj'.2 hhitj with hstart|hfinish
    · exact ⟨(⟨j,hj⟩,true),hstart⟩
    · exact ⟨(⟨j,hj⟩,false),hfinish⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro c d he
    by_contra hne
    exact Set.disjoint_left.mp (hdis c d hne) (hf c) (he.symm ▸ hf d)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [E,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe,Nat.mul_comm] using hc

end Erdos583CarrierGroupsDevelopment
