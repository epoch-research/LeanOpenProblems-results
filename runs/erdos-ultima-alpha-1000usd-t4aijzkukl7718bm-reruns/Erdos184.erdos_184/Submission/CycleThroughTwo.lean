import Submission.MengerPaths
import Submission.CriticalNeighborPairs
import Submission.TwoTerminalGluing

/-!
A simple cycle through two specified vertices, obtained from vertex-deletion
connectivity. Adjacent endpoints are handled separately so their common edge
is never duplicated.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleThroughTwo

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma cycle_through_pair {u v : V} (huv : u ≠ v) (hdeg : 2 ≤ G.degree u)
    (hconn : ∀ S : Set V, S.ncard ≤ 1 → ∀ a b : ↥(Sᶜ),
      (G.induce Sᶜ).Reachable a b) :
    ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      u ∈ H.verts ∧ v ∈ H.verts := by
  by_cases hadj : G.Adj u v
  · have hex : ∃ w, G.Adj u w ∧ w ≠ v := by
      by_contra! hn
      have hs : G.neighborFinset u ⊆ {v} := by
        intro w hw
        exact Finset.mem_singleton.mpr (hn w ((G.mem_neighborFinset u w).mp hw))
      have hh := Finset.card_le_card hs
      simp only [card_neighborFinset_eq_degree,Finset.card_singleton] at hh
      omega
    obtain ⟨w,huw,hwv⟩ := hex
    have hwS : w ∈ ({u} : Set V)ᶜ := by simpa using huw.ne.symm
    have hvS : v ∈ ({u} : Set V)ᶜ := by simpa using huv.symm
    obtain ⟨p,hp⟩ := (hconn {u} (by simp) ⟨w,hwS⟩ ⟨v,hvS⟩).exists_isPath
    let f : G.induce ({u} : Set V)ᶜ →g G := (SimpleGraph.Embedding.induce ({u} : Set V)ᶜ).toHom
    have huP : u ∉ (p.map f).support := by
      simp only [Walk.support_map,List.mem_map,not_exists,not_and]
      intro x _ hx
      exact x.property hx
    obtain ⟨H,hH,hwH,hvH⟩ := CriticalNeighborPairs.cycle_of_avoiding_path huw hadj hwv
      (p.map f) (Walk.map_isPath_of_injective Subtype.val_injective hp) huP
    exact ⟨H,hH,H.edge_vert hvH,H.edge_vert hvH.symm⟩
  · obtain ⟨p,hp,hd,hs⟩ := MengerMatching.exists_internally_disjoint_paths (k := 2) huv hadj
      (by intro S hS huS hvS; exact hconn S (by omega) ⟨u,huS⟩ ⟨v,hvS⟩)
    let P := p 0
    let Q := (p 1).reverse
    have hPQ : P.edges.Disjoint Q.edges := by
      simpa only [P,Q,Walk.edges_reverse,List.disjoint_reverse_right] using hd 0 1 (by decide)
    have hi : ∀ x, x ∈ P.support → x ∈ Q.support → x = u ∨ x = v := by
      intro x hx hy
      exact hs 0 1 (by decide) x hx (by simpa only [Q,Walk.support_reverse,List.mem_reverse] using hy)
    have hc := TwoTerminalGluing.append_isCycle_of_paths P Q (hp 0) (hp 1).reverse huv hPQ hi
    refine ⟨(P.append Q).toSubgraph,cycle_subgraph_regular G hc,?_,?_⟩
    · exact (P.append Q).mem_verts_toSubgraph.mpr (P.append Q).start_mem_support
    · exact (P.append Q).mem_verts_toSubgraph.mpr
        (Walk.subset_support_append_left P Q P.end_mem_support)

end Erdos184.CycleThroughTwo
