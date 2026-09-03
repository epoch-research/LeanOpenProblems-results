import FormalConjecturesUtil
import Submission.EdgeContraction
import Submission.SplitRootPaths

/-! Obstructed contractions force short odd cycles through the contracted
edge, for nonseparable bipartite forbidden patterns. -/
open SimpleGraph
namespace Erdos713ContractionOddCycles
open Erdos713VertexMerging Erdos713VertexSplitWitnesses
open Erdos713EdgeContraction Erdos713SplitRootPaths
variable {V W : Type*}
set_option maxHeartbeats 2000000

def ShortEvenAlternative (G : SimpleGraph V) (q : ℕ) (u v : V) : Prop :=
  ∃ p : G.Walk v u, p.IsPath ∧ Even p.length ∧ p.length ≤ q ∧ s(u,v) ∉ p.edges

lemma even_alternative_of_contract [Fintype W] {H : SimpleGraph W} (hH : H.IsBipartite)
    (hRest : ∀ w, (H.induce {w}ᶜ).Preconnected) {G : SimpleGraph V} (hf : H.Free G)
    {u v : V} (hc : H ⊑ contract G u v) : ShortEvenAlternative G (Fintype.card W) u v := by
  classical
  have hfK : H.Free (eraseEdge G u v) := fun h => hf (h.trans ⟨Copy.ofLE _ _ (eraseEdge_le G u v)⟩)
  obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_copy_of_merge hfK (eraseEdge_not_adj G u v) hc
  obtain ⟨p,hp,heven,hlen⟩ := even_root_path hH w (hRest w) S hL hR
  have hpath : ∃ p0 : (eraseEdge G u v).Walk v u,
      p0.IsPath ∧ Even p0.length ∧ p0.length ≤ Fintype.card W := by
    let pm := p.map f.toHom
    refine ⟨pm.copy hv hu,?_,?_,?_⟩
    · exact (Walk.isPath_copy pm hv hu).mpr (Walk.map_isPath_of_injective f.injective hp)
    · simpa only [Walk.length_copy,Walk.length_map,pm] using heven
    · simpa only [Walk.length_copy,Walk.length_map,pm] using hlen
  obtain ⟨p0,hp0,he0,hl0⟩ := hpath
  let pG : G.Walk v u := p0.mapLe (eraseEdge_le G u v)
  refine ⟨pG,hp0.mapLe _,?_,?_,?_⟩
  · simpa [pG] using he0
  · simpa [pG] using hl0
  · intro he
    have he0 : s(u,v) ∈ p0.edges := by simpa [pG] using he
    have hh := p0.edges_subset_edgeSet he0
    simp only [mem_edgeSet,eraseEdge,deleteEdges_adj,Set.mem_singleton_iff,not_true_eq_false,and_false] at hh

lemma even_alternative_of_common {G : SimpleGraph V} {u v x : V}
    (huv : G.Adj u v) (hux : G.Adj u x) (hvx : G.Adj v x) : ShortEvenAlternative G 2 u v := by
  let p : G.Walk v u := .cons hvx (.cons hux.symm .nil)
  refine ⟨p,?_,by dsimp [p]; decide,by simp [p],?_⟩
  · have hp1 : (Walk.cons hux.symm Walk.nil).IsPath :=
      Walk.IsPath.nil.cons (by simp [hux.ne.symm])
    exact hp1.cons (by simp [hvx.ne,huv.ne.symm])
  · simp [p,huv.ne,hux.ne,hvx.ne,huv.ne.symm]

lemma odd_cycle_of_even_alternative {G : SimpleGraph V} {q : ℕ} {u v : V}
    (huv : G.Adj u v) (hp : ShortEvenAlternative G q u v) :
    ∃ p : G.Walk u u, p.IsCycle ∧ Odd p.length ∧ p.length ≤ q+1 ∧ s(u,v) ∈ p.edges := by
  obtain ⟨p,hp,he,hl,hedge⟩ := hp
  refine ⟨.cons huv p,(Walk.cons_isCycle_iff p huv).mpr ⟨hp,hedge⟩,?_,?_,?_⟩
  · simpa only [Walk.length_cons] using he.add_one
  · simpa only [Walk.length_cons] using Nat.add_le_add_right hl 1
  · simp only [Walk.edges_cons,List.mem_cons,true_or]

/-- A backward increment greater than one forces EVERY host edge onto a
short odd cycle. The vertex-deletion preconnectedness condition on H is
explicit; no such conclusion is asserted for arbitrary H here. -/
theorem every_edge_on_short_odd_cycle [Fintype V] [Fintype W]
    {H : SimpleGraph W} (hH : H.IsBipartite) (hQ : 2 ≤ Fintype.card W)
    (hRest : ∀ w, (H.induce {w}ᶜ).Preconnected) {G : SimpleGraph V} (hf : H.Free G)
    (he : Nat.card G.edgeSet = extremalNumber (Fintype.card V) H)
    (hgap : (1 : ℝ) < (extremalNumber (Fintype.card V) H : ℝ)-
      (extremalNumber (Fintype.card V-1) H : ℝ)) {u v : V} (huv : G.Adj u v) :
    ∃ p : G.Walk u u, p.IsCycle ∧ Odd p.length ∧
      p.length ≤ Fintype.card W+1 ∧ s(u,v) ∈ p.edges := by
  classical
  apply odd_cycle_of_even_alternative huv
  by_cases hcommon : ∃ x, G.Adj u x ∧ G.Adj v x
  · obtain ⟨x,hux,hvx⟩ := hcommon
    obtain ⟨p,hp,he,hl,hn⟩ := even_alternative_of_common huv hux hvx
    exact ⟨p,hp,he,hl.trans hQ,hn⟩
  · haveI : IsEmpty (G.commonNeighbors u v) := ⟨by rintro ⟨x,hux,hvx⟩; exact hcommon ⟨x,hux,hvx⟩⟩
    apply even_alternative_of_contract hH hRest hf
    exact contract_contains_of_backward H G he hgap huv (by simp)

#print axioms even_alternative_of_contract
#print axioms every_edge_on_short_odd_cycle
end Erdos713ContractionOddCycles
