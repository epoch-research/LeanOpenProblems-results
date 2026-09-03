import Submission.TerminalPacking

/-!
Four-terminal sewing when each side consists of two vertex-disjoint paths.
Compatible pairings with arbitrary within-side intersections were treated in
TerminalPacking. No arbitrary four-terminal re-pairing is asserted here.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TerminalRouting
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 800000

lemma append_path_of_single_intersection {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ x, x ∈ p.support → x ∈ q.support → x = b) : (p.append q).IsPath := by
  have hb : b ∉ q.support.tail := by
    have hh := hq.support_nodup
    rw [Walk.support_eq_cons,List.nodup_cons] at hh
    exact hh.1
  rw [Walk.isPath_def,Walk.support_append,List.nodup_append']
  refine ⟨hp.support_nodup,hq.support_nodup.tail,?_⟩
  intro x hx hy
  exact hb ((hi x hx (List.mem_of_mem_tail hy)) ▸ hy)

/-- Crossed pairings form one simple cycle when the paths within each side
are vertex-disjoint and the only cross-side intersections are the terminals. -/
lemma crossed_strong_paths_cycle {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d) (r : G.Walk a c) (s : G.Walk b d)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) (hs : s.IsPath)
    (had : a ≠ d) (hpq : p.support.Disjoint q.support) (hrs : r.support.Disjoint s.support)
    (hcross : Disjoint (walkEdges p ∪ walkEdges q) (walkEdges r ∪ walkEdges s))
    (hi : (walkVerts p ∪ walkVerts q) ∩ (walkVerts r ∪ walkVerts s) ⊆ {a,b,c,d}) :
    ((p.append s).append (q.reverse.append r.reverse)).IsCycle := by
  have haq : a ∉ q.support := hpq p.start_mem_support
  have hbq : b ∉ q.support := hpq p.end_mem_support
  have hcp : c ∉ p.support := fun h => hpq h q.start_mem_support
  have hdp : d ∉ p.support := fun h => hpq h q.end_mem_support
  have has : a ∉ s.support := hrs r.start_mem_support
  have hcs : c ∉ s.support := hrs r.end_mem_support
  have hbr : b ∉ r.support := fun h => hrs h s.start_mem_support
  have hdr : d ∉ r.support := fun h => hrs h s.end_mem_support
  have hips : ∀ x, x ∈ p.support → x ∈ s.support → x = b := by
    intro x hx hy
    have hh := hi ⟨Or.inl hx,Or.inr hy⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl | rfl
    · exact (has hy).elim
    · rfl
    · exact (hcp hx).elim
    · exact (hdp hx).elim
  have hiqr : ∀ x, x ∈ q.reverse.support → x ∈ r.reverse.support → x = c := by
    intro x hx hy
    simp only [Walk.support_reverse,List.mem_reverse] at hx hy
    have hh := hi ⟨Or.inr hx,Or.inl hy⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl | rfl
    · exact (haq hx).elim
    · exact (hbq hx).elim
    · rfl
    · exact (hdr hy).elim
  have hP := append_path_of_single_intersection p s hp hs hips
  have hQ := append_path_of_single_intersection q.reverse r.reverse hq.reverse hr.reverse hiqr
  have hpsqr : ∀ x, x ∈ (p.append s).support → x ∈ (q.reverse.append r.reverse).support →
      x = a ∨ x = d := by
    intro x hx hy
    simp only [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (hpq hx hy).elim
    · have hh := hi ⟨Or.inl hx,Or.inl hy⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (hbr hy).elim
      · exact (hcp hx).elim
      · exact Or.inr rfl
    · have hh := hi ⟨Or.inr hy,Or.inr hx⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (hbq hy).elim
      · exact (hcs hx).elim
      · exact Or.inr rfl
    · exact (hrs hy hx).elim
  have hpqe : p.edges.Disjoint q.edges := by
    intro e he hf
    induction e using Sym2.ind with
    | h x y => exact hpq (p.fst_mem_support_of_mem_edges he) (q.fst_mem_support_of_mem_edges hf)
  have hrse : r.edges.Disjoint s.edges := by
    intro e he hf
    induction e using Sym2.ind with
    | h x y => exact hrs (r.fst_mem_support_of_mem_edges he) (s.fst_mem_support_of_mem_edges hf)
  have he : (p.append s).edges.Disjoint (q.reverse.append r.reverse).edges := by
    intro e hx hy
    simp only [Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_reverse] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hpqe hx hy
    · exact Set.disjoint_left.mp hcross (Or.inl hx) (Or.inl hy)
    · exact Set.disjoint_left.mp hcross (Or.inr hy) (Or.inr hx)
    · exact hrse hy hx
  exact TwoTerminalGluing.append_isCycle_of_paths _ _ hP hQ had he hpsqr

variable [Fintype V]

lemma packing_of_crossed_strong_paths {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d) (r : G.Walk a c) (s : G.Walk b d)
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) (hs : s.IsPath)
    (had : a ≠ d) (hpq : p.support.Disjoint q.support) (hrs : r.support.Disjoint s.support)
    (hcross : Disjoint (walkEdges p ∪ walkEdges q) (walkEdges r ∪ walkEdges s))
    (hi : (walkVerts p ∪ walkVerts q) ∩ (walkVerts r ∪ walkVerts s) ⊆ {a,b,c,d}) :
    ∃ P : Packing G,
      P.edges = (walkEdges p ∪ walkEdges q) ∪ (walkEdges r ∪ walkEdges s) ∧
      P.pieces.card ≤ 1 := by
  obtain ⟨P,hP,hcard⟩ := packing_of_cycle _
    (crossed_strong_paths_cycle p q r s hp hq hr hs had hpq hrs hcross hi)
  refine ⟨P,?_,hcard⟩
  rw [hP]
  ext e
  simp only [mem_walkEdges,Walk.edges_append,Walk.edges_reverse,List.mem_append,
    List.mem_reverse,Set.mem_union]
  tauto

end Erdos184.TerminalRouting
