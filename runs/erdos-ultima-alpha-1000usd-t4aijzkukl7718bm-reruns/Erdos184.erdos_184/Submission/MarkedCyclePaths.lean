import Submission.PathUnionRank

/-!
Cutting marked edges out of a simple cycle. In particular, two vertex-disjoint
marked edges in one cycle leave two vertex-disjoint paths. This is the strong
routing case needed for adaptive four-terminal parity correction.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.MarkedCyclePaths
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 400000

lemma walk_split_at_edge {u v a b : V} (p : G.Walk u v) (hab : G.Adj a b)
    (he : s(a,b) ∈ p.edges) :
    (∃ l : G.Walk u a, ∃ r : G.Walk b v, p = l.append (r.cons hab)) ∨
    (∃ l : G.Walk u b, ∃ r : G.Walk a v, p = l.append (r.cons hab.symm)) := by
  induction p with
  | nil => simp at he
  | @cons u w v huw p ih =>
    simp only [Walk.edges_cons,List.mem_cons] at he
    rcases he with he | he
    · rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · subst a; subst b
        exact Or.inl ⟨.nil,p,rfl⟩
      · subst a; subst b
        exact Or.inr ⟨.nil,p,rfl⟩
    · rcases ih he with ⟨l,r,hlr⟩ | ⟨l,r,hlr⟩
      · exact Or.inl ⟨l.cons huw,r,by rw [hlr]; rfl⟩
      · exact Or.inr ⟨l.cons huw,r,by rw [hlr]; rfl⟩

lemma cut_fields {u v a b : V} (l : G.Walk u a) (r : G.Walk b v)
    (hab : G.Adj a b) (hp : (l.append (r.cons hab)).IsPath) :
    l.IsPath ∧ r.IsPath ∧ l.support.Disjoint r.support ∧
      (∀ e, e ∈ l.edges ∨ e ∈ r.edges ↔
        e ∈ (l.append (r.cons hab)).edges ∧ e ≠ s(a,b)) := by
  have hpn := hp.support_nodup
  simp only [Walk.support_append,Walk.support_cons,List.tail_cons] at hpn
  have hparts := List.nodup_append'.mp hpn
  have hedges := hp.isTrail.edges_nodup
  simp only [Walk.edges_append,Walk.edges_cons,List.nodup_append',List.nodup_cons] at hedges
  refine ⟨hp.of_append_left,hp.of_append_right.of_cons,hparts.2.2,?_⟩
  intro e
  simp only [Walk.edges_append,Walk.edges_cons,List.mem_append,List.mem_cons]
  constructor
  · intro he
    refine ⟨by tauto,?_⟩
    intro heq
    subst e
    rcases he with hl | hr
    · exact hedges.2.2 hl (by simp)
    · exact hedges.2.1.1 hr
  · tauto

variable [Fintype V]

/-- Removing two distinct marked edges of a cycle leaves two paths with
pairwise disjoint vertex supports, in one of the two complementary pairings. -/
lemma cycle_remove_two_edges {a b c d : V} (H : G.Subgraph)
    (hc : H.coe.Connected) (hr : H.coe.IsRegularOfDegree 2)
    (hab : H.Adj a b) (hcd : H.Adj c d) (he : s(a,b) ≠ s(c,d)) :
    (∃ p : G.Walk b c, ∃ q : G.Walk d a,
      p.IsPath ∧ q.IsPath ∧ p.support.Disjoint q.support ∧
      (∀ e, e ∈ p.edges ∨ e ∈ q.edges ↔
        e ∈ H.edgeSet ∧ e ≠ s(a,b) ∧ e ≠ s(c,d)) ∧
      (∀ x ∈ p.support, x ∈ H.verts) ∧ (∀ x ∈ q.support, x ∈ H.verts)) ∨
    (∃ p : G.Walk b d, ∃ q : G.Walk c a,
      p.IsPath ∧ q.IsPath ∧ p.support.Disjoint q.support ∧
      (∀ e, e ∈ p.edges ∨ e ∈ q.edges ↔
        e ∈ H.edgeSet ∧ e ≠ s(a,b) ∧ e ≠ s(c,d)) ∧
      (∀ x ∈ p.support, x ∈ H.verts) ∧ (∀ x ∈ q.support, x ∈ H.verts)) := by
  obtain ⟨p,hp,hpe,hpv⟩ := TwoTerminalGluing.cycle_complementary_path H hc hr hab
  have hecd : s(c,d) ∈ p.edges := (hpe _).mpr ⟨hcd,he.symm⟩
  rcases walk_split_at_edge p hcd.adj_sub hecd with ⟨l,r,heq⟩ | ⟨l,r,heq⟩
  · have hf := cut_fields l r hcd.adj_sub (heq ▸ hp)
    refine Or.inl ⟨l,r,hf.1,hf.2.1,hf.2.2.1,?_,?_,?_⟩
    · intro e
      rw [hf.2.2.2,← heq,hpe]
      tauto
    · intro x hx
      apply hpv x
      rw [heq,Walk.support_append,Walk.support_cons,List.tail_cons,List.mem_append]
      exact Or.inl hx
    · intro x hx
      apply hpv x
      rw [heq,Walk.support_append,Walk.support_cons,List.tail_cons,List.mem_append]
      exact Or.inr hx
  · have hf := cut_fields l r hcd.adj_sub.symm (heq ▸ hp)
    refine Or.inr ⟨l,r,hf.1,hf.2.1,hf.2.2.1,?_,?_,?_⟩
    · intro e
      rw [hf.2.2.2,← heq,hpe]
      have hdc : s(d,c) = s(c,d) := Sym2.eq_swap
      rw [hdc]
      tauto
    · intro x hx
      apply hpv x
      rw [heq,Walk.support_append,Walk.support_cons,List.tail_cons,List.mem_append]
      exact Or.inl hx
    · intro x hx
      apply hpv x
      rw [heq,Walk.support_append,Walk.support_cons,List.tail_cons,List.mem_append]
      exact Or.inr hx

end Erdos184.MarkedCyclePaths
