import Submission.OddPathExtraction

/-! A local cycle-absorption move for two vertex-disjoint endpoint paths.
No claim is made that such paths always exist in an all-odd graph. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.Absorption
variable {V : Type*} {G : SimpleGraph V} {a b u v z : V}
set_option maxHeartbeats 400000

lemma join_isPath (p : G.Walk a u) (q : G.Walk v b)
    (hp : p.IsPath) (hq : q.IsPath) (huv : G.Adj u v)
    (hdis : p.support.Disjoint q.support) : ((p.concat huv).append q).IsPath := by
  have hvp : v ∉ p.support := fun hv => hdis hv q.start_mem_support
  have hp' := hp.concat hvp huv
  apply append_isPath_of_support_inter hp' hq
  intro x hx hqx
  simp only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] at hx
  exact hx.elim (fun hpx => (hdis hpx hqx).elim) id

/-- A residual cycle containing an edge between endpoints of two vertex-disjoint
paths can be absorbed. Join the old paths through that edge, and use the rest
of the cycle as the other new path. The four endpoints are retained. -/
lemma absorb_cons (p : G.Walk a u) (q : G.Walk v b) (c : G.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath) (huv : G.Adj u v)
    (hc : (Walk.cons huv c).IsCycle)
    (hdis : p.support.Disjoint q.support)
    (hpc : p.edges.Disjoint c.edges) (hqc : q.edges.Disjoint c.edges) :
    ∃ r : G.Walk a b,
      r.IsPath ∧ c.IsPath ∧ a ≠ b ∧ v ≠ u ∧ r.edges.Disjoint c.edges ∧
      (r.edges ++ c.edges).Perm (p.edges ++ q.edges ++ (Walk.cons huv c).edges) := by
  let r := (p.concat huv).append q
  have hce := (Walk.cons_isCycle_iff c huv).mp hc
  have hab : a ≠ b := by
    intro he
    exact hdis p.start_mem_support (he ▸ q.end_mem_support)
  refine ⟨r,join_isPath p q hp hq huv hdis,hce.1,hab,huv.ne.symm,?_,?_⟩
  · intro e her hec
    simp only [r,Walk.edges_append,Walk.edges_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] at her
    rcases her with (hep | he) | heq
    · exact hpc hep hec
    · subst e
      exact hce.2 hec
    · exact hqc heq hec
  · apply List.perm_iff_count.mpr
    intro e
    simp only [r,Walk.edges_append,Walk.edges_concat,List.concat_eq_append,Walk.edges_cons,
      List.count_append,List.count_cons,List.count_nil]
    omega

lemma absorb_cycle_at_edge (p : G.Walk a u) (q : G.Walk v b) (c : G.Walk z z)
    (hp : p.IsPath) (hq : q.IsPath) (hc : c.IsCycle)
    (huv : G.Adj u v) (he : s(u,v) ∈ c.edges)
    (hdis : p.support.Disjoint q.support)
    (hpc : p.edges.Disjoint c.edges) (hqc : q.edges.Disjoint c.edges) :
    ∃ (r : G.Walk a b) (s : G.Walk v u),
      r.IsPath ∧ s.IsPath ∧ a ≠ b ∧ v ≠ u ∧ r.edges.Disjoint s.edges ∧
      (r.edges ++ s.edges).Perm (p.edges ++ q.edges ++ c.edges) := by
  obtain ⟨s,hs,hperm⟩ := CertificateStructure.cycle_edge_cons c hc huv he
  have hp' : p.edges.Disjoint s.edges := by
    intro e hep hes
    exact hpc hep (hperm.mem_iff.mp (List.mem_cons_of_mem _ hes))
  have hq' : q.edges.Disjoint s.edges := by
    intro e heq hes
    exact hqc heq (hperm.mem_iff.mp (List.mem_cons_of_mem _ hes))
  obtain ⟨r,hr,hs',hab,hvu,hrs,hcov⟩ := absorb_cons p q s hp hq huv hs hdis hp' hq'
  refine ⟨r,s,hr,hs',hab,hvu,hrs,hcov.trans ?_⟩
  exact (List.Perm.refl (p.edges ++ q.edges)).append hperm

#print axioms join_isPath

/-- A second absorption move. One path meets the cycle only at `u`; the other
starts at its neighbor `v` and avoids `u`. The old paths may intersect outside
the cycle. -/
lemma absorb_clean_cons (p : G.Walk a u) (q : G.Walk v b) (c : G.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath) (huv : G.Adj u v)
    (hc : (Walk.cons huv c).IsCycle)
    (hclean : ∀ x, x ∈ p.support → x ∈ c.support → x = u)
    (huq : u ∉ q.support)
    (hpq : p.edges.Disjoint q.edges)
    (hpc : p.edges.Disjoint c.edges) (hqc : q.edges.Disjoint c.edges) :
    ∃ (r : G.Walk u b) (s : G.Walk v a),
      r.IsPath ∧ s.IsPath ∧ u ≠ b ∧ v ≠ a ∧ r.edges.Disjoint s.edges ∧
      (r.edges ++ s.edges).Perm (p.edges ++ q.edges ++ (Walk.cons huv c).edges) := by
  let r := Walk.cons huv q
  let s := c.append p.reverse
  have hce := (Walk.cons_isCycle_iff c huv).mp hc
  have hr : r.IsPath := (Walk.cons_isPath_iff huv q).mpr ⟨hq,huq⟩
  have hs : s.IsPath := by
    apply append_isPath_of_support_inter hce.1 hp.reverse
    intro x hxc hxp
    exact hclean x (by simpa only [Walk.support_reverse,List.mem_reverse] using hxp) hxc
  have hub : u ≠ b := fun h => huq (h ▸ q.end_mem_support)
  have hva : v ≠ a := by
    intro h
    have hvp : v ∈ p.support := h ▸ p.start_mem_support
    exact huv.ne.symm (hclean v hvp c.start_mem_support)
  have huep : s(u,v) ∉ p.edges := by
    intro he
    exact huv.ne.symm (hclean v (p.snd_mem_support_of_mem_edges he) c.start_mem_support)
  refine ⟨r,s,hr,hs,hub,hva,?_,?_⟩
  · intro e her hes
    simp only [r,Walk.edges_cons,List.mem_cons] at her
    simp only [s,Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_reverse] at hes
    rcases her with he | heq
    · subst e
      exact hes.elim hce.2 huep
    · exact hes.elim (hqc heq) (fun hep => hpq hep heq)
  · apply List.perm_iff_count.mpr
    intro e
    simp only [r,s,Walk.edges_cons,Walk.edges_append,Walk.edges_reverse,
      List.count_append,List.count_cons,List.count_reverse]
    omega

#print axioms absorb_clean_cons

#print axioms absorb_cons
#print axioms absorb_cycle_at_edge
end Erdos184Work.OddPaths.Absorption
