import Submission.CycleRing

/-! Shortest-cycle facts used to extract clean incidence rings. -/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace ShortestCycle
variable {V : Type*} {G : SimpleGraph V}

lemma girth_le_path_add_one {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hvu : G.Adj v u) (he : s(u,v) ∉ p.edges) : G.girth ≤ p.length + 1 := by
  have hc : (Walk.cons hvu p).IsCycle := by
    apply (Walk.cons_isCycle_iff _ _).mpr
    exact ⟨hp, by simpa only [Sym2.eq_swap] using he⟩
  simpa only [Walk.length_cons] using SimpleGraph.girth_le_length hc

lemma girth_le_path_add_two {u v x : V} (p : G.Walk u v) (hp : p.IsPath)
    (hxu : G.Adj x u) (hvx : G.Adj v x) (hne : u ≠ v) (hx : x ∉ p.support) :
    G.girth ≤ p.length + 2 := by
  have hpath : (p.concat hvx).IsPath := by
    rw [Walk.isPath_def, Walk.support_concat]
    exact hp.support_nodup.concat hx
  have he : s(u,x) ∉ (p.concat hvx).edges := by
    simp only [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton]
    rintro (he | he)
    · exact hx (p.snd_mem_support_of_mem_edges he)
    · have huv : u = v := by
        rcases Sym2.eq_iff.mp he with h | h
        · exact h.1
        · exact (hx (h.1 ▸ p.start_mem_support)).elim
      exact hne huv
  have h := girth_le_path_add_one (p.concat hvx) hpath hxu (by
    simpa only [Sym2.eq_swap] using he)
  simpa only [Walk.length_concat, Nat.add_assoc] using h

/-- A shortest cycle has no chord. -/
lemma isInduced {a : V} (p : G.Walk a a) (hp : p.IsCycle) (hg : G.girth = p.length) :
    p.toSubgraph.IsInduced := by
  intro u hu v hv huv
  by_contra he
  have hu' := p.mem_verts_toSubgraph.mp hu
  let c := p.rotate hu'
  have hc : c.IsCycle := hp.rotate hu'
  have hcsub : c.toSubgraph = p.toSubgraph := by simp [c]
  have hv' : v ∈ c.support := by
    apply c.mem_verts_toSubgraph.mp
    rwa [hcsub]
  let q := c.takeUntil v hv'
  let r := (c.dropUntil v hv').reverse
  have hq : q.IsPath := hc.isPath_takeUntil hv'
  have hr : r.IsPath := by
    apply Walk.IsPath.reverse
    apply Walk.IsCycle.isPath_of_append_right (p := q) (Walk.not_nil_of_ne huv.ne)
    simpa only [q, Walk.take_spec] using hc
  have hec : s(u,v) ∉ c.edges := by
    intro h
    exact he (by rw [← hcsub]; exact c.mem_edges_toSubgraph.mpr h)
  have hqe : s(u,v) ∉ q.edges := fun h => hec (c.edges_takeUntil_subset hv' h)
  have hre : s(u,v) ∉ r.edges := by
    intro h
    exact hec (c.edges_dropUntil_subset hv' (by simpa only [r, Walk.edges_reverse, List.mem_reverse] using h))
  have hlen : q.length + r.length = c.length := by
    simpa only [q, r, Walk.length_append, Walk.length_reverse] using
      congrArg Walk.length (c.take_spec hv')
  have h₁ := girth_le_path_add_one q hq huv.symm hqe
  have h₂ := girth_le_path_add_one r hr huv.symm hre
  have hl : c.length = p.length := by
    simpa only [Walk.length_edges] using (p.rotate_edges hu').perm.length_eq
  have h3 := hp.three_le_length
  omega

/-- When a shortest cycle has length at least five, an outside vertex
cannot have two distinct neighbors on it. -/
lemma common_neighbor_mem_support {a u v x : V} (p : G.Walk a a)
    (hp : p.IsCycle) (hg : G.girth = p.length) (hlower : 5 ≤ p.length)
    (hu : u ∈ p.support) (hv : v ∈ p.support) (hne : u ≠ v)
    (hux : G.Adj u x) (hvx : G.Adj v x) : x ∈ p.support := by
  by_contra hx
  let c := p.rotate hu
  have hc : c.IsCycle := hp.rotate hu
  have hcsub : c.toSubgraph = p.toSubgraph := by simp [c]
  have hv' : v ∈ c.support := by
    apply c.mem_verts_toSubgraph.mp
    rw [hcsub]
    exact p.mem_verts_toSubgraph.mpr hv
  have hx' : x ∉ c.support := by
    intro h
    apply hx
    apply p.mem_verts_toSubgraph.mp
    rw [← hcsub]
    exact c.mem_verts_toSubgraph.mpr h
  let q := c.takeUntil v hv'
  let r := (c.dropUntil v hv').reverse
  have hq : q.IsPath := hc.isPath_takeUntil hv'
  have hr : r.IsPath := by
    apply Walk.IsPath.reverse
    apply Walk.IsCycle.isPath_of_append_right (p := q) (Walk.not_nil_of_ne hne)
    simpa only [q, Walk.take_spec] using hc
  have hxq : x ∉ q.support := fun h => hx' (c.support_takeUntil_subset hv' h)
  have hxr : x ∉ r.support := by
    intro h
    exact hx' (c.support_dropUntil_subset hv' (by
      simpa only [r, Walk.support_reverse, List.mem_reverse] using h))
  have hlen : q.length + r.length = c.length := by
    simpa only [q, r, Walk.length_append, Walk.length_reverse] using
      congrArg Walk.length (c.take_spec hv')
  have h₁ := girth_le_path_add_two q hq hux.symm hvx hne hxq
  have h₂ := girth_le_path_add_two r hr hux.symm hvx hne hxr
  have hl : c.length = p.length := by
    simpa only [Walk.length_edges] using (p.rotate_edges hu).perm.length_eq
  omega

end ShortestCycle
end Erdos184
