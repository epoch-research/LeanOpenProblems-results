import FormalConjecturesUtil

/-! Local cycle recombination lemmas for Erdős Problem 184. -/

open SimpleGraph
namespace Erdos184Recombination

variable {V : Type*} {G : SimpleGraph V}

lemma path_start_not_mem_tail {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [p.support_eq_cons, List.nodup_cons] at h
  exact h.1

lemma append_isPath_of_support_inter {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.tail, List.disjoint_iff_ne.mp ?_⟩
  intro x hxp hxq
  have hxv := hinter x hxp (List.mem_of_mem_tail hxq)
  exact path_start_not_mem_tail hq (hxv ▸ hxq)

lemma append_isCycle_of_support_inter {u v : V} {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hedge : p.edges.Disjoint q.edges)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
    exact ⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup, List.disjoint_iff_ne.mp hedge⟩
  · intro hnil
    have hzero := congrArg Walk.length hnil
    simp only [Walk.length_append, Walk.length_nil] at hzero
    have hpzero : p.length = 0 := by omega
    exact huv (Walk.eq_of_length_eq_zero hpzero)
  · rw [Walk.tail_support_append, List.nodup_append]
    refine ⟨hp.support_nodup.tail, hq.support_nodup.tail, List.disjoint_iff_ne.mp ?_⟩
    intro x hxp hxq
    rcases hinter x (List.mem_of_mem_tail hxp) (List.mem_of_mem_tail hxq) with hx | hx
    · exact path_start_not_mem_tail hp (hx ▸ hxp)
    · exact path_start_not_mem_tail hq (hx ▸ hxq)

lemma triangle_paths_isCycle {u v w : V}
    {p : G.Walk u v} {q : G.Walk v w} {r : G.Walk w u}
    (hp : p.IsPath) (hq : q.IsPath) (hr : r.IsPath) (huw : u ≠ w)
    (hpq : ∀ x, x ∈ p.support → x ∈ q.support → x = v)
    (hqr : ∀ x, x ∈ q.support → x ∈ r.support → x = w)
    (hpr : ∀ x, x ∈ p.support → x ∈ r.support → x = u)
    (hpe : p.edges.Disjoint r.edges) (hqe : q.edges.Disjoint r.edges) :
    ((p.append q).append r).IsCycle := by
  apply append_isCycle_of_support_inter
    (append_isPath_of_support_inter hp hq hpq) hr huw
  · rw [Walk.edges_append]
    exact List.disjoint_append_left.mpr ⟨hpe, hqe⟩
  · intro x hx hxr
    rw [Walk.support_append, List.mem_append] at hx
    rcases hx with hxp | hxq
    · exact Or.inl (hpr x hxp hxr)
    · exact Or.inr (hqr x (List.mem_of_mem_tail hxq) hxr)

lemma cycle_dropUntil_isPath {u v : V} [DecidableEq V] {c : G.Walk u u}
    (hc : c.IsCycle) (hv : v ∈ c.support) (huv : u ≠ v) :
    (c.dropUntil v hv).IsPath := by
  have hc' : ((c.takeUntil v hv).append (c.dropUntil v hv)).IsCycle := by
    simpa only [Walk.take_spec] using hc
  exact hc'.isPath_of_append_right (Walk.not_nil_of_ne huv)

set_option maxHeartbeats 2000000 in
lemma three_cycle_ring_recombine {u v w : V}
    (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (c₁ : G.Walk u u) (c₂ : G.Walk v v) (c₃ : G.Walk w w)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) (hc₃ : c₃.IsCycle)
    (hv : v ∈ c₁.support) (hw : w ∈ c₂.support) (hu : u ∈ c₃.support)
    (hs₁₂ : ∀ x, x ∈ c₁.support → x ∈ c₂.support → x = v)
    (hs₂₃ : ∀ x, x ∈ c₂.support → x ∈ c₃.support → x = w)
    (hs₁₃ : ∀ x, x ∈ c₁.support → x ∈ c₃.support → x = u)
    (he₁₂ : c₁.edges.Disjoint c₂.edges)
    (he₂₃ : c₂.edges.Disjoint c₃.edges)
    (he₁₃ : c₁.edges.Disjoint c₃.edges) :
    ∃ a b : G.Walk u u, a.IsCycle ∧ b.IsCycle ∧ a.edges.Disjoint b.edges ∧
      ∀ e, (e ∈ a.edges ∨ e ∈ b.edges) ↔
        (e ∈ c₁.edges ∨ e ∈ c₂.edges ∨ e ∈ c₃.edges) := by
  classical
  let p₁ := c₁.takeUntil v hv
  let p₂ := (c₁.dropUntil v hv).reverse
  let q₁ := c₂.takeUntil w hw
  let q₂ := (c₂.dropUntil w hw).reverse
  let r₁ := c₃.takeUntil u hu
  let r₂ := (c₃.dropUntil u hu).reverse
  have hp₁ : p₁.IsPath := hc₁.isPath_takeUntil hv
  have hp₂ : p₂.IsPath := (cycle_dropUntil_isPath hc₁ hv huv).reverse
  have hq₁ : q₁.IsPath := hc₂.isPath_takeUntil hw
  have hq₂ : q₂.IsPath := (cycle_dropUntil_isPath hc₂ hw hvw).reverse
  have hr₁ : r₁.IsPath := hc₃.isPath_takeUntil hu
  have hr₂ : r₂.IsPath := (cycle_dropUntil_isPath hc₃ hu huw.symm).reverse
  have hsp₁ : p₁.support ⊆ c₁.support := c₁.support_takeUntil_subset hv
  have hsp₂ : p₂.support ⊆ c₁.support := by
    simpa only [p₂, Walk.support_reverse, List.reverse_subset] using c₁.support_dropUntil_subset hv
  have hsq₁ : q₁.support ⊆ c₂.support := c₂.support_takeUntil_subset hw
  have hsq₂ : q₂.support ⊆ c₂.support := by
    simpa only [q₂, Walk.support_reverse, List.reverse_subset] using c₂.support_dropUntil_subset hw
  have hsr₁ : r₁.support ⊆ c₃.support := c₃.support_takeUntil_subset hu
  have hsr₂ : r₂.support ⊆ c₃.support := by
    simpa only [r₂, Walk.support_reverse, List.reverse_subset] using c₃.support_dropUntil_subset hu
  have hep₁ : p₁.edges ⊆ c₁.edges := c₁.edges_takeUntil_subset hv
  have hep₂ : p₂.edges ⊆ c₁.edges := by
    simpa only [p₂, Walk.edges_reverse, List.reverse_subset] using c₁.edges_dropUntil_subset hv
  have heq₁ : q₁.edges ⊆ c₂.edges := c₂.edges_takeUntil_subset hw
  have heq₂ : q₂.edges ⊆ c₂.edges := by
    simpa only [q₂, Walk.edges_reverse, List.reverse_subset] using c₂.edges_dropUntil_subset hw
  have her₁ : r₁.edges ⊆ c₃.edges := c₃.edges_takeUntil_subset hu
  have her₂ : r₂.edges ⊆ c₃.edges := by
    simpa only [r₂, Walk.edges_reverse, List.reverse_subset] using c₃.edges_dropUntil_subset hu
  let a := (p₁.append q₁).append r₁
  let b := (p₂.append q₂).append r₂
  have ha : a.IsCycle := triangle_paths_isCycle hp₁ hq₁ hr₁ huw
    (fun x hx hy => hs₁₂ x (hsp₁ hx) (hsq₁ hy))
    (fun x hx hy => hs₂₃ x (hsq₁ hx) (hsr₁ hy))
    (fun x hx hy => hs₁₃ x (hsp₁ hx) (hsr₁ hy))
    (fun e he hf => he₁₃ (hep₁ he) (her₁ hf))
    (fun e he hf => he₂₃ (heq₁ he) (her₁ hf))
  have hb : b.IsCycle := triangle_paths_isCycle hp₂ hq₂ hr₂ huw
    (fun x hx hy => hs₁₂ x (hsp₂ hx) (hsq₂ hy))
    (fun x hx hy => hs₂₃ x (hsq₂ hx) (hsr₂ hy))
    (fun x hx hy => hs₁₃ x (hsp₂ hx) (hsr₂ hy))
    (fun e he hf => he₁₃ (hep₂ he) (her₂ hf))
    (fun e he hf => he₂₃ (heq₂ he) (her₂ hf))
  have hdp : p₁.edges.Disjoint p₂.edges := by
    simpa only [p₁, p₂, Walk.edges_reverse, List.disjoint_reverse_right] using
      hc₁.isTrail.disjoint_edges_takeUntil_dropUntil hv
  have hdq : q₁.edges.Disjoint q₂.edges := by
    simpa only [q₁, q₂, Walk.edges_reverse, List.disjoint_reverse_right] using
      hc₂.isTrail.disjoint_edges_takeUntil_dropUntil hw
  have hdr : r₁.edges.Disjoint r₂.edges := by
    simpa only [r₁, r₂, Walk.edges_reverse, List.disjoint_reverse_right] using
      hc₃.isTrail.disjoint_edges_takeUntil_dropUntil hu
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · intro e hae hbe
    simp only [a, b, Walk.edges_append, List.mem_append] at hae hbe
    rcases hae with (hpe | hqe) | hre <;>
      rcases hbe with (hpe' | hqe') | hre'
    · exact hdp hpe hpe'
    · exact he₁₂ (hep₁ hpe) (heq₂ hqe')
    · exact he₁₃ (hep₁ hpe) (her₂ hre')
    · exact he₁₂ (hep₂ hpe') (heq₁ hqe)
    · exact hdq hqe hqe'
    · exact he₂₃ (heq₁ hqe) (her₂ hre')
    · exact he₁₃ (hep₂ hpe') (her₁ hre)
    · exact he₂₃ (heq₂ hqe') (her₁ hre)
    · exact hdr hre hre'
  · intro e
    have hcp : (e ∈ p₁.edges ∨ e ∈ p₂.edges) ↔ e ∈ c₁.edges := by
      simp only [p₁, p₂, Walk.edges_reverse, List.mem_reverse]
      rw [← List.mem_append, ← Walk.edges_append, Walk.take_spec]
    have hcq : (e ∈ q₁.edges ∨ e ∈ q₂.edges) ↔ e ∈ c₂.edges := by
      simp only [q₁, q₂, Walk.edges_reverse, List.mem_reverse]
      rw [← List.mem_append, ← Walk.edges_append, Walk.take_spec]
    have hcr : (e ∈ r₁.edges ∨ e ∈ r₂.edges) ↔ e ∈ c₃.edges := by
      simp only [r₁, r₂, Walk.edges_reverse, List.mem_reverse]
      rw [← List.mem_append, ← Walk.edges_append, Walk.take_spec]
    simp only [a, b, Walk.edges_append, List.mem_append]
    tauto

#print axioms three_cycle_ring_recombine

#print axioms triangle_paths_isCycle
end Erdos184Recombination
