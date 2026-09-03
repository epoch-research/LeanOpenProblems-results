import Submission.RigidityDegree

/-! Even subgraphs cannot stop inside a series path. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.PathSeries
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] {G T : SimpleGraph V}

lemma even_at_of_elsewhere (G : SimpleGraph V) (v : V)
    (h : ∀ w, w ≠ v → Even (G.degree w)) : Even (G.degree v) := by
  have hs : Even (∑ w, G.degree w) := by
    rw [G.sum_degrees_eq_twice_card_edges]
    exact even_two.mul_right _
  have hr : Even (∑ w ∈ Finset.univ.erase v, G.degree w) := by
    apply Finset.even_sum
    intro w hw
    exact h w (Finset.mem_erase.mp hw).1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)] at hs
  exact (Nat.even_add.mp hs).mp hr

lemma path_start_degree {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hn : ¬ p.Nil) :
    p.toSubgraph.spanningCoe.degree u = 1 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  change (p.toSubgraph.neighborSet u).ncard = 1
  rw [hp.neighborSet_toSubgraph_startpoint hn]
  simp

lemma even_path_subgraph_bot {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hT : T ≤ p.toSubgraph.spanningCoe) (he : ∀ x, Even (T.degree x)) : T = ⊥ := by
  induction p with
  | nil =>
    apply le_antisymm _ bot_le
    intro x y hxy
    have h := hT hxy
    simpa using h
  | @cons u w v huw p ih =>
    have hp' := (Walk.cons_isPath_iff huw p).mp hp
    have hdu : T.degree u = 0 := by
      have hlo := SimpleGraph.degree_le_of_le (v := u) hT
      have hhi := path_start_degree (.cons huw p) hp (by simp)
      have hv := Nat.even_iff.mp (he u)
      omega
    apply ih hp'.1 _
    intro x y hxy
    have hxyP : s(x,y) ∈ (Walk.cons huw p).edges :=
      (Walk.cons huw p).mem_edges_toSubgraph.mp (hT hxy)
    simp only [Walk.edges_cons,List.mem_cons] at hxyP
    rcases hxyP with heq | hxyP
    · have heu : u ∈ s(x,y) := heq ▸ (by simp : u ∈ s(u,w))
      rcases Sym2.mem_iff.mp heu with rfl | rfl
      · have hpos := (T.degree_pos_iff_exists_adj u).mpr ⟨y,hxy⟩
        omega
      · have hpos := (T.degree_pos_iff_exists_adj u).mpr ⟨x,hxy.symm⟩
        omega
    · exact p.mem_edges_toSubgraph.mpr hxyP

lemma path_internal_even {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (x : V) (hxu : x ≠ u) (hxv : x ≠ v) : Even (p.toSubgraph.spanningCoe.degree x) := by
  by_cases hx : x ∈ p.support
  · obtain ⟨i,hi,hil⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have hi0 : i ≠ 0 := by rintro rfl; exact hxu (by simpa using hi.symm)
    have hiL : i < p.length := by
      by_contra h
      have hi' : i = p.length := by omega
      exact hxv (by simpa [hi'] using hi.symm)
    have hd : p.toSubgraph.spanningCoe.degree x = 2 := by
      rw [← hi,← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hiL
    rw [hd]
    decide
  · have hd : p.toSubgraph.spanningCoe.degree x = 0 := by
      rw [SimpleGraph.degree_eq_zero_iff_notMem_support]
      rintro ⟨y,hxy⟩
      exact hx (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hxy))
    rw [hd]
    exact ⟨0,rfl⟩

lemma path_subgraph_all_or_none {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (huv : u ≠ v) (hT : T ≤ p.toSubgraph.spanningCoe)
    (he : ∀ x, x ≠ u → x ≠ v → Even (T.degree x)) :
    T = ⊥ ∨ T = p.toSubgraph.spanningCoe := by
  have hu : p.toSubgraph.spanningCoe.degree u = 1 := path_start_degree p hp (Walk.not_nil_of_ne huv)
  have zero_implies_bot (R : SimpleGraph V) (hR : R ≤ p.toSubgraph.spanningCoe)
      (hRu : R.degree u = 0)
      (hRe : ∀ x, x ≠ u → x ≠ v → Even (R.degree x)) : R = ⊥ := by
    have he' : ∀ x, x ≠ v → Even (R.degree x) := by
      intro x hxv
      by_cases hxu : x = u
      · subst x
        rw [hRu]
        exact ⟨0,rfl⟩
      · exact hRe x hxu hxv
    have hev := even_at_of_elsewhere R v he'
    apply even_path_subgraph_bot p hp hR
    intro x
    by_cases hx : x = v
    · exact hx ▸ hev
    · exact he' x hx
  by_cases hTu : T.degree u = 0
  · exact Or.inl (zero_implies_bot T hT hTu he)
  · right
    let R := p.toSubgraph.spanningCoe \ T
    have hR : R ≤ p.toSubgraph.spanningCoe := sdiff_le
    have hd := degree_sdiff_add p.toSubgraph.spanningCoe T hT u
    have hRu : R.degree u = 0 := by
      change R.degree u + T.degree u = p.toSubgraph.spanningCoe.degree u at hd
      omega
    have hRe (x : V) (hxu : x ≠ u) (hxv : x ≠ v) : Even (R.degree x) := by
      have hd := degree_sdiff_add p.toSubgraph.spanningCoe T hT x
      have heP := path_internal_even p hp x hxu hxv
      have heT := he x hxu hxv
      change R.degree x + T.degree x = p.toSubgraph.spanningCoe.degree x at hd
      rw [← hd] at heP
      exact (Nat.even_add.mp heP).mpr heT
    have hz := zero_implies_bot R hR (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hRu) (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hRe)
    apply le_antisymm hT
    intro x y hxy
    by_contra hn
    have hr : R.Adj x y := ⟨hxy,hn⟩
    rw [hz] at hr
    exact hr

#print axioms path_subgraph_all_or_none
end Erdos184Work.PathSeries
