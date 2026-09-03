import Submission.Work

/-! Suppression of a degree-two vertex in a smallest-order failure.
The two-neighbor edge may be added only once; the triangular case has an
explicit extra path cost rather than an unjustified zero-cost lifting. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
namespace Erdos583DegreeTwoReductionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

noncomputable def bypass {V : Type*} (G : SimpleGraph V) (u a b : V) : SimpleGraph V :=
  within G ({u}ᶜ : Set V) ⊔ fromEdgeSet {s(a,b)}

lemma bypass_not_adj_root {V : Type*} {G : SimpleGraph V} {u a b x : V}
    (ha : G.Adj u a) (hb : G.Adj u b) : ¬(bypass G u a b).Adj u x := by
  rintro (hx|hx)
  · exact hx.2.1 rfl
  · obtain ⟨he,_⟩ := hx
    rcases Sym2.eq_iff.mp he with ⟨he,_⟩|⟨he,_⟩
    · exact ha.ne he
    · exact hb.ne he

lemma bypass_within {V : Type*} {G : SimpleGraph V} {u a b : V}
    (ha : G.Adj u a) (hb : G.Adj u b) :
    within (bypass G u a b) ({u}ᶜ : Set V)=bypass G u a b := by
  ext x y
  constructor
  · exact And.left
  · intro hxy
    refine ⟨hxy,?_,?_⟩
    · rintro rfl
      exact bypass_not_adj_root ha hb hxy
    · rintro rfl
      exact bypass_not_adj_root ha hb hxy.symm

lemma bypass_connected {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {u a b : V} (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b)
    (hN : ∀ x, G.Adj u x → x=a ∨ x=b) :
    ((bypass G u a b).induce ({u}ᶜ : Set V)).Connected := by
  classical
  let J := bypass G u a b
  let S : Set V := {u}ᶜ
  let f : V → S := fun x ↦ if hx : x=u then ⟨a,ha.ne.symm⟩ else ⟨x,hx⟩
  have hjab : J.Adj a b := Or.inr ⟨rfl,hab⟩
  have hf : ∀ x y, G.Adj x y → (J.induce S).Reachable (f x) (f y) := by
    intro x y hxy
    by_cases hx : x=u
    · subst x
      rcases hN y hxy with rfl|rfl
      · simp only [f,dif_pos rfl,dif_neg ha.ne.symm]
        exact Reachable.rfl
      · apply Adj.reachable
        simpa [f,ha.ne.symm,hb.ne.symm] using hjab
    · by_cases hy : y=u
      · subst y
        rcases hN x hxy.symm with rfl|rfl
        · simp only [f,dif_pos rfl,dif_neg ha.ne.symm]
          exact Reachable.rfl
        · apply Adj.reachable
          simpa [f,ha.ne.symm,hb.ne.symm] using hjab.symm
      · apply Adj.reachable
        change J.Adj (f x).val (f y).val
        simp only [f,dif_neg hx,dif_neg hy]
        exact Or.inl ⟨hxy,hx,hy⟩
  have hfx (x : S) : f x.val=x := by
    apply Subtype.ext
    have hx : x.val ≠ u := x.property
    simp [f,hx]
  letI : Nonempty S := ⟨⟨a,ha.ne.symm⟩⟩
  refine ⟨fun x y ↦ ?_⟩
  have hh := reachable_map_to_reachable f hf (hG.preconnected x.val y.val)
  simpa only [hfx] using hh

lemma bypass_edgeSet {V : Type*} (G : SimpleGraph V) (u a b : V) (hab : a ≠ b) :
    (bypass G u a b).edgeSet=(within G ({u}ᶜ : Set V)).edgeSet ∪ {s(a,b)} := by
  rw [bypass,edgeSet_sup,edgeSet_fromEdgeSet]
  congr 1
  apply Set.Subset.antisymm Set.diff_subset
  intro e he
  refine ⟨he,?_⟩
  intro hd
  obtain rfl := Set.mem_singleton_iff.mp he
  exact hab (Sym2.mem_diagSet_iff_eq.mp hd)

lemma bypass_triangle {V : Type*} {G : SimpleGraph V} {u a b : V}
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : G.Adj a b) :
    bypass G u a b=within G ({u}ᶜ : Set V) := by
  apply sup_eq_left.mpr
  intro x y hxy
  obtain ⟨he,_⟩ := hxy
  rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨hab,ha.ne.symm,hb.ne.symm⟩
  · exact ⟨hab.symm,hb.ne.symm,ha.ne.symm⟩

lemma delete_two_path {V : Type*} {G : SimpleGraph V} {u a b : V}
    (ha : G.Adj u a) (hb : G.Adj u b)
    (hN : ∀ x, G.Adj u x → x=a ∨ x=b) :
    G.deleteEdges (Walk.cons ha.symm (Walk.cons hb Walk.nil)).toSubgraph.edgeSet=
      within G ({u}ᶜ : Set V) := by
  ext x y
  simp only [deleteEdges_adj,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
    List.mem_cons,List.not_mem_nil,or_false,within,Set.mem_compl_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hxy,hn⟩
    refine ⟨hxy,?_,?_⟩
    · rintro rfl
      rcases hN y hxy with rfl|rfl
      · exact hn (Or.inl Sym2.eq_swap)
      · exact hn (Or.inr rfl)
    · rintro rfl
      rcases hN x hxy.symm with rfl|rfl
      · exact hn (Or.inl rfl)
      · exact hn (Or.inr Sym2.eq_swap)
  · rintro ⟨hxy,hxu,hyu⟩
    refine ⟨hxy,?_⟩
    rintro (he|he) <;> rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hyu rfl
    · exact hxu rfl
    · exact hxu rfl
    · exact hyu rfl

lemma restore_bypass {V : Type*} [Fintype V] {G : SimpleGraph V} {u a b : V}
    (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b)
    (hN : ∀ x, G.Adj u x → x=a ∨ x=b)
    (D : Finset ((bypass G u a b).induce ({u}ᶜ : Set V)).Subgraph)
    (hD : GoodDecomposition ((bypass G u a b).induce ({u}ᶜ : Set V)) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ D.card+(if G.Adj a b then 1 else 0) := by
  classical
  let r : G.Walk a b := Walk.cons ha.symm (Walk.cons hb Walk.nil)
  have hr : r.IsPath := by simp [r,Walk.cons_isPath_iff,ha.ne.symm,hb.ne,hab]
  have hdel : G.deleteEdges r.toSubgraph.edgeSet=within G ({u}ᶜ : Set V) := delete_two_path ha hb hN
  generalize hk : D.card=k
  have hex : ∃ E : Finset (within (bypass G u a b) ({u}ᶜ : Set V)).Subgraph,
      GoodDecomposition (within (bypass G u a b) ({u}ᶜ : Set V)) E ∧ E.card ≤ k := by
    simpa only [hk] using lift_induce_within ({u}ᶜ : Set V) D hD
  rw [bypass_within ha hb] at hex
  by_cases habG : G.Adj a b
  · rw [bypass_triangle ha hb habG,←hdel] at hex
    obtain ⟨D',hD',hDc⟩ := hex
    obtain ⟨E,hE,hEc⟩ := restore_path_subgraph (show IsPathSubgraph r.toSubgraph from ⟨_,_,r,hr,rfl⟩) hD'
    exact ⟨E,hE,by simp only [if_pos habG]; omega⟩
  · obtain ⟨D',hD',hDc⟩ := hex
    have hcover : G.edgeSet=((bypass G u a b).edgeSet \ {s(a,b)}) ∪ r.toSubgraph.edgeSet := by
      have hn : s(a,b) ∉ (within G ({u}ᶜ : Set V)).edgeSet := fun hh ↦ habG hh.1
      rw [bypass_edgeSet G u a b hab,Set.union_diff_distrib,Set.diff_self,Set.union_empty,
        Set.diff_singleton_eq_self hn,←hdel,edgeSet_deleteEdges]
      exact (Set.diff_union_of_subset r.toSubgraph.edgeSet_subset).symm
    have hfresh : ∀ x ∈ r.support, x ≠ a → x ≠ b → x ∉ (bypass G u a b).support := by
      intro x hx hxa hxb hxJ
      have hxU : x=u := by simpa [r,Walk.support,hxa,hxb] using hx
      subst x
      obtain ⟨y,hy⟩ := (mem_support _).mp hxJ
      exact bypass_not_adj_root ha hb hy
    obtain ⟨E,hE,hEc⟩ := hD'.expand_edge (show (bypass G u a b).Adj a b from Or.inr ⟨rfl,hab⟩)
      r hr hfresh hcover
    exact ⟨E,hE,by simp only [if_neg habG,add_zero]; omega⟩

lemma degree_two_configuration {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u a b : Fin n} (ha : G.Adj u a) (hb : G.Adj u b) (hab : a ≠ b)
    (hN : ∀ x, G.Adj u x → x=a ∨ x=b) : Even n ∧ G.Adj a b := by
  classical
  have hc : ({u}ᶜ : Set (Fin n)).ncard=n-1 := by
    rw [Set.ncard_compl,Set.ncard_singleton,Nat.card_eq_fintype_card,Fintype.card_fin]
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce (bypass G u a b) ({u}ᶜ : Set (Fin n))
    (by rw [hc]; have := Fin.pos u; omega) (bypass_connected hG ha hb hab hN)
  obtain ⟨E,hE,hEc⟩ := restore_bypass ha hb hab hN D hD
  rw [hc,ceil_half] at hDc
  have habG : G.Adj a b := by
    by_contra hn
    simp only [if_neg hn,add_zero] at hEc
    exact hfail ⟨E,hE,by simp only [Fintype.card_fin,ceil_half]; omega⟩
  refine ⟨?_,habG⟩
  apply Nat.not_odd_iff_even.mp
  rintro ⟨k,hk⟩
  simp only [if_pos habG] at hEc
  exact hfail ⟨E,hE,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma degree_two_triangle {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u : Fin n} (hdegree : Nat.card (G.neighborSet u)=2) :
    Even n ∧ ∃ a b, a ≠ b ∧ G.neighborSet u={a,b} ∧ G.Adj a b := by
  rw [Nat.card_coe_set_eq] at hdegree
  obtain ⟨a,b,hab,heq⟩ := Set.ncard_eq_two.mp hdegree
  have ha : G.Adj u a := by change a ∈ G.neighborSet u; rw [heq]; exact Or.inl rfl
  have hb : G.Adj u b := by change b ∈ G.neighborSet u; rw [heq]; exact Or.inr rfl
  have hN : ∀ x, G.Adj u x → x=a ∨ x=b := by intro x hx; change x ∈ G.neighborSet u at hx; simpa only [heq,Set.mem_insert_iff,Set.mem_singleton_iff] using hx
  obtain ⟨hn,hG⟩ := degree_two_configuration hsmall hG hfail ha hb hab hN
  exact ⟨hn,a,b,hab,heq,hG⟩

lemma no_degree_two_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    Nat.card (G.neighborSet u) ≠ 2 := by
  intro hdegree
  exact Nat.not_even_iff_odd.mpr hn (degree_two_triangle hsmall hG hfail hdegree).1

lemma min_degree_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    3 ≤ Nat.card (G.neighborSet u) := by
  classical
  obtain ⟨v,w,hvw,_,_⟩ := EdgeDefect.failure_has_even_nonbridge G hfail
  letI : Nontrivial (Fin n) := ⟨⟨w,v,hvw.ne⟩⟩
  have hpos : 0 < Nat.card (G.neighborSet u) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hG.preconnected.degree_pos_of_nontrivial u
  have h1 := LeafReduction.no_leaf_of_odd_failure hsmall hn hG hfail u
  have h2 := no_degree_two_of_odd_failure hsmall hn hG hfail u
  omega

end Erdos583DegreeTwoReductionDevelopment
