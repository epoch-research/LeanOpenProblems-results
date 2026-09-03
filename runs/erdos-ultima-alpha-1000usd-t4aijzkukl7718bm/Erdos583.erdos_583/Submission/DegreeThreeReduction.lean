import Submission.Work

/-! Low-degree vertex deletion in a bridgeless graph, and a degree-three
restoration using an endpoint forced by parity. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
namespace Erdos583DegreeThreeReductionDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma within_walk_support {V : Type*} {G : SimpleGraph V} {S : Set V}
    {x y : V} (p : (within G S).Walk x y) (hx : x ∈ S) :
    ∀ z ∈ p.support, z ∈ S := by
  induction p with
  | nil => simpa using hx
  | @cons x w y h p ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact hx
    · exact ih h.2.2 z hz

lemma within_reachable_induce {V : Type*} {G : SimpleGraph V} {S : Set V}
    (x y : S) (h : (within G S).Reachable x.val y.val) : (G.induce S).Reachable x y := by
  obtain ⟨p⟩ := h
  let q := p.mapLe (within_le G S)
  have hs : ∀ z ∈ q.support, z ∈ S := by
    simpa only [q,Walk.support_mapLe_eq_support] using within_walk_support p x.property
  exact ⟨q.induce S hs⟩

/-- A nonbridge incident edge links its neighbor to a different neighbor
without visiting the deleted vertex. -/
lemma nonbridge_neighbor_link {V : Type*} {G : SimpleGraph V} {u a : V}
    (ha : G.Adj u a) (hnb : ¬G.IsBridge s(u,a)) :
    ∃ b, G.Adj u b ∧ b ≠ a ∧ (within G ({u}ᶜ : Set V)).Reachable a b := by
  have hr : (G.deleteEdges {s(u,a)}).Reachable u a := by
    by_contra hn
    exact hnb (isBridge_iff.mpr ⟨ha,hn⟩)
  obtain ⟨p,hp⟩ := hr.exists_isPath
  cases p with
  | nil => exact (ha.ne rfl).elim
  | @cons _ b _ hb q =>
    have hbG : G.Adj u b := G.deleteEdges_le _ hb
    have hba : b ≠ a := by
      rintro rfl
      exact (deleteEdges_adj.mp hb).2 rfl
    have hn := (Walk.cons_isPath_iff hb q).mp hp |>.2
    have hedge : ∀ e ∈ q.edges, e ∈ (within G ({u}ᶜ : Set V)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        have hxy : q.toSubgraph.Adj x y := q.mem_edges_toSubgraph.mpr he
        refine ⟨G.deleteEdges_le _ (q.toSubgraph.adj_sub hxy),?_,?_⟩
        · rintro rfl
          exact hn (Walk.mem_support_of_adj_toSubgraph hxy)
        · rintro rfl
          exact hn (Walk.mem_support_of_adj_toSubgraph hxy.symm)
    exact ⟨b,hbG,hba,(q.transfer _ hedge).reachable.symm⟩

lemma neighbors_reachable_of_degree_le_three {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u : V} (hdeg : Nat.card (G.neighborSet u) ≤ 3)
    (hnb : ∀ x, G.Adj u x → ¬G.IsBridge s(u,x))
    {a b : V} (ha : G.Adj u a) (hb : G.Adj u b) :
    (within G ({u}ᶜ : Set V)).Reachable a b := by
  classical
  by_cases hab : a=b
  · subst b; exact Reachable.rfl
  obtain ⟨c,hc,hca,hac⟩ := nonbridge_neighbor_link ha (hnb a ha)
  obtain ⟨d,hd,hdb,hbd⟩ := nonbridge_neighbor_link hb (hnb b hb)
  by_cases hcb : c=b
  · simpa only [hcb] using hac
  by_cases hda : d=a
  · simpa only [hda] using hbd.symm
  by_cases hcd : c=d
  · exact hac.trans (hcd ▸ hbd.symm)
  have hsub : ({a,b,c,d} : Finset V) ⊆ G.neighborFinset u := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rw [mem_neighborFinset]
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  have hc4 : ({a,b,c,d} : Finset V).card=4 := by
    simp [hab,hca.symm,Ne.symm hcb,Ne.symm hda,hdb.symm,hcd]
  have hh := Finset.card_le_card hsub
  rw [hc4,card_neighborFinset_eq_degree] at hh
  have hh' : 4 ≤ Nat.card (G.neighborSet u) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hh
  omega

lemma delete_vertex_connected_of_neighbor_links {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {u a : V} (ha : G.Adj u a)
    (hlinks : ∀ b, G.Adj u b → (within G ({u}ᶜ : Set V)).Reachable a b) :
    (G.induce ({u}ᶜ : Set V)).Connected := by
  classical
  let S : Set V := {u}ᶜ
  let f : V → S := fun x ↦ if hx : x=u then ⟨a,ha.ne.symm⟩ else ⟨x,hx⟩
  have hf : ∀ x y, G.Adj x y → (G.induce S).Reachable (f x) (f y) := by
    intro x y hxy
    by_cases hx : x=u
    · subst x
      have hh := within_reachable_induce (⟨a,ha.ne.symm⟩ : S) ⟨y,hxy.ne.symm⟩ (hlinks y hxy)
      simpa only [f,dif_pos rfl,dif_neg hxy.ne.symm] using hh
    · by_cases hy : y=u
      · subst y
        have hh := within_reachable_induce (⟨a,ha.ne.symm⟩ : S) ⟨x,hxy.ne⟩ (hlinks x hxy.symm)
        simpa only [f,dif_pos rfl,dif_neg hxy.ne] using hh.symm
      · apply Adj.reachable
        change G.Adj (f x).val (f y).val
        simpa only [f,dif_neg hx,dif_neg hy] using hxy
  have hfx (x : S) : f x.val=x := by
    apply Subtype.ext
    have hx : x.val ≠ u := x.property
    simp [f,hx]
  letI : Nonempty S := ⟨⟨a,ha.ne.symm⟩⟩
  refine ⟨fun x y ↦ ?_⟩
  have hh := reachable_map_to_reachable f hf (hG.preconnected x.val y.val)
  simpa only [hfx] using hh

lemma delete_vertex_connected_of_degree_le_three {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.Connected) {u a : V} (ha : G.Adj u a)
    (hdeg : Nat.card (G.neighborSet u) ≤ 3)
    (hnb : ∀ x, G.Adj u x → ¬G.IsBridge s(u,x)) :
    (G.induce ({u}ᶜ : Set V)).Connected :=
  delete_vertex_connected_of_neighbor_links hG ha
    (fun _ hb ↦ neighbors_reachable_of_degree_le_three hdeg hnb ha hb)

lemma isolated_mem_support {V : Type*} {G : SimpleGraph V} {u a b : V}
    (hiso : ∀ x, ¬G.Adj u x) (p : G.Walk a b) (hu : u ∈ p.support) : a=u ∧ b=u := by
  induction p with
  | @nil z =>
    have hh : u=z := by simpa using hu
    exact ⟨hh.symm,hh.symm⟩
  | @cons a c b h p ih =>
    rcases List.mem_cons.mp hu with hu|hu
    · subst a
      exact (hiso c h).elim
    · obtain ⟨rfl,_⟩ := ih hu
      exact (hiso a h.symm).elim

lemma append_at_odd_to_isolated {V : Type*} [Fintype V] {A B : SimpleGraph V}
    {u v : V} (hAB : A ≤ B) (h : B.Adj u v) (hiso : ∀ x, ¬A.Adj u x)
    (hv : Odd (Nat.card (A.neighborSet v)))
    (hcover : B.edgeSet=insert s(u,v) A.edgeSet)
    (D : Finset A.Subgraph) (hD : GoodDecomposition A D) :
    ∃ E : Finset B.Subgraph, GoodDecomposition B E ∧ E.card ≤ D.card := by
  obtain ⟨T,hT,i,hi⟩ := EdgeDefect.decomposition_odd_endpoint D hD v hv
  have hu : u ∉ (T.walk i).support := by
    intro hm
    obtain ⟨ha,hb⟩ := isolated_mem_support hiso (T.walk i) hm
    rcases hi with hi|hi
    · exact h.ne (hi.trans ha).symm
    · exact h.ne (hi.trans hb).symm
  obtain ⟨U,_,_,hU,_⟩ := DeletionEndpoint.append_new_edge_tracked hAB T hT i hi h
    (fun hh ↦ hiso v hh) hcover
  exact MatchingAppend.path_family_partition U (hU hu)

lemma within_neighbor_add_one {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : G.Adj u v) :
    Nat.card ((within G ({u}ᶜ : Set V)).neighborSet v)+1=Nat.card (G.neighborSet v) := by
  have heq : (within G ({u}ᶜ : Set V)).neighborSet v=G.neighborSet v \ {u} := by
    ext x
    simp only [within,mem_neighborSet,Set.mem_compl_iff,Set.mem_singleton_iff,
      Set.mem_diff,h.ne.symm,not_false_eq_true,true_and]
  simp only [Nat.card_coe_set_eq]
  rw [heq]
  exact Set.ncard_diff_singleton_add_one h.symm

lemma restore_degree_three {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v a b : V} (hv : G.Adj u v) (ha : G.Adj u a) (hb : G.Adj u b)
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v)
    (hN : ∀ x, G.Adj u x → x=v ∨ x=a ∨ x=b)
    (heven : Even (Nat.card (G.neighborSet v)))
    (D : Finset (G.induce ({u}ᶜ : Set V)).Subgraph)
    (hD : GoodDecomposition (G.induce ({u}ᶜ : Set V)) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let A := within G ({u}ᶜ : Set V)
  let r : G.Walk a b := Walk.cons ha.symm (Walk.cons hb Walk.nil)
  let B := G.deleteEdges r.toSubgraph.edgeSet
  have hr : r.IsPath := by simp [r,Walk.cons_isPath_iff,ha.ne.symm,hb.ne,hab]
  have hre (x y : V) : s(x,y) ∈ r.toSubgraph.edgeSet ↔ s(x,y)=s(a,u) ∨ s(x,y)=s(u,b) := by
    simp only [r,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false]
  have hAB : A ≤ B := by
    intro x y hxy
    apply deleteEdges_adj.mpr
    refine ⟨hxy.1,?_⟩
    rw [hre]
    rintro (he|he) <;> rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hxy.2.2 rfl
    · exact hxy.2.1 rfl
    · exact hxy.2.1 rfl
    · exact hxy.2.2 rfl
  have hBuv : B.Adj u v := by
    apply deleteEdges_adj.mpr
    refine ⟨hv,?_⟩
    rw [hre]
    simp [ha.ne,hb.ne,hav.symm,hbv.symm]
  have hcover : B.edgeSet=insert s(u,v) A.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      constructor
      · intro he
        have he' := deleteEdges_adj.mp he
        rw [hre] at he'
        by_cases hx : x=u
        · subst x
          rcases hN y he'.1 with rfl|rfl|rfl
          · exact Or.inl rfl
          · exact (he'.2 (Or.inl Sym2.eq_swap)).elim
          · exact (he'.2 (Or.inr rfl)).elim
        · by_cases hy : y=u
          · subst y
            rcases hN x he'.1.symm with rfl|rfl|rfl
            · exact Or.inl Sym2.eq_swap
            · exact (he'.2 (Or.inl rfl)).elim
            · exact (he'.2 (Or.inr Sym2.eq_swap)).elim
          · exact Or.inr ⟨he'.1,hx,hy⟩
      · rintro (he|he)
        · exact (G.deleteEdges _).adj_congr_of_sym2 he |>.mpr hBuv
        · exact hAB he
  have hiso : ∀ x, ¬A.Adj u x := fun x hx ↦ hx.2.1 rfl
  have hod : Odd (Nat.card (A.neighborSet v)) := by
    have heq := within_neighbor_add_one hv
    change Nat.card (A.neighborSet v)+1=Nat.card (G.neighborSet v) at heq
    have hh : Even (Nat.card (A.neighborSet v)+1) := heq.symm ▸ heven
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hh)
  obtain ⟨D',hD',hDc⟩ := lift_induce_within ({u}ᶜ : Set V) D hD
  obtain ⟨E,hE,hEc⟩ := append_at_odd_to_isolated hAB hBuv hiso hod hcover D' hD'
  obtain ⟨F,hF,hFc⟩ := restore_path_subgraph (show IsPathSubgraph r.toSubgraph from ⟨_,_,r,hr,rfl⟩) hE
  exact ⟨F,hF,by omega⟩

lemma degree_three_other_neighbors {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (hv : G.Adj u v) (hd : Nat.card (G.neighborSet u)=3) :
    ∃ a b, G.Adj u a ∧ G.Adj u b ∧ a ≠ b ∧ a ≠ v ∧ b ≠ v ∧
      ∀ x, G.Adj u x → x=v ∨ x=a ∨ x=b := by
  have hc : (G.neighborSet u \ {v}).ncard=2 := by
    have hh := Set.ncard_diff_singleton_add_one (show v ∈ G.neighborSet u from hv)
    rw [Nat.card_coe_set_eq] at hd
    omega
  obtain ⟨a,b,hab,heq⟩ := Set.ncard_eq_two.mp hc
  have ha : a ∈ G.neighborSet u \ {v} := by rw [heq]; exact Or.inl rfl
  have hb : b ∈ G.neighborSet u \ {v} := by rw [heq]; exact Or.inr rfl
  refine ⟨a,b,ha.1,hb.1,hab,ha.2,hb.2,?_⟩
  intro x hx
  by_cases he : x=v
  · exact Or.inl he
  · have hx' : x ∈ G.neighborSet u \ {v} := ⟨hx,he⟩
    rw [heq] at hx'
    exact Or.inr hx'

lemma degree_three_odd_neighbors {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u : Fin n} (hd : Nat.card (G.neighborSet u)=3) :
    ∀ v, G.Adj u v → Odd (Nat.card (G.neighborSet v)) := by
  classical
  intro v hv
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨a,b,ha,hb,hab,hav,hbv,hN⟩ := degree_three_other_neighbors hv hd
  have hconn := delete_vertex_connected_of_degree_le_three hG hv (by omega)
    (fun x _ ↦ LeafReduction.bridgeless_of_odd_failure hsmall hn hG hfail s(u,x))
  have hc : ({u}ᶜ : Set (Fin n)).ncard=n-1 := by
    rw [Set.ncard_compl,Set.ncard_singleton,Nat.card_eq_fintype_card,Fintype.card_fin]
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce G ({u}ᶜ : Set (Fin n))
    (by rw [hc]; have := Fin.pos u; omega) hconn
  obtain ⟨E,hE,hEc⟩ := restore_degree_three hv ha hb hab hav hbv hN heven D hD
  rw [hc,ceil_half] at hDc
  obtain ⟨k,hk⟩ := hn
  exact hfail ⟨E,hE,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma degree_ge_four_at_even_neighbor {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (h : G.Adj u v) (hv : Even (Nat.card (G.neighborSet v))) :
    4 ≤ Nat.card (G.neighborSet u) := by
  have h3 := DegreeTwoReduction.min_degree_of_odd_failure hsmall hn hG hfail u
  have hn3 : Nat.card (G.neighborSet u) ≠ 3 := by
    intro he
    exact Nat.not_even_iff_odd.mpr (degree_three_odd_neighbors hsmall hn hG hfail he v h) hv
  omega

lemma degree_three_pair_adj {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v a b : Fin n} (hv : G.Adj u v) (ha : G.Adj u a) (hb : G.Adj u b)
    (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v)
    (hN : ∀ x, G.Adj u x → x=v ∨ x=a ∨ x=b) : G.Adj a b := by
  classical
  by_contra habG
  let F := G.deleteEdges {s(u,v)}
  have hF : F.Connected := hG.connected_delete_edge_of_not_isBridge
    (LeafReduction.bridgeless_of_odd_failure hsmall hn hG hfail s(u,v))
  have haF : F.Adj u a := by
    apply deleteEdges_adj.mpr
    refine ⟨ha,?_⟩
    simpa [Sym2.eq_iff,ha.ne,hv.ne] using hav
  have hbF : F.Adj u b := by
    apply deleteEdges_adj.mpr
    refine ⟨hb,?_⟩
    simpa [Sym2.eq_iff,hb.ne,hv.ne] using hbv
  have hNF : ∀ x, F.Adj u x → x=a ∨ x=b := by
    intro x hx
    have hh := deleteEdges_adj.mp hx
    rcases hN x hh.1 with rfl|hxa|hxb
    · exact (hh.2 rfl).elim
    · exact Or.inl hxa
    · exact Or.inr hxb
  have hc : ({u}ᶜ : Set (Fin n)).ncard=n-1 := by
    rw [Set.ncard_compl,Set.ncard_singleton,Nat.card_eq_fintype_card,Fintype.card_fin]
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce (DegreeTwoReduction.bypass F u a b) ({u}ᶜ : Set (Fin n))
    (by rw [hc]; have := Fin.pos u; omega) (DegreeTwoReduction.bypass_connected hF haF hbF hab hNF)
  obtain ⟨E,hE,hEc⟩ := DegreeTwoReduction.restore_bypass haF hbF hab hNF D hD
  have hnon : ¬F.Adj a b := fun hh ↦ habG (G.deleteEdges_le _ hh)
  simp only [if_neg hnon,add_zero] at hEc
  obtain ⟨P,hP,hPc⟩ := restore_edge hv hE
  rw [hc,ceil_half] at hDc
  obtain ⟨k,hk⟩ := hn
  exact hfail ⟨P,hP,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma edge_with_common_neighbor_not_bridge {V : Type*} {G : SimpleGraph V}
    {a b c : V} (hac : G.Adj a c) (hcb : G.Adj c b) : ¬G.IsBridge s(a,b) := by
  intro hbr
  have hh := (isBridge_iff_adj_and_forall_walk_mem_edges.mp hbr).2
    (Walk.cons hac (Walk.cons hcb Walk.nil))
  simp [hac.ne,hcb.ne.symm] at hh

lemma delete_edge_neighbor_add_one {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} (h : G.Adj a b) :
    Nat.card ((G.deleteEdges {s(a,b)}).neighborSet a)+1=Nat.card (G.neighborSet a) := by
  have heq : (G.deleteEdges {s(a,b)}).neighborSet a=G.neighborSet a \ {b} := by
    ext x
    simp only [mem_neighborSet,deleteEdges_adj,Set.mem_singleton_iff,Set.mem_diff]
    simp [h.ne]
  simp only [Nat.card_coe_set_eq]
  rw [heq]
  exact Set.ncard_diff_singleton_add_one h

lemma restore_path_at_odd_leaf {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u v : V} (P : G.Walk a b) (hp : P.IsPath)
    (h : (G.deleteEdges P.toSubgraph.edgeSet).Adj u v)
    (hleaf : ∀ x, (G.deleteEdges P.toSubgraph.edgeSet).Adj u x → x=v)
    (ho : Odd (Nat.card ((within (G.deleteEdges P.toSubgraph.edgeSet) ({u}ᶜ : Set V)).neighborSet v)))
    (D : Finset (within (G.deleteEdges P.toSubgraph.edgeSet) ({u}ᶜ : Set V)).Subgraph)
    (hD : GoodDecomposition (within (G.deleteEdges P.toSubgraph.edgeSet) ({u}ᶜ : Set V)) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  let B := G.deleteEdges P.toSubgraph.edgeSet
  let A := within B ({u}ᶜ : Set V)
  have hcover : B.edgeSet=insert s(u,v) A.edgeSet := by
    change B.edgeSet=insert s(u,v) (within B ({u}ᶜ : Set V)).edgeSet
    rw [LeafReduction.within_delete_leaf hleaf]
    conv_rhs => rw [edgeSet_deleteEdges]
    rw [Set.insert_diff_singleton,Set.insert_eq_of_mem (show s(u,v) ∈ B.edgeSet from h)]
  have hiso : ∀ x, ¬A.Adj u x := fun x hx ↦ hx.2.1 rfl
  obtain ⟨E,hE,hEc⟩ := append_at_odd_to_isolated (within_le B ({u}ᶜ : Set V)) h
    hiso ho hcover D hD
  obtain ⟨F,hF,hFc⟩ := restore_path_subgraph (show IsPathSubgraph P.toSubgraph from ⟨_,_,P,hp,rfl⟩) hE
  exact ⟨F,hF,by omega⟩

lemma induce_delete_edge {V : Type*} {G : SimpleGraph V} (S : Set V)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    (G.deleteEdges {s(a,b)}).induce S=(G.induce S).deleteEdges {s(⟨a,ha⟩,⟨b,hb⟩)} := by
  ext x y
  simp [deleteEdges_adj,Subtype.ext_iff]

/-- Delete the neighbor edge a-b first. The four missing edges can be
restored as the terminal extension a-u and the simple path a-b-u-v. -/
lemma restore_cubic_triangle {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v a b : V} (hv : G.Adj u v) (ha : G.Adj u a) (hb : G.Adj u b)
    (habG : G.Adj a b) (hav : a ≠ v) (hbv : b ≠ v)
    (hN : ∀ x, G.Adj u x → x=v ∨ x=a ∨ x=b)
    (ho : Odd (Nat.card (G.neighborSet a)))
    (D : Finset ((G.deleteEdges {s(a,b)}).induce ({u}ᶜ : Set V)).Subgraph)
    (hD : GoodDecomposition ((G.deleteEdges {s(a,b)}).induce ({u}ᶜ : Set V)) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 := by
  classical
  let F := G.deleteEdges {s(a,b)}
  let P : G.Walk a v := Walk.cons habG (Walk.cons hb.symm (Walk.cons hv Walk.nil))
  let B := G.deleteEdges P.toSubgraph.edgeSet
  have hp : P.IsPath := by
    simp [P,Walk.cons_isPath_iff,habG.ne,ha.ne.symm,hav,hb.ne.symm,hbv,hv.ne]
  have hre (x y : V) : s(x,y) ∈ P.toSubgraph.edgeSet ↔
      s(x,y)=s(a,b) ∨ s(x,y)=s(b,u) ∨ s(x,y)=s(u,v) := by
    simp only [P,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
      List.mem_cons,List.not_mem_nil,or_false]
  have hBua : B.Adj u a := by
    apply deleteEdges_adj.mpr
    refine ⟨ha,?_⟩
    rw [hre]
    simp [ha.ne,hb.ne,hv.ne,habG.ne,hav]
  have hleaf : ∀ x, B.Adj u x → x=a := by
    intro x hx
    have hh := deleteEdges_adj.mp hx
    rw [hre] at hh
    rcases hN x hh.1 with rfl|hh'|rfl
    · exact (hh.2 (Or.inr (Or.inr rfl))).elim
    · exact hh'
    · exact (hh.2 (Or.inr (Or.inl Sym2.eq_swap))).elim
  have hwithin : within B ({u}ᶜ : Set V)=within F ({u}ᶜ : Set V) := by
    ext x y
    by_cases hx : x=u
    · subst x; simp [within]
    by_cases hy : y=u
    · subst y; simp [within]
    have hn1 : s(x,y) ≠ s(b,u) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨_,rfl⟩|⟨rfl,_⟩
      · exact hy rfl
      · exact hx rfl
    have hn2 : s(x,y) ≠ s(u,v) := by
      intro he
      rcases Sym2.eq_iff.mp he with ⟨rfl,_⟩|⟨_,rfl⟩
      · exact hx rfl
      · exact hy rfl
    change (B.Adj x y ∧ x ≠ u ∧ y ≠ u) ↔ (F.Adj x y ∧ x ≠ u ∧ y ≠ u)
    simp only [B,F,deleteEdges_adj,hre,Set.mem_singleton_iff,hn1,hn2,or_false]
  have haF : F.Adj u a := by
    apply deleteEdges_adj.mpr
    refine ⟨ha,?_⟩
    simp [ha.ne,hb.ne]
  have hod : Odd (Nat.card ((within B ({u}ᶜ : Set V)).neighborSet a)) := by
    rw [hwithin]
    have hh1 := within_neighbor_add_one haF
    have hh2 := delete_edge_neighbor_add_one habG
    change Nat.card (F.neighborSet a)+1=Nat.card (G.neighborSet a) at hh2
    simp only [Nat.odd_iff] at ho ⊢
    omega
  have hex := lift_induce_within ({u}ᶜ : Set V) D hD
  change (∃ E : Finset (within F ({u}ᶜ : Set V)).Subgraph,
    GoodDecomposition (within F ({u}ᶜ : Set V)) E ∧ E.card ≤ D.card) at hex
  rw [←hwithin] at hex
  obtain ⟨D',hD',hDc⟩ := hex
  obtain ⟨E,hE,hEc⟩ := restore_path_at_odd_leaf P hp hBua hleaf hod D' hD'
  exact ⟨E,hE,by omega⟩

lemma no_degree_three_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    Nat.card (G.neighborSet u) ≠ 3 := by
  classical
  intro hd
  have hpos : 0 < (G.neighborSet u).ncard := by rw [←Nat.card_coe_set_eq,hd]; decide
  obtain ⟨v,hv⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  obtain ⟨a,b,ha,hb,hab,hav,hbv,hN⟩ := degree_three_other_neighbors hv hd
  have habG := degree_three_pair_adj hsmall hn hG hfail hv ha hb hab hav hbv hN
  have hvaG := degree_three_pair_adj hsmall hn hG hfail hb hv ha hav.symm hbv.symm hab
    (by intro x hx; have := hN x hx; tauto)
  have hvbG := degree_three_pair_adj hsmall hn hG hfail ha hv hb hbv.symm hav.symm hab.symm
    (by intro x hx; have := hN x hx; tauto)
  have ho := degree_three_odd_neighbors hsmall hn hG hfail hd a ha
  let S : Set (Fin n) := {u}ᶜ
  let a' : S := ⟨a,ha.ne.symm⟩
  let b' : S := ⟨b,hb.ne.symm⟩
  let v' : S := ⟨v,hv.ne.symm⟩
  have hconn : (G.induce S).Connected := delete_vertex_connected_of_degree_le_three hG hv (by omega)
    (fun x _ ↦ LeafReduction.bridgeless_of_odd_failure hsmall hn hG hfail s(u,x))
  have hnon : ¬(G.induce S).IsBridge s(a',b') := edge_with_common_neighbor_not_bridge
    (show (G.induce S).Adj a' v' from hvaG.symm) (show (G.induce S).Adj v' b' from hvbG)
  have hconn' : ((G.deleteEdges {s(a,b)}).induce S).Connected := by
    rw [induce_delete_edge S ha.ne.symm hb.ne.symm]
    exact hconn.connected_delete_edge_of_not_isBridge hnon
  have hc : S.ncard=n-1 := by
    change ({u}ᶜ : Set (Fin n)).ncard=n-1
    rw [Set.ncard_compl,Set.ncard_singleton,Nat.card_eq_fintype_card,Fintype.card_fin]
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce (G.deleteEdges {s(a,b)}) S
    (by rw [hc]; have := Fin.pos u; omega) hconn'
  obtain ⟨E,hE,hEc⟩ := restore_cubic_triangle hv ha hb habG hav hbv hN ho D hD
  rw [hc,ceil_half] at hDc
  obtain ⟨k,hk⟩ := hn
  exact hfail ⟨E,hE,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma min_degree_four_of_odd_failure {n : ℕ} (hsmall : SmallerOrders n) (hn : Odd n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    4 ≤ Nat.card (G.neighborSet u) := by
  have h3 := DegreeTwoReduction.min_degree_of_odd_failure hsmall hn hG hfail u
  have hne := no_degree_three_of_odd_failure hsmall hn hG hfail u
  omega

end Erdos583DegreeThreeReductionDevelopment
