import Submission.Work

/-! Paths joining degree-two vertices, with support-parity accounting. -/
namespace Erdos583TipParityDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical
open scoped Classical
set_option maxHeartbeats 1600000

lemma shortest_path_neighbor_not_mem {V : Type*} {G : SimpleGraph V}
    {u v b : V} (P : G.Walk u v) (hlen : P.length=G.dist u v)
    (hub : G.Adj u b) (hbs : b ≠ P.snd) : b ∉ P.support := by
  classical
  intro hb
  cases P with
  | nil => exact hub.ne.symm (by simpa using hb)
  | cons h P =>
    have hbp : b ∈ P.support := by simpa only [Walk.support_cons,List.mem_cons,hub.ne.symm,false_or] using hb
    have ht := length_eq_dist_of_subwalk hlen ((Walk.cons h P).isSubwalk_takeUntil hb)
    rw [Walk.takeUntil_cons hbp hub.ne h,Walk.length_cons,dist_eq_one_iff_adj.mpr hub] at ht
    have hn : (P.takeUntil b hbp).Nil := Walk.nil_iff_length_eq.mpr (by omega)
    exact hbs (by simpa only [Walk.snd_cons] using hn.eq.symm)

lemma support_evenCount_eq {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ComponentDeficit.evenCount (G.induce G.support)=
      {v | v ∈ G.support ∧ Even (Nat.card (G.neighborSet v))}.ncard := by
  classical
  have hd (x : G.support) :
      Nat.card ((G.induce G.support).neighborSet x)=Nat.card (G.neighborSet x.val) := by
    simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,degree_induce_support]
  let e : {x : G.support // Even (Nat.card ((G.induce G.support).neighborSet x))} ≃
      {v | v ∈ G.support ∧ Even (Nat.card (G.neighborSet v))} :=
    { toFun := fun x ↦ ⟨x.val.val,x.val.property,by simpa only [hd] using x.property⟩
      invFun := fun x ↦ ⟨⟨x.val,x.property.1⟩,by rw [hd]; exact x.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  unfold ComponentDeficit.evenCount
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
  exact Nat.card_congr e

lemma delete_path_degree_parity {V : Type*} [Finite V] {G : SimpleGraph V}
    {a b x : V} (P : G.Walk a b) (hp : P.IsPath) (hxa : x ≠ a) (hxb : x ≠ b) :
    Even (Nat.card ((G.deleteEdges P.toSubgraph.edgeSet).neighborSet x)) ↔
      Even (Nat.card (G.neighborSet x)) := by
  have hs := ncard_neighbor_delete_subgraph_add P.toSubgraph x
  have he := Nat.even_iff.mp (path_neighbor_ncard_even hp hxa hxb)
  simp only [Nat.card_coe_set_eq,Nat.even_iff]
  omega

lemma delete_path_evenCount_le_of_two_isolated {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a b u v : V} (P : G.Walk a b) (hp : P.IsPath)
    (huv : u ≠ v) (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v)))
    (hzu : u ∉ (G.deleteEdges P.toSubgraph.edgeSet).support)
    (hzv : v ∉ (G.deleteEdges P.toSubgraph.edgeSet).support) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    ComponentDeficit.evenCount (H.induce H.support) ≤ ComponentDeficit.evenCount G := by
  classical
  dsimp only
  rw [support_evenCount_eq]
  let A := {v | Even (Nat.card (G.neighborSet v))}
  let H := G.deleteEdges P.toSubgraph.edgeSet
  let B := {v | v ∈ H.support ∧ Even (Nat.card (H.neighborSet v))}
  have hsub : B ⊆ (A \ {u,v}) ∪ {a,b} := by
    intro x hx
    by_cases hxa : x=a
    · exact Or.inr (Or.inl hxa)
    by_cases hxb : x=b
    · exact Or.inr (Or.inr hxb)
    refine Or.inl ⟨(delete_path_degree_parity P hp hxa hxb).mp hx.2,?_⟩
    rintro (rfl|rfl)
    · exact hzu hx.1
    · exact hzv hx.1
  have hpair : ({u,v} : Set V) ⊆ A := by
    rintro x (rfl|rfl)
    · exact hu
    · exact hv
  have hc := Set.ncard_le_ncard hsub
  have hd := Set.ncard_diff_add_ncard_of_subset hpair
  rw [Set.ncard_pair huv] at hd
  have hb := Set.ncard_union_le (A \ {u,v}) ({a,b} : Set V)
  have htwo : ({a,b} : Set V).ncard ≤ 2 := by
    by_cases hab : a=b
    · subst b; simp
    · exact (Set.ncard_pair hab).le
  change B.ncard ≤ A.ncard
  omega

lemma degree_two_internal_isolated {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b u : V} (P : G.Walk a b) (hp : P.IsPath) (hu : Nat.card (G.neighborSet u)=2)
    (hup : u ∈ P.support) (hua : u ≠ a) (hub : u ≠ b) :
    u ∉ (G.deleteEdges P.toSubgraph.edgeSet).support := by
  classical
  have hn : ¬P.Nil := by
    intro hh
    have he := Walk.nil_iff_support_eq.mp hh
    rw [he] at hup
    exact hua (List.mem_singleton.mp hup)
  have hi := path_neighbor_ncard_formula hp hn u
  simp only [hua,hub,false_or,if_false,if_pos hup] at hi
  have hs := ncard_neighbor_delete_subgraph_add P.toSubgraph u
  rw [Nat.card_coe_set_eq] at hu
  rw [hi,hu] at hs
  have hzero : ((G.deleteEdges P.toSubgraph.edgeSet).neighborSet u).ncard=0 := by omega
  have he : (G.deleteEdges P.toSubgraph.edgeSet).neighborSet u=∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp hzero
  rintro ⟨z,hz⟩
  exact Set.notMem_empty z (he ▸ hz)

lemma exists_path_internal_two {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.Connected) {u v : V} (hu : 2 ≤ Nat.card (G.neighborSet u))
    (hv : 2 ≤ Nat.card (G.neighborSet v)) (hdis : Disjoint (G.neighborSet u) (G.neighborSet v)) :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ u ∈ P.support ∧ v ∈ P.support ∧
      u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b := by
  classical
  obtain ⟨P,hp,hlen⟩ := hG.exists_path_of_dist u v
  have choose_other (x z : V) (hx : 2 ≤ Nat.card (G.neighborSet x)) :
      ∃ y, G.Adj x y ∧ y ≠ z := by
    rw [Nat.card_coe_set_eq] at hx
    obtain ⟨c,d,hc,hd,hcd⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp (by omega : 1 < (G.neighborSet x).ncard)
    by_cases hcz : c=z
    · exact ⟨d,hd,fun hh ↦ hcd (hcz.trans hh.symm)⟩
    · exact ⟨c,hc,hcz⟩
  obtain ⟨a,hua,ha⟩ := choose_other u P.snd hu
  obtain ⟨b,hvb,hb⟩ := choose_other v P.reverse.snd hv
  have haP := shortest_path_neighbor_not_mem P hlen hua ha
  have hbr : P.reverse.length=G.dist v u := by rw [Walk.length_reverse,hlen,dist_comm]
  have hbP : b ∉ P.support := by
    simpa only [Walk.support_reverse,List.mem_reverse] using shortest_path_neighbor_not_mem P.reverse hbr hvb hb
  have hab : a ≠ b := by
    rintro rfl
    exact Set.disjoint_left.mp hdis hua hvb
  let Q := (Walk.cons hua.symm P).concat hvb
  have hQ : Q.IsPath := by
    apply (Walk.concat_isPath_iff hvb).mpr
    refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hp,haP⟩,?_⟩
    simpa only [Walk.support_cons,List.mem_cons,not_or] using And.intro hab.symm hbP
  have hau : a ≠ u := fun h ↦ haP (h ▸ P.start_mem_support)
  have hav : a ≠ v := fun h ↦ haP (h ▸ P.end_mem_support)
  have hbu : b ≠ u := fun h ↦ hbP (h ▸ P.start_mem_support)
  have hbv : b ≠ v := fun h ↦ hbP (h ▸ P.end_mem_support)
  refine ⟨a,b,Q,hQ,?_,?_,hau.symm,hbu.symm,hav.symm,hbv.symm⟩
  · simp [Q]
  · simp [Q]

lemma support_card_bound_two_missing {V : Type*} [Fintype V] (H : SimpleGraph V)
    {u v : V} (huv : u ≠ v) (hu : u ∉ H.support) (hv : v ∉ H.support) :
    H.support.ncard+2 ≤ Fintype.card V := by
  have hsub : H.support ⊆ ({u,v} : Set V)ᶜ := by
    intro x hx
    rintro (rfl|rfl)
    · exact hu hx
    · exact hv hx
  have hs := Set.ncard_le_ncard hsub
  rw [Set.ncard_compl,Set.ncard_pair huv,Nat.card_eq_fintype_card] at hs
  have hpair := ({u,v} : Set V).ncard_le_card
  rw [Set.ncard_pair huv,Nat.card_eq_fintype_card] at hpair
  omega

lemma failure_path_isolating_two_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {a b u v : Fin n} (P : G.Walk a b) (hp : P.IsPath) (huv : u ≠ v)
    (hu : Even (Nat.card (G.neighborSet u))) (hv : Even (Nat.card (G.neighborSet v)))
    (hzu : u ∉ (G.deleteEdges P.toSubgraph.edgeSet).support)
    (hzv : v ∉ (G.deleteEdges P.toSubgraph.edgeSet).support) :
    6 ≤ ComponentDeficit.evenCount G := by
  have hs : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n := by
    simpa only [Fintype.card_fin] using support_card_bound_two_missing
      (G.deleteEdges P.toSubgraph.edgeSet) huv hzu hzv
  have he := ComponentDeficit.failure_path_six_even_support hsmall hfail P hp hs
  exact he.trans (delete_path_evenCount_le_of_two_isolated P hp huv hu hv hzu hzv)

lemma two_degree_two_implies_six_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : u ≠ v)
    (hu : Nat.card (G.neighborSet u)=2) (hv : Nat.card (G.neighborSet v)=2) :
    6 ≤ ComponentDeficit.evenCount G := by
  obtain ⟨a,b,P,hp,hup,hvp,hua,hub,hva,hvb⟩ :=
    exists_path_internal_two hG hu.ge hv.ge
      (DegreeTwoPacking.degree_two_neighbors_disjoint hsmall hG hfail huv hu hv)
  exact failure_path_isolating_two_even hsmall hfail P hp huv
    (by rw [hu]; decide) (by rw [hv]; decide)
    (degree_two_internal_isolated P hp hu hup hua hub)
    (degree_two_internal_isolated P hp hv hvp hva hvb)

/-- The even count here is in the ORIGINAL graph. This is a necessary
condition on a globally smallest failure, not a proof of the whole conjecture
for graphs with at most five even vertices. -/
lemma degree_two_at_most_one_of_five_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (he : ComponentDeficit.evenCount G ≤ 5) :
    {u | Nat.card (G.neighborSet u)=2}.ncard ≤ 1 := by
  by_contra hn
  have ht : 1 < {u | Nat.card (G.neighborSet u)=2}.ncard := by omega
  obtain ⟨u,v,hu,hv,huv⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp ht
  have hge := two_degree_two_implies_six_even hsmall hG hfail huv hu hv
  omega

end Erdos583TipParityDevelopment
