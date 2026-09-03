import Submission.Work

/-! Original even-vertex counts after path deletion, including isolated leaves. -/
namespace Erdos583LowDegreeParityDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.VertexCritical Erdos583Work.TipParity
open scoped Classical
set_option maxHeartbeats 1600000

lemma even_degree_of_not_support {V : Type*} {G : SimpleGraph V} {v : V}
    (hv : v ∉ G.support) : Even (Nat.card (G.neighborSet v)) := by
  have he : G.neighborSet v=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hv (G.mem_support.mpr ⟨w,hw⟩)
  simp [he]

lemma delete_path_evenCount_le_add_two {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a b : V} (P : G.Walk a b) (hp : P.IsPath) :
    ComponentDeficit.evenCount (G.deleteEdges P.toSubgraph.edgeSet) ≤
      ComponentDeficit.evenCount G+2 := by
  classical
  let A := {v | Even (Nat.card (G.neighborSet v))}
  let B := {v | Even (Nat.card ((G.deleteEdges P.toSubgraph.edgeSet).neighborSet v))}
  have hsub : B ⊆ A ∪ {a,b} := by
    intro x hx
    by_cases hxa : x=a
    · exact Or.inr (Or.inl hxa)
    by_cases hxb : x=b
    · exact Or.inr (Or.inr hxb)
    exact Or.inl ((delete_path_degree_parity P hp hxa hxb).mp hx)
  have hs := Set.ncard_le_ncard hsub
  have hc := Set.ncard_union_le A ({a,b} : Set V)
  have htwo : ({a,b} : Set V).ncard ≤ 2 := by
    by_cases hab : a=b
    · subst b; simp
    · exact (Set.ncard_pair hab).le
  change B.ncard ≤ A.ncard+2
  omega

lemma support_evenCount_add_two_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    {u v : V} (huv : u ≠ v) (hu : u ∉ G.support) (hv : v ∉ G.support) :
    ComponentDeficit.evenCount (G.induce G.support)+2 ≤ ComponentDeficit.evenCount G := by
  let A := {v | Even (Nat.card (G.neighborSet v))}
  let B := {v | v ∈ G.support ∧ Even (Nat.card (G.neighborSet v))}
  have hsub : B ∪ {u,v} ⊆ A := by
    rintro x (hx|rfl|rfl)
    · exact hx.2
    · exact even_degree_of_not_support hu
    · exact even_degree_of_not_support hv
  have hd : Disjoint B ({u,v} : Set V) := by
    apply Set.disjoint_left.mpr
    rintro x hx (rfl|rfl)
    · exact hu hx.1
    · exact hv hx.1
  have hs := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hd,Set.ncard_pair huv] at hs
  rw [support_evenCount_eq]
  exact hs

lemma evenCount_eq_support_add_compl {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ComponentDeficit.evenCount G=ComponentDeficit.evenCount (G.induce G.support)+G.supportᶜ.ncard := by
  rw [support_evenCount_eq]
  let A := {v | Even (Nat.card (G.neighborSet v))}
  let B := {v | v ∈ G.support ∧ Even (Nat.card (G.neighborSet v))}
  have he : B ∪ G.supportᶜ=A := by
    ext x
    constructor
    · rintro (hx|hx)
      · exact hx.2
      · exact even_degree_of_not_support hx
    · intro hx
      by_cases hs : x ∈ G.support
      · exact Or.inl ⟨hs,hx⟩
      · exact Or.inr hs
  have hd : Disjoint B G.supportᶜ := Set.disjoint_left.mpr fun _ hx hn ↦ hn hx.1
  change A.ncard=B.ncard+G.supportᶜ.ncard
  rw [←he,Set.ncard_union_eq hd]

lemma delete_path_evenCount_support_deficit {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a b : V} (P : G.Walk a b) (hp : P.IsPath) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    ComponentDeficit.evenCount (H.induce H.support)+Fintype.card V ≤
      ComponentDeficit.evenCount G+H.support.ncard+2 := by
  have hs := delete_path_evenCount_le_add_two P hp
  rw [evenCount_eq_support_add_compl,Set.ncard_compl,Nat.card_eq_fintype_card] at hs
  have hc := (G.deleteEdges P.toSubgraph.edgeSet).support.ncard_le_card
  rw [Nat.card_eq_fintype_card] at hc
  dsimp only
  omega

lemma delete_path_support_evenCount_le_of_two_missing {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a b u v : V} (P : G.Walk a b) (hp : P.IsPath)
    (huv : u ≠ v) (hu : u ∉ (G.deleteEdges P.toSubgraph.edgeSet).support)
    (hv : v ∉ (G.deleteEdges P.toSubgraph.edgeSet).support) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    ComponentDeficit.evenCount (H.induce H.support) ≤ ComponentDeficit.evenCount G := by
  have hs := support_evenCount_add_two_le (G.deleteEdges P.toSubgraph.edgeSet) huv hu hv
  have hc := delete_path_evenCount_le_add_two P hp
  dsimp only
  omega

lemma delete_path_support_evenCount_le {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a b : V} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ Fintype.card V) :
    let H := G.deleteEdges P.toSubgraph.edgeSet
    ComponentDeficit.evenCount (H.induce H.support) ≤ ComponentDeficit.evenCount G := by
  have hc : 1 < (G.deleteEdges P.toSubgraph.edgeSet).supportᶜ.ncard := by
    rw [Set.ncard_compl,Nat.card_eq_fintype_card]
    omega
  obtain ⟨u,v,hu,hv,huv⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hc
  exact delete_path_support_evenCount_le_of_two_missing P hp huv hu hv

lemma failure_path_six_original_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :
    6 ≤ ComponentDeficit.evenCount G := by
  exact (ComponentDeficit.failure_path_six_even_support hsmall hfail P hp hsize).trans
    (delete_path_support_evenCount_le P hp (by simpa only [Fintype.card_fin] using hsize))

/-- The number of original even vertices is at least four more than the
number of vertices missing from the residual support. -/
lemma failure_path_evenCount_deficit {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)}
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n) :
    n+4 ≤ ComponentDeficit.evenCount G+(G.deleteEdges P.toSubgraph.edgeSet).support.ncard := by
  have hs := ComponentDeficit.failure_path_six_even_support hsmall hfail P hp hsize
  have he := delete_path_evenCount_support_deficit P hp
  dsimp only at hs he
  simp only [Fintype.card_fin] at he
  omega

lemma restore_path_five_original_even {n : ℕ} (hsmall : SmallerOrders n)
    (G : SimpleGraph (Fin n)) {a b : Fin n} (P : G.Walk a b) (hp : P.IsPath)
    (hsize : (G.deleteEdges P.toSubgraph.edgeSet).support.ncard+2 ≤ n)
    (he : ComponentDeficit.evenCount G ≤ 5) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  apply ComponentDeficit.restore_path_five_even_support hsmall G P hp hsize
  exact (delete_path_support_evenCount_le P hp
    (by simpa only [Fintype.card_fin] using hsize)).trans he

lemma degree_one_endpoint_isolated {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} (P : G.Walk a b) (hp : P.IsPath) (hn : ¬P.Nil)
    (ha : Nat.card (G.neighborSet a)=1) :
    a ∉ (G.deleteEdges P.toSubgraph.edgeSet).support := by
  classical
  have hi := path_neighbor_ncard_formula hp hn a
  simp only [true_or,if_true] at hi
  have hs := ncard_neighbor_delete_subgraph_add P.toSubgraph a
  rw [Nat.card_coe_set_eq] at ha
  rw [hi,ha] at hs
  have hzero : ((G.deleteEdges P.toSubgraph.edgeSet).neighborSet a).ncard=0 := by omega
  have he := (Set.ncard_eq_zero (Set.toFinite _)).mp hzero
  intro h
  obtain ⟨z,hz⟩ := (G.deleteEdges P.toSubgraph.edgeSet).mem_support.mp h
  exact Set.notMem_empty z (he ▸ hz)

lemma two_leaves_implies_six_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : u ≠ v)
    (hu : Nat.card (G.neighborSet u)=1) (hv : Nat.card (G.neighborSet v)=1) :
    6 ≤ ComponentDeficit.evenCount G := by
  obtain ⟨P,hp,_⟩ := hG.exists_path_of_dist u v
  have hzu := degree_one_endpoint_isolated P hp (Walk.not_nil_of_ne huv) hu
  have hzv : v ∉ (G.deleteEdges P.toSubgraph.edgeSet).support := by
    simpa only [Walk.toSubgraph_reverse] using
      degree_one_endpoint_isolated P.reverse hp.reverse (Walk.not_nil_of_ne huv.symm) hv
  apply failure_path_six_original_even hsmall hfail P hp
  simpa only [Fintype.card_fin] using support_card_bound_two_missing
    (G.deleteEdges P.toSubgraph.edgeSet) huv hzu hzv

lemma path_with_prescribed_start_and_internal {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hG : G.Connected) {u v : V} (huv : u ≠ v)
    (hv : 2 ≤ Nat.card (G.neighborSet v)) :
    ∃ (b : V) (Q : G.Walk u b), Q.IsPath ∧ ¬Q.Nil ∧ v ∈ Q.support ∧ v ≠ b := by
  classical
  obtain ⟨P,hp,hlen⟩ := hG.exists_path_of_dist u v
  rw [Nat.card_coe_set_eq] at hv
  obtain ⟨x,y,hx,hy,hxy⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp
    (by omega : 1 < (G.neighborSet v).ncard)
  obtain ⟨b,hvb,hb⟩ : ∃ b, G.Adj v b ∧ b ≠ P.reverse.snd := by
    by_cases hx' : x=P.reverse.snd
    · exact ⟨y,hy,fun hh ↦ hxy (hx'.trans hh.symm)⟩
    · exact ⟨x,hx,hx'⟩
  have hbr : P.reverse.length=G.dist v u := by rw [Walk.length_reverse,hlen,dist_comm]
  have hbP : b ∉ P.support := by
    simpa only [Walk.support_reverse,List.mem_reverse] using
      shortest_path_neighbor_not_mem P.reverse hbr hvb hb
  let Q := P.concat hvb
  have hQ : Q.IsPath := hp.concat hbP hvb
  have hvQ : v ∈ Q.support := by simp [Q]
  refine ⟨b,Q,hQ,?_,hvQ,hvb.ne⟩
  intro hn
  rw [Walk.nil_iff_support_eq.mp hn] at hvQ
  exact huv.symm (List.mem_singleton.mp hvQ)

lemma leaf_and_degree_two_implies_six_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : u ≠ v)
    (hu : Nat.card (G.neighborSet u)=1) (hv : Nat.card (G.neighborSet v)=2) :
    6 ≤ ComponentDeficit.evenCount G := by
  obtain ⟨b,P,hp,hn,hvP,hvb⟩ := path_with_prescribed_start_and_internal hG huv hv.ge
  have hzu := degree_one_endpoint_isolated P hp hn hu
  have hzv := degree_two_internal_isolated P hp hv hvP huv.symm hvb
  apply failure_path_six_original_even hsmall hfail P hp
  simpa only [Fintype.card_fin] using support_card_bound_two_missing
    (G.deleteEdges P.toSubgraph.edgeSet) huv hzu hzv

lemma two_low_degree_implies_six_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (huv : u ≠ v)
    (hu : Nat.card (G.neighborSet u)=1 ∨ Nat.card (G.neighborSet u)=2)
    (hv : Nat.card (G.neighborSet v)=1 ∨ Nat.card (G.neighborSet v)=2) :
    6 ≤ ComponentDeficit.evenCount G := by
  rcases hu with hu|hu <;> rcases hv with hv|hv
  · exact two_leaves_implies_six_even hsmall hG hfail huv hu hv
  · exact leaf_and_degree_two_implies_six_even hsmall hG hfail huv hu hv
  · exact leaf_and_degree_two_implies_six_even hsmall hG hfail huv.symm hv hu
  · exact two_degree_two_implies_six_even hsmall hG hfail huv hu hv

lemma low_degree_card_le_one_of_five_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (he : ComponentDeficit.evenCount G ≤ 5) :
    {u | Nat.card (G.neighborSet u)=1 ∨ Nat.card (G.neighborSet u)=2}.ncard ≤ 1 := by
  by_contra hn
  have ht : 1 < {u | Nat.card (G.neighborSet u)=1 ∨ Nat.card (G.neighborSet u)=2}.ncard := by omega
  obtain ⟨u,v,hu,hv,huv⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp ht
  have hge := two_low_degree_implies_six_even hsmall hG hfail huv hu hv
  omega

end Erdos583LowDegreeParityDevelopment
