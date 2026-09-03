import Submission.StarCopyIntegrated

/-! Upper bounds on terminal weight from the capacity of the deleted graph.
These are necessary conditions, not the missing lower bound for Gallai. -/
namespace Erdos583TerminalCapacityDevelopment
open SimpleGraph Erdos583Work Erdos583Work.MatchingTrim
open scoped Classical
set_option maxHeartbeats 2400000

lemma path_length_le_of_avoids {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (hp : p.IsPath) (hv : v ∉ p.support) :
    p.length ≤ Fintype.card V - 2 := by
  have hsub : p.support.toFinset ⊆ (Finset.univ.erase v : Finset V) := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h ↦ hv (h ▸ List.mem_toFinset.mp hx), Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hcard
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hcard
  omega

lemma path_edge_capacity_at_vertex {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath) (hne : ¬p.Nil) (v : V) :
    2*p.toSubgraph.edgeSet.ncard ≤ 2*(Fintype.card V-2) +
      (p.toSubgraph.neighborSet v).ncard +
      (if (p.toSubgraph.neighborSet v).ncard=1 then 1 else 0) := by
  rw [path_edgeSet_ncard hp]
  have hinc : (p.toSubgraph.neighborSet v).ncard +
      (if (p.toSubgraph.neighborSet v).ncard=1 then 1 else 0) =
      if v ∈ p.support then 2 else 0 := by
    rw [path_neighbor_ncard_formula hp hne]
    have hend : v=a ∨ v=b → v ∈ p.support := by
      rintro (rfl|rfl)
      · exact p.start_mem_support
      · exact p.end_mem_support
    split_ifs <;> simp_all
  rw [Nat.add_assoc, hinc]
  by_cases hv : v ∈ p.support
  · rw [if_pos hv]
    have hlen := hp.length_lt
    have hpos : 0 < p.length := by cases p <;> simp_all
    omega
  · rw [if_neg hv]
    have hlen := path_length_le_of_avoids p hp hv
    omega

/-- A density bound which also records the endpoint multiplicity at one
vertex. Unlike the degree-only inequality, this detects the loss of a
Hamilton path when that vertex is absent. -/
lemma edge_capacity_at_vertex {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) (v : V) :
    2*G.edgeSet.ncard ≤ 2*(Fintype.card V-2)*D.card + G.degree v +
      endpointMultiplicity D v := by
  have hlocal (K : G.Subgraph) (hK : K ∈ D) :
      2*K.edgeSet.ncard ≤ 2*(Fintype.card V-2) + (K.neighborSet v).ncard +
        (if (K.neighborSet v).ncard=1 then 1 else 0) := by
    obtain ⟨a,b,p,hp,rfl⟩ := hD.1 K hK
    apply path_edge_capacity_at_vertex p hp
    intro hnil
    have h := hne _ hK
    cases hnil
    simp at h
  have hs := Finset.sum_le_sum hlocal
  have he : G.edgeSet.ncard = ∑ K ∈ D, K.edgeSet.ncard := by
    simpa using hD.2.ncard_inter_eq_sum Set.univ
  rw [he, hD.2.degree_eq_sum, endpointMultiplicity, Finset.card_filter]
  simpa only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, Nat.mul_comm] using hs

/-- Any lower bound for partitions of the deleted graph is an upper bound
on terminal weight. -/
lemma terminal_weight_of_deletion_lower_bound {V : Type*} [Fintype V]
    {H F : SimpleGraph V} (hFH : F ≤ H)
    (hm : ∀ v, (F.neighborSet v).Subsingleton)
    {D : Finset H.Subgraph} (hD : GoodDecomposition H D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) (q : ℕ)
    (hlower : ∀ E : Finset (H \ F).Subgraph, GoodDecomposition (H \ F) E → q ≤ E.card) :
    q + terminalWeight D F ≤ D.card + F.edgeSet.ncard := by
  obtain ⟨E,hE,hEc⟩ := trim_decomposition F hFH hm hD hne
  exact (Nat.add_le_add_right (hlower E hE) _).trans hEc

lemma terminal_weight_copy_lower_bound {V : Type*} [Fintype V]
    {H F : SimpleGraph (Bool × V)} {G : SimpleGraph V}
    (hFH : F ≤ H) (hm : ∀ v, (F.neighborSet v).Subsingleton)
    (hdel : H \ F = pairedCopies G ∅)
    {D : Finset H.Subgraph} (hD : GoodDecomposition H D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) (q : ℕ)
    (hlower : ∀ E : Finset G.Subgraph, GoodDecomposition G E → q ≤ E.card) :
    2*q + terminalWeight D F ≤ D.card + F.edgeSet.ncard := by
  apply terminal_weight_of_deletion_lower_bound hFH hm hD hne (2*q)
  rw [hdel]
  intro E hE
  obtain ⟨B,hB,hBc⟩ := decompose_one_of_two_copies hE
  have hq := hlower B hB
  omega

/-- Restriction to a spanning subgraph, with the exact endpoint counts
of the surviving path components. -/
lemma restrict_path_normal {V : Type*} [Fintype V] {H J : SimpleGraph V}
    {a b : V} (p : H.Walk a b) (hp : p.IsPath) :
    ∃ E : Finset J.Subgraph,
      (∀ K ∈ E, IsPathSubgraph K) ∧
      Set.PairwiseDisjoint (E : Set J.Subgraph) (fun K ↦ K.edgeSet) ∧
      (⋃ K ∈ E, K.edgeSet)=p.toSubgraph.edgeSet ∩ J.edgeSet ∧
      (∀ K ∈ E, K.edgeSet.Nonempty) ∧
      (∀ v, endpointMultiplicity E v =
        if Odd (Nat.card ((p.toSubgraph.spanningCoe ⊓ J).neighborSet v)) then 1 else 0) ∧
      2*E.card=Nat.card {v // Odd (Nat.card ((p.toSubgraph.spanningCoe ⊓ J).neighborSet v))} := by
  let A := p.toSubgraph.spanningCoe ⊓ J
  have hA : A.IsAcyclic := (path_spanningCoe_isAcyclic p hp).anti inf_le_left
  obtain ⟨D,hD,hne,hends,hcard⟩ := forest_normal_decomposition A hA
  let f : A.Subgraph → J.Subgraph := Subgraph.map (Hom.ofLE inf_le_right)
  refine ⟨D.image f,?_,hD.2.lift_pairwise inf_le_right,?_,?_,?_,?_⟩
  · intro K hK
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    exact lift_path_subgraph inf_le_right (hD.1 L hL)
  · rw [hD.2.lift_union inf_le_right,edgeSet_inf]
    rfl
  · intro K hK
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hK
    exact (edgeSet_lift inf_le_right L).symm ▸ hne L hL
  · intro v
    rw [endpointMultiplicity_lift inf_le_right D v,hends]
    simp only [A,Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  · rw [Finset.card_image_of_injective _ (lift_subgraph_injective inf_le_right)]
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hcard

/-- Refinements with nonempty pieces have exact, not just subadditive,
cardinality and endpoint bookkeeping. -/
lemma refine_decomposition_exact {V : Type*} [Fintype V] {G J : SimpleGraph V}
    (hJG : J ≤ G) {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (f : D → Finset J.Subgraph)
    (hp : ∀ H, ∀ K ∈ f H, IsPathSubgraph K)
    (hd : ∀ H, Set.PairwiseDisjoint (f H : Set J.Subgraph) (fun K ↦ K.edgeSet))
    (hc : ∀ H, (⋃ K ∈ f H, K.edgeSet)=H.val.edgeSet ∩ J.edgeSet)
    (hne : ∀ H, ∀ K ∈ f H, K.edgeSet.Nonempty) :
    ∃ E : Finset J.Subgraph, GoodDecomposition J E ∧
      (∀ K ∈ E, K.edgeSet.Nonempty) ∧ E.card=∑ H, (f H).card ∧
      ∀ v, endpointMultiplicity E v=∑ H, endpointMultiplicity (f H) v := by
  have hsub (H : D) (K : J.Subgraph) (hK : K ∈ f H) : K.edgeSet ⊆ H.val.edgeSet := by
    intro e he
    have hh : e ∈ ⋃ K ∈ f H, K.edgeSet := Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨hK,he⟩⟩
    rw [hc] at hh
    exact hh.1
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset D) : Set D) f := by
    intro H _ K _ hHK
    apply Finset.disjoint_left.mpr
    intro L hL hL'
    obtain ⟨e,he⟩ := hne H L hL
    exact Set.disjoint_left.mp (hD.2.1 H.property K.property (fun h ↦ hHK (Subtype.ext h)))
      (hsub H L hL he) (hsub K L hL' he)
  obtain ⟨E,hE,hcard,hinc⟩ := MarkedDouble.refine_decomposition_tracked hJG hD f hp hd hc
  have hUE : Finset.univ.biUnion f ⊆ E := by
    intro K hK
    obtain ⟨H,_,hK⟩ := Finset.mem_biUnion.mp hK
    exact hinc H hK
  have hUcard : (Finset.univ.biUnion f).card=∑ H, (f H).card := Finset.card_biUnion hdis
  have heq : E=Finset.univ.biUnion f :=
    (Finset.eq_of_subset_of_card_le hUE (hcard.trans_eq hUcard.symm)).symm
  refine ⟨E,hE,?_,by rw [heq,hUcard],?_⟩
  · intro K hK
    rw [heq] at hK
    obtain ⟨H,_,hK⟩ := Finset.mem_biUnion.mp hK
    exact hne H K hK
  · intro v
    simp only [endpointMultiplicity,Finset.card_filter]
    rw [heq,Finset.sum_biUnion hdis]

/-- At an endpoint used exactly once, a terminal matching incidence
leaves no endpoint in any of the restricted members. -/
lemma restricted_degree_even_of_terminal {V : Type*} [Fintype V]
    {H F : SimpleGraph V} (hm : ∀ v, (F.neighborSet v).Subsingleton)
    {D : Finset H.Subgraph} (hD : GoodDecomposition H D)
    {K L : H.Subgraph} (hK : K ∈ D) (hL : L ∈ D) {v : V}
    (hv : endpointMultiplicity D v=1) (ht : v ∈ terminalVertices K F) :
    ¬Odd (Nat.card ((L.spanningCoe \ F).neighborSet v)) := by
  have ht' := (Finset.mem_filter.mp ht).2
  have hdeg : (L.neighborSet v).ncard ≤ 2 := path_neighbor_ncard_le_two (hD.1 L hL) v
  have hsum : ((L.spanningCoe \ F).neighborSet v).ncard +
      ((L.spanningCoe ⊓ F).neighborSet v).ncard=(L.neighborSet v).ncard := by
    have hh := Set.ncard_inter_add_ncard_diff_eq_ncard (L.neighborSet v) (F.neighborSet v)
    change ((L.spanningCoe ⊓ F).neighborSet v).ncard +
      ((L.spanningCoe \ F).neighborSet v).ncard=(L.neighborSet v).ncard at hh
    omega
  simp only [Nat.card_coe_set_eq, Nat.odd_iff]
  by_cases hLK : L=K
  · subst L
    rw [ht'.1,ht'.2] at hsum
    omega
  · have hdne : (L.neighborSet v).ncard ≠ 1 := by
      intro hd
      have hcard : (D.filter fun P ↦ (P.neighborSet v).ncard=1).card ≤ 1 := by
        change endpointMultiplicity D v ≤ 1
        omega
      exact hLK (Finset.card_le_one.mp hcard L
        (Finset.mem_filter.mpr ⟨hL,hd⟩) K (Finset.mem_filter.mpr ⟨hK,ht'.1⟩))
    have hb : ((L.spanningCoe ⊓ F).neighborSet v).ncard=0 := by
      suffices he : (L.spanningCoe ⊓ F).neighborSet v=∅ by simp [he]
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hkpos : 0 < ((K.spanningCoe ⊓ F).neighborSet v).ncard := by omega
      obtain ⟨z,hz⟩ := (Set.ncard_pos (Set.toFinite _)).mp hkpos
      have hwz : w=z := hm v hw.2 hz.2
      have heK : s(v,w) ∈ K.edgeSet := hwz.symm ▸ hz.1
      exact Set.disjoint_left.mp (hD.2.1 hL hK hLK) hw.1 heK
    rw [hb] at hsum
    omega

/-- Exact matching trimming, retaining the vanishing endpoint information
at every terminal matching incidence of endpoint multiplicity one. -/
lemma trim_decomposition_exact {V : Type*} [Fintype V]
    {H F : SimpleGraph V} (hFH : F ≤ H)
    (hm : ∀ v, (F.neighborSet v).Subsingleton)
    {D : Finset H.Subgraph} (hD : GoodDecomposition H D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) :
    ∃ E : Finset (H \ F).Subgraph, GoodDecomposition (H \ F) E ∧
      (∀ K ∈ E, K.edgeSet.Nonempty) ∧
      E.card+terminalWeight D F=D.card+F.edgeSet.ncard ∧
      ∀ v, endpointMultiplicity D v=1 →
        (∃ K ∈ D, v ∈ terminalVertices K F) → endpointMultiplicity E v=0 := by
  have hparts (K : D) :
      ∃ E : Finset (H \ F).Subgraph,
        (∀ L ∈ E, IsPathSubgraph L) ∧
        Set.PairwiseDisjoint (E : Set (H \ F).Subgraph) (fun L ↦ L.edgeSet) ∧
        (⋃ L ∈ E, L.edgeSet)=K.val.edgeSet ∩ (H \ F).edgeSet ∧
        (∀ L ∈ E, L.edgeSet.Nonempty) ∧
        E.card+(terminalVertices K.val F).card=1+(K.val.edgeSet ∩ F.edgeSet).ncard ∧
        ∀ v, endpointMultiplicity E v =
          if Odd (Nat.card ((K.val.spanningCoe \ F).neighborSet v)) then 1 else 0 := by
    obtain ⟨a,b,p,hp,hK⟩ := hD.1 K.val K.property
    have hn : ¬p.Nil := by
      intro hn
      obtain ⟨e,he⟩ := hne K.val K.property
      rw [hK] at he
      cases hn
      simp at he
    obtain ⟨E,hpE,hdE,hcE,hneE,hendsE,hcardE⟩ := restrict_path_normal (J := H \ F) p hp
    have hg : p.toSubgraph.spanningCoe ⊓ (H \ F)=p.toSubgraph.spanningCoe \ F := by
      ext x y
      constructor
      · rintro ⟨h,_,hn⟩; exact ⟨h,hn⟩
      · rintro ⟨h,hn⟩; exact ⟨h,p.toSubgraph.adj_sub h,hn⟩
    rw [hg] at hcardE hendsE
    have ht := trim_odd_card F hm p hp hn
    simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hcardE
    refine ⟨E,hpE,hdE,by simpa only [hK] using hcE,hneE,?_,?_⟩
    · rw [hK]
      simp only [←Nat.card_eq_fintype_card] at hcardE
      omega
    · intro v
      simpa only [hK] using hendsE v
  choose f hp hd hc hnf hcf hef using hparts
  obtain ⟨E,hE,hneE,hcardE,hendsE⟩ := refine_decomposition_exact sdiff_le hD f hp hd hc hnf
  have hs := Finset.sum_congr rfl (fun K (_ : K ∈ (Finset.univ : Finset D)) ↦ hcf K)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul,mul_one] at hs
  rw [Finset.sum_coe_sort D (fun K ↦ (terminalVertices K F).card),
    Finset.sum_coe_sort D (fun K ↦ (K.edgeSet ∩ F.edgeSet).ncard)] at hs
  have hi := hD.2.ncard_inter_eq_sum F.edgeSet
  rw [Set.inter_eq_right.mpr (edgeSet_mono hFH)] at hi
  rw [←hi] at hs
  refine ⟨E,hE,hneE,?_,?_⟩
  · unfold terminalWeight
    omega
  · intro v hv ⟨K,hK,ht⟩
    rw [hendsE]
    apply Finset.sum_eq_zero
    intro L _
    rw [hef,if_neg (restricted_degree_even_of_terminal hm hD hK L.property hv ht)]

end Erdos583TerminalCapacityDevelopment
