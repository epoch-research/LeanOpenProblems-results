import Submission.Work

/-! Edge-capacity lower bounds and the sharp boundary case for odd-order
complete graphs minus a maximum matching. These are not a proof of Gallai. -/

open SimpleGraph Erdos583Work
namespace Erdos583BoundsDevelopment

lemma GoodDecomposition.card_edges_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D) :
    G.edgeSet.ncard ≤ D.card * (Fintype.card V - 1) := by
  classical
  have he : G.edgeSet.ncard = ∑ K ∈ D, K.edgeSet.ncard := by
    simpa using hD.2.ncard_inter_eq_sum Set.univ
  rw [he]
  calc
    ∑ K ∈ D, K.edgeSet.ncard ≤ ∑ _K ∈ D, (Fintype.card V - 1) := by
      apply Finset.sum_le_sum
      intro K hK
      obtain ⟨u, v, p, hp, rfl⟩ := hD.1 K hK
      rw [path_edgeSet_ncard hp]
      have hl := hp.length_lt
      omega
    _ = D.card * (Fintype.card V - 1) := by simp

lemma GoodDecomposition.card_gt_of_edge_capacity {V : Type*} [Fintype V]
    {G : SimpleGraph V} {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (k : ℕ) (hm : k * (Fintype.card V - 1) < G.edgeSet.ncard) : k < D.card := by
  by_contra hn
  have hc := GoodDecomposition.card_edges_le hD
  have hmul := Nat.mul_le_mul_right (Fintype.card V - 1) (show D.card ≤ k by omega)
  omega

lemma edge_ncard_add_compl {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard + (Gᶜ).edgeSet.ncard = (Fintype.card V).choose 2 := by
  classical
  have hn := Set.ncard_diff_add_ncard_of_subset
    (edgeSet_mono (show Gᶜ ≤ (⊤ : SimpleGraph V) from le_top))
  rw [← edgeSet_sdiff, top_sdiff, compl_compl] at hn
  have ht : (⊤ : SimpleGraph V).edgeSet.ncard = (Fintype.card V).choose 2 := by
    rw [Set.ncard_eq_toFinset_card']
    exact card_edgeFinset_top_eq_card_choose_two
  exact hn.trans ht

lemma odd_order_edge_ncard_add_compl {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) (hn : Fintype.card V = 2*k+1) :
    G.edgeSet.ncard + (Gᶜ).edgeSet.ncard = k*(2*k+1) := by
  rw [edge_ncard_add_compl, hn, Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm (2*k+1), Nat.mul_assoc]
  simp

namespace WaleckiCycles
open Erdos583Work.Walecki Erdos583Work.WaleckiCycles

/-- When all k marked cycle edges are deleted, no extra path is needed. -/
lemma canonical_maximum_matching_decomposition (k : ℕ) (hk : 0 < k) :
    ∃ D : Finset ((prefixMatching k k)ᶜ).Subgraph,
      GoodDecomposition (prefixMatching k k)ᶜ D ∧ D.card ≤ k := by
  classical
  letI : NeZero (2*k) := ⟨by omega⟩
  let F := prefixMatching k k
  let J := Fᶜ
  obtain ⟨c, hc, hd⟩ := exists_cycle_family k hk
  choose a b q hq hqe hql using fun i ↦
    exists_cycle_cut_edge (c i) (hc i).1 (middleEdge i) (hc i).2.2.2.1
  have hqJ (i : Fin k) : ∀ e ∈ (q i).edges, e ∈ J.edgeSet := by
    intro e he
    have hec : e ∈ (c i).toSubgraph.edgeSet \ {middleEdge i} :=
      hqe i ▸ (q i).mem_edges_toSubgraph.mpr he
    change e ∈ ((⊤ : SimpleGraph (Option (ZMod (2*k)))) \ F).edgeSet
    rw [edgeSet_sdiff]
    refine ⟨(q i).edges_subset_edgeSet he, ?_⟩
    intro heF
    obtain ⟨j, hj, rfl⟩ := (prefixMatching_mem _).mp heF
    have hcol := (hc i).2.2.2.2 (middleA j) (middleB j) ((c i).mem_edges_toSubgraph.mp hec.1)
    have hij : i = j := Fin.ext (hcol.symm.trans (middle_color j))
    subst j
    exact hec.2 (by simp)
  let r (i : Fin k) := (q i).transfer J (hqJ i)
  have hr (i : Fin k) : (r i).IsPath := (hq i).transfer (hqJ i)
  have hre (i : Fin k) : (r i).toSubgraph.edgeSet =
      (c i).toSubgraph.edgeSet \ {middleEdge i} := by
    simpa [r, Walk.edgeSet_toSubgraph] using hqe i
  have hrL (i : Fin k) : (r i).length = 2*k := by
    have h₁ := hql i
    have h₂ := (hc i).2.1
    simp only [r, Walk.length_transfer]
    omega
  have hdr : Pairwise (fun i j ↦ Disjoint (r i).toSubgraph.edgeSet (r j).toSubgraph.edgeSet) := by
    intro i j hij
    rw [hre, hre]
    exact (hd hij).mono Set.diff_subset Set.diff_subset
  have hcJ : J.edgeSet.ncard = k*(2*k) := by
    have hh := odd_order_edge_ncard_add_compl J k (by rw [Fintype.card_option, ZMod.card])
    have hf : (Jᶜ).edgeSet.ncard = k := by
      change ((Fᶜ)ᶜ).edgeSet.ncard = k
      rw [compl_compl]
      exact prefixMatching_ncard le_rfl
    rw [hf] at hh
    nlinarith
  have hsum : ∑ i : Fin k, (r i).toSubgraph.edgeSet.ncard = J.edgeSet.ncard := by
    simp only [path_edgeSet_ncard (hr _), hrL, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, hcJ]
  obtain ⟨D, hD, hn⟩ := decomposition_of_family_of_card J (fun i ↦ (r i).toSubgraph)
    (fun i ↦ ⟨_, _, r i, hr i, rfl⟩) hdr hsum
  exact ⟨D, hD, by simpa using hn⟩

end WaleckiCycles

/-- The floor bound for odd order when the complement matching is maximum. -/
lemma complete_odd_maximum_matching_deletion {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hn : Fintype.card V = 2*k+1)
    (hm : ∀ x, ((Gᶜ).neighborSet x).Subsingleton) (hc : (Gᶜ).edgeSet.ncard = k) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  by_cases hk : k = 0
  · subst k
    letI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have ht : G.edgeSet = ∅ := by
      ext e
      induction e using Sym2.ind with
      | h x y => simp [Subsingleton.elim x y]
    refine ⟨∅, ⟨by simp, by simp, ?_⟩, by simp⟩
    simp [ht]
  · have hkpos : 0 < k := by omega
    letI : NeZero (2*k) := ⟨by omega⟩
    let F := Erdos583Work.WaleckiCycles.prefixMatching k k
    obtain ⟨e, he⟩ := matching_equiv_of_card F Gᶜ
      (Erdos583Work.WaleckiCycles.prefixMatching_matching k k) hm
      (by rw [Fintype.card_option, ZMod.card, hn])
      ((Erdos583Work.WaleckiCycles.prefixMatching_ncard le_rfl).trans hc.symm)
    have hJ : G.comap e = Fᶜ := by
      ext x y
      rw [comap_adj, compl_adj]
      have hrel := he x y
      rw [compl_adj] at hrel
      constructor
      · intro hxy
        refine ⟨fun h ↦ hxy.ne (congrArg e h), ?_⟩
        intro hF
        exact (hrel.mpr hF).2 hxy
      · rintro ⟨hne, hnF⟩
        by_contra hnG
        exact hnF (hrel.mp ⟨fun h ↦ hne (e.injective h), hnG⟩)
    have hex : ∃ D : Finset (G.comap e).Subgraph,
        GoodDecomposition (G.comap e) D ∧ D.card ≤ k := by
      rw [hJ]
      exact WaleckiCycles.canonical_maximum_matching_decomposition k hkpos
    obtain ⟨D, hD, hnD⟩ := hex
    obtain ⟨E, hE, hnE⟩ := GoodDecomposition.map_comap_equiv e hD
    exact ⟨E, hE, hnE.trans hnD⟩

/-- The exact optimum in the odd-order complement-matching family. A maximum
matching permits k paths; a smaller matching forces k+1 by edge capacity. -/
lemma sharp_odd_complement_matching_decomposition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hn : Fintype.card V = 2*k+1)
    (hm : ∀ x, ((Gᶜ).neighborSet x).Subsingleton) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card = k + (if (Gᶜ).edgeSet.ncard < k then 1 else 0) ∧
      ∀ E : Finset G.Subgraph, GoodDecomposition G E → D.card ≤ E.card := by
  classical
  have hsupport := matching_support_card Gᶜ hm
  have hsle := Set.ncard_le_card (Gᶜ).support
  rw [Nat.card_eq_fintype_card] at hsle
  have ht : (Gᶜ).edgeSet.ncard ≤ k := by omega
  have hec := odd_order_edge_ncard_add_compl G k hn
  by_cases heq : (Gᶜ).edgeSet.ncard = k
  · obtain ⟨D, hD, hc⟩ := complete_odd_maximum_matching_deletion G k hn hm heq
    have hl (E : Finset G.Subgraph) (hE : GoodDecomposition G E) : k ≤ E.card := by
      have hb := GoodDecomposition.card_edges_le hE
      rw [hn] at hb
      simp only [Nat.add_sub_cancel] at hb
      rw [heq] at hec
      by_cases hk : k = 0
      · omega
      · nlinarith
    have hDc : D.card = k := Nat.le_antisymm hc (hl D hD)
    refine ⟨D, hD, ?_, fun E hE ↦ hDc ▸ hl E hE⟩
    simp [hDc, heq]
  · have hlt : (Gᶜ).edgeSet.ncard < k := by omega
    have hcap : k * (Fintype.card V - 1) < G.edgeSet.ncard := by
      rw [hn]
      simp only [Nat.add_sub_cancel]
      nlinarith
    have hl (E : Finset G.Subgraph) (hE : GoodDecomposition G E) : k+1 ≤ E.card :=
      GoodDecomposition.card_gt_of_edge_capacity hE k hcap
    obtain ⟨D, hD, hc⟩ := complete_odd_matching_deletion G (by exact ⟨k, hn⟩) hm
    have hDc : D.card = k+1 := by have hh := hl D hD; omega
    refine ⟨D, hD, ?_, fun E hE ↦ hDc ▸ hl E hE⟩
    simp [hDc, hlt]

lemma GoodDecomposition.exists_endpoint {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D) (hne : G.edgeSet.Nonempty) :
    ∃ v, 0 < endpointMultiplicity D v := by
  classical
  obtain ⟨e, he⟩ := hne
  have heD : e ∈ ⋃ K ∈ D, K.edgeSet := hD.2.2.symm ▸ he
  simp only [Set.mem_iUnion] at heD
  obtain ⟨K, hK, heK⟩ := heD
  obtain ⟨u, v, p, hp, rfl⟩ := hD.1 K hK
  have hpne : ¬p.Nil := by
    intro hh
    cases hh
    simp at heK
  have hd : (p.toSubgraph.neighborSet u).ncard = 1 := by
    rw [hp.neighborSet_toSubgraph_startpoint hpne]
    simp
  refine ⟨u, ?_⟩
  change 0 < (D.filter fun K ↦ (K.neighborSet u).ncard = 1).card
  exact Finset.card_pos.mpr ⟨p.toSubgraph, Finset.mem_filter.mpr ⟨hK, hd⟩⟩

/-- A nonempty graph of minimum degree d requires at least (d+1)/2 paths.
An endpoint improves the elementary maximum-degree capacity bound. -/
lemma GoodDecomposition.min_degree_lower_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) (hne : G.edgeSet.Nonempty)
    (d : ℕ) (hd : ∀ v, d ≤ G.degree v) : d+1 ≤ 2*D.card := by
  obtain ⟨v, hv⟩ := GoodDecomposition.exists_endpoint hD hne
  have hb := hD.degree_add_endpointMultiplicity_le v
  have hh := hd v
  omega

/-- In even order at least four, deleting any matching leaves path number n/2. -/
lemma sharp_even_complement_matching_decomposition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k) (hn : Fintype.card V = 2*k)
    (hm : ∀ x, ((Gᶜ).neighborSet x).Subsingleton) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card = k ∧
      ∀ E : Finset G.Subgraph, GoodDecomposition G E → D.card ≤ E.card := by
  classical
  have hdeg (v : V) : 2*k-2 ≤ G.degree v := by
    have hc : (Gᶜ).degree v ≤ 1 := by
      rw [← neighborSet_ncard]
      exact (Set.ncard_le_one (Set.toFinite _)).mpr (hm v)
    rw [degree_compl, hn] at hc
    omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj (Classical.arbitrary V)).mp
    (by have := hdeg (Classical.arbitrary V); omega)
  have hne : G.edgeSet.Nonempty := ⟨s(Classical.arbitrary V, w), hvw⟩
  have hl (E : Finset G.Subgraph) (hE : GoodDecomposition G E) : k ≤ E.card := by
    have hh := GoodDecomposition.min_degree_lower_bound hE hne (2*k-2) hdeg
    omega
  obtain ⟨D, hD, hc⟩ := complete_even_matching_deletion G (by exact ⟨k, by omega⟩) hm
  have hDc : D.card = k := by have hh := hl D hD; omega
  exact ⟨D, hD, hDc, fun E hE ↦ hDc ▸ hl E hE⟩

end Erdos583BoundsDevelopment
