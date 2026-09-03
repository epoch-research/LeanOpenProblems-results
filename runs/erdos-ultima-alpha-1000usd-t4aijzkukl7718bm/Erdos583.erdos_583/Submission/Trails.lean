import Submission.Work

/-! Trail surgery for the all-odd case. The normal trail partition constructed
here is not a simple-path partition. -/

open SimpleGraph Erdos583Work
namespace Erdos583TrailDevelopment

set_option maxHeartbeats 1200000

lemma trail_append_of_disjoint {V : Type*} {G : SimpleGraph V}
    {a b c : V} {p : G.Walk a b} {q : G.Walk b c}
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hd : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet) :
    (p.append q).IsTrail := by
  rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
  refine ⟨hp.edges_nodup, hq.edges_nodup, ?_⟩
  intro e he f hf hef
  subst f
  exact Set.disjoint_left.mp hd (p.mem_edges_toSubgraph.mpr he)
    (q.mem_edges_toSubgraph.mpr hf)

/-- Trail parity is determined by the two endpoints, even if their local
 degrees exceed one. -/
lemma trail_neighbor_ncard_even_iff {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} {p : G.Walk a b} (hp : p.IsTrail) (x : V) :
    Even (p.toSubgraph.neighborSet x).ncard ↔ a ≠ b → x ≠ a ∧ x ≠ b := by
  classical
  let F := p.toSubgraph.spanningCoe
  have hedge : ∀ e ∈ p.edges, e ∈ F.edgeSet := fun e he ↦ p.mem_edges_toSubgraph.mpr he
  let q := p.transfer F hedge
  have hq : q.IsTrail := by simpa [q, Walk.isTrail_def] using hp
  have hE : q.IsEulerian := hq.isEulerian_of_forall_mem fun e he ↦ by
    simpa [q] using p.mem_edges_toSubgraph.mp he
  have hd : F.degree x = (p.toSubgraph.neighborSet x).ncard := by
    rw [← neighborSet_ncard]
    rfl
  rw [← hd]
  exact hE.even_degree_iff

lemma trail_neighbor_ncard_odd_iff {V : Type*} [Fintype V] {G : SimpleGraph V}
    {a b : V} {p : G.Walk a b} (hp : p.IsTrail) (x : V) :
    Odd (p.toSubgraph.neighborSet x).ncard ↔ a ≠ b ∧ (x = a ∨ x = b) := by
  rw [← Nat.not_even_iff_odd, trail_neighbor_ncard_even_iff hp]
  tauto

/-- A closed trail can be spliced at either endpoint, preserving the endpoints
of the open trail. No claim of vertex-simplicity is made. -/
lemma splice_closed_trail {V : Type*} {G : SimpleGraph V}
    {a b v : V} (p : G.Walk a b) (c : G.Walk v v)
    (hp : p.IsTrail) (hc : c.IsTrail) (hv : v = a ∨ v = b)
    (hd : Disjoint p.toSubgraph.edgeSet c.toSubgraph.edgeSet) :
    ∃ q : G.Walk a b, q.IsTrail ∧ q.toSubgraph = p.toSubgraph ⊔ c.toSubgraph := by
  rcases hv with rfl | rfl
  · exact ⟨c.append p, trail_append_of_disjoint hc hp hd.symm, by simp [sup_comm]⟩
  · exact ⟨p.append c, trail_append_of_disjoint hp hc hd, by simp⟩

/-- Replace one member of an indexed trail family by splicing in an
edge-disjoint closed trail. -/
lemma extend_trail_family {V I : Type*} {G : SimpleGraph V}
    {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsTrail)
    (hpp : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet)
    {v : V} (c : G.Walk v v) (hc : c.IsTrail)
    (hpc : ∀ i, Disjoint (p i).toSubgraph.edgeSet c.toSubgraph.edgeSet)
    (i : I) (hi : v = a i ∨ v = b i) :
    ∃ q : ∀ j, G.Walk (a j) (b j),
      (∀ j, (q j).IsTrail) ∧
      (Pairwise fun j k ↦ Disjoint (q j).toSubgraph.edgeSet (q k).toSubgraph.edgeSet) ∧
      (∀ e, (∃ j, e ∈ (q j).toSubgraph.edgeSet) ↔
        (∃ j, e ∈ (p j).toSubgraph.edgeSet) ∨ e ∈ c.toSubgraph.edgeSet) := by
  classical
  obtain ⟨r, hr, hre⟩ := splice_closed_trail (p i) c (hp i) hc hi (hpc i)
  let q := Function.update p i r
  have hqi : q i = r := by simp [q]
  have hqj (j : I) (hj : j ≠ i) : q j = p j := by simp [q, hj]
  have hqe : (q i).toSubgraph.edgeSet = (p i).toSubgraph.edgeSet ∪ c.toSubgraph.edgeSet := by
    rw [hqi, hre, Subgraph.edgeSet_sup]
  refine ⟨q, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst j; simpa [hqi] using hr
    · simpa [hqj j hj] using hp j
  · intro j k hjk
    by_cases hj : j = i
    · subst j
      rw [hqe, hqj k hjk.symm]
      exact disjoint_sup_left.mpr ⟨hpp hjk, (hpc k).symm⟩
    · by_cases hk : k = i
      · subst k
        rw [hqj j hj, hqe]
        exact disjoint_sup_right.mpr ⟨hpp hjk, hpc j⟩
      · rw [hqj j hj, hqj k hk]
        exact hpp hjk
  · intro e
    constructor
    · rintro ⟨j, hj⟩
      by_cases hji : j = i
      · subst j
        rw [hqe] at hj
        exact hj.elim (fun h ↦ Or.inl ⟨i, h⟩) Or.inr
      · exact Or.inl ⟨j, by simpa [hqj j hji] using hj⟩
    · rintro (⟨j, hj⟩ | he)
      · by_cases hji : j = i
        · subst j
          exact ⟨i, hqe.symm ▸ Or.inl hj⟩
        · exact ⟨j, by simpa [hqj j hji] using hj⟩
      · exact ⟨i, hqe.symm ▸ Or.inr he⟩

/-- If the endpoints of a trail family cover all vertices, every disjoint
cycle remainder can be absorbed without changing that indexed endpoint system. -/
lemma absorb_cycle_family {V I : Type*} {G : SimpleGraph V} {a b : I → V}
    (hend : ∀ v, ∃ i, v = a i ∨ v = b i)
    (C : Finset G.Subgraph) (hC : ∀ K ∈ C, IsCycleSubgraph K)
    (hCC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun K ↦ K.edgeSet))
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsTrail)
    (hpp : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet)
    (hpc : ∀ i K, K ∈ C → Disjoint (p i).toSubgraph.edgeSet K.edgeSet) :
    ∃ q : ∀ i, G.Walk (a i) (b i),
      (∀ i, (q i).IsTrail) ∧
      (Pairwise fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet) ∧
      (∀ e, (∃ i, e ∈ (q i).toSubgraph.edgeSet) ↔
        (∃ i, e ∈ (p i).toSubgraph.edgeSet) ∨ ∃ K ∈ C, e ∈ K.edgeSet) := by
  classical
  induction C using Finset.induction_on generalizing p with
  | empty =>
    exact ⟨p, hp, hpp, by simp⟩
  | @insert K C hKC ih =>
    have hC' : ∀ L ∈ C, IsCycleSubgraph L := fun L hL ↦ hC L (Finset.mem_insert_of_mem hL)
    have hCC' : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun L ↦ L.edgeSet) :=
      fun L hL M hM hLM ↦ hCC (Finset.mem_insert_of_mem hL) (Finset.mem_insert_of_mem hM) hLM
    obtain ⟨q, hq, hqq, hqe⟩ := ih hC' hCC' p hp hpp
      (fun i L hL ↦ hpc i L (Finset.mem_insert_of_mem hL))
    obtain ⟨v, c, hc, rfl⟩ := hC K (Finset.mem_insert_self _ _)
    have hqc (i : I) : Disjoint (q i).toSubgraph.edgeSet c.toSubgraph.edgeSet := by
      apply Set.disjoint_left.mpr
      intro e he hce
      rcases (hqe e).mp ⟨i, he⟩ with ⟨j, hj⟩ | ⟨L, hL, heL⟩
      · exact Set.disjoint_left.mp (hpc j _ (Finset.mem_insert_self _ _)) hj hce
      · exact Set.disjoint_left.mp
          (hCC (Finset.mem_insert_of_mem hL) (Finset.mem_insert_self _ _)
            (fun h ↦ hKC (h ▸ hL))) heL hce
    obtain ⟨i, hi⟩ := hend v
    obtain ⟨r, hr, hrr, hre⟩ := extend_trail_family q hq hqq c hc.isTrail hqc i hi
    refine ⟨r, hr, hrr, ?_⟩
    intro e
    rw [hre, hqe]
    simp only [Finset.mem_insert, exists_eq_or_imp]
    exact or_assoc.trans (or_congr_right or_comm)


/-- Every finite all-odd graph has exactly n/2 edge-disjoint open trails,
with every vertex used exactly once as an endpoint. These trails may revisit
vertices. -/
lemma all_odd_normal_trail_partition {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ho : ∀ v, Odd (G.degree v)) :
    ∃ k : ℕ, 2*k = Fintype.card V ∧
      ∃ a b : Fin k → V, ∃ p : ∀ i, G.Walk (a i) (b i),
        (∀ i, (p i).IsTrail) ∧
        Function.Bijective (fun x : Fin k × Bool ↦ if x.2 then a x.1 else b x.1) ∧
        (Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet) ∧
        (∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (p i).toSubgraph.edgeSet) := by
  classical
  obtain ⟨P, C, hP, hC, hD, hPC, hend, hcard⟩ := normal_path_cycle_decomposition G
  choose a b p hp he using fun K : P ↦ (hP K.val K.property).1
  have hab (K : P) : a K ≠ b K :=
    path_endpoints_ne (hp K) (he K ▸ (hP K.val K.property).2)
  have hcard' : 2*P.card = Fintype.card V := by
    simpa [ho] using hcard
  let e : Fin P.card ≃ P := (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm
  let aa : Fin P.card → V := a ∘ e
  let bb : Fin P.card → V := b ∘ e
  let pp (i : Fin P.card) : G.Walk (aa i) (bb i) := p (e i)
  let f : Fin P.card × Bool → V := fun x ↦ if x.2 then aa x.1 else bb x.1
  have hs : Function.Surjective f := by
    intro v
    have h1 : (P.filter fun K ↦ (K.neighborSet v).ncard = 1).card = 1 := by
      simpa [endpointMultiplicity, ho v] using hend v
    obtain ⟨K, hK⟩ := Finset.card_pos.mp (show 0 < (P.filter fun K ↦
      (K.neighborSet v).ncard = 1).card by omega)
    obtain ⟨hKP, hKv⟩ := Finset.mem_filter.mp hK
    let L : P := ⟨K, hKP⟩
    have hva : v = a L ∨ v = b L := by
      by_contra hn
      have hn' := not_or.mp hn
      have hEven := path_neighbor_ncard_even (hp L) hn'.1 hn'.2
      have hh : (p L).toSubgraph.neighborSet v = K.neighborSet v := by rw [← he L]
      rw [hh, hKv] at hEven
      exact (by decide : ¬Even (1 : ℕ)) hEven
    rcases hva with hv | hv
    · exact ⟨(e.symm L, true), by simpa [f, aa] using hv.symm⟩
    · exact ⟨(e.symm L, false), by simpa [f, bb] using hv.symm⟩
  have hcf : Fintype.card (Fin P.card × Bool) = Fintype.card V := by
    simpa [Nat.mul_comm] using hcard'
  have hf : Function.Bijective f :=
    ⟨(Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcf)).mpr hs, hs⟩
  have hends (v : V) : ∃ i, v = aa i ∨ v = bb i := by
    obtain ⟨⟨i, c⟩, hi⟩ := hs v
    cases c
    · exact ⟨i, Or.inr hi.symm⟩
    · exact ⟨i, Or.inl hi.symm⟩
  have hpp : Pairwise fun i j ↦ Disjoint (pp i).toSubgraph.edgeSet (pp j).toSubgraph.edgeSet := by
    intro i j hij
    have hne : (e i).val ≠ (e j).val := fun hh ↦ hij (e.injective (Subtype.ext hh))
    have hd := hD.1 (Finset.mem_union_left _ (e i).property)
      (Finset.mem_union_left _ (e j).property) hne
    simpa only [he] using hd
  have hCC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun K ↦ K.edgeSet) :=
    fun K hK L hL hKL ↦ hD.1 (Finset.mem_union_right _ hK) (Finset.mem_union_right _ hL) hKL
  have hpc (i : Fin P.card) (K : G.Subgraph) (hK : K ∈ C) :
      Disjoint (pp i).toSubgraph.edgeSet K.edgeSet := by
    have hne : (e i).val ≠ K := fun hh ↦ Finset.disjoint_left.mp hPC (hh ▸ (e i).property) hK
    have hd := hD.1 (Finset.mem_union_left _ (e i).property) (Finset.mem_union_right _ hK) hne
    simpa only [he] using hd
  obtain ⟨q, hq, hqq, hqe⟩ := absorb_cycle_family hends C hC hCC pp
    (fun i ↦ (hp (e i)).isTrail) hpp hpc
  refine ⟨P.card, hcard', aa, bb, q, hq, hf, hqq, ?_⟩
  intro d
  rw [hqe]
  constructor
  · intro hd
    have hh : d ∈ ⋃ K ∈ P ∪ C, K.edgeSet := hD.2.symm ▸ hd
    simp only [Set.mem_iUnion] at hh
    obtain ⟨K, hK, hdK⟩ := hh
    rcases Finset.mem_union.mp hK with hKP | hKC
    · refine Or.inl ⟨e.symm ⟨K, hKP⟩, ?_⟩
      simpa only [pp, Equiv.apply_symm_apply, ← he] using hdK
    · exact Or.inr ⟨K, hKC, hdK⟩
  · rintro (⟨i, hi⟩ | ⟨K, _, hK⟩)
    · exact (pp i).toSubgraph.edgeSet_subset hi
    · exact K.edgeSet_subset hK


open scoped Classical in
/-- The all-odd simple-path theorem would follow from a path-and-cycle
partition with at most n/2 members. Parity leaves no room for cycles. -/
lemma all_odd_paths_of_bounded_path_cycle {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (ho : ∀ v, Odd (G.degree v))
    (P C : Finset G.Subgraph)
    (hP : ∀ K ∈ P, IsPathSubgraph K) (hC : ∀ K ∈ C, IsCycleSubgraph K)
    (hD : IsDecomposition G (P ∪ C))
    (hn : 2*(P.card+C.card) ≤ Fintype.card V) :
    GoodDecomposition G P ∧ C = ∅ ∧ 2*P.card = Fintype.card V := by
  classical
  choose a b p hp he using fun K : P ↦ hP K.val K.property
  let f : P × Bool → V := fun x ↦ if x.2 then a x.1 else b x.1
  have hs : Function.Surjective f := by
    intro v
    by_contra hn
    have hmiss (x : P × Bool) : f x ≠ v := fun hx ↦ hn ⟨x, hx⟩
    have hEven : Even (G.degree v) := by
      rw [hD.degree_eq_sum]
      apply Finset.even_sum
      intro K hK
      rcases Finset.mem_union.mp hK with hKP | hKC
      · let L : P := ⟨K, hKP⟩
        change Even (L.val.neighborSet v).ncard
        rw [he L]
        apply path_neighbor_ncard_even (hp L)
        · exact (show a L ≠ v by simpa [f] using hmiss (L, true)).symm
        · exact (show b L ≠ v by simpa [f] using hmiss (L, false)).symm
      · obtain ⟨w, c, hc, rfl⟩ := hC K hKC
        exact cycle_neighbor_ncard_even hc v
    exact (Nat.not_even_iff_odd.mpr (ho v)) hEven
  have hle : Fintype.card V ≤ 2*P.card := by
    simpa [Nat.mul_comm] using Fintype.card_le_of_surjective f hs
  have hC0 : C = ∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨⟨hP, ?_⟩, hC0, by omega⟩
  simpa [hC0] using hD

/-- A normal trail system records explicit endpoints, rather than counting
members with local degree one. The endpoint pairing is part of the data and
may change when comparing two systems. -/
structure NormalTrailSystem {V : Type*} (G : SimpleGraph V) (k : ℕ) where
  start : Fin k → V
  finish : Fin k → V
  walk : ∀ i, G.Walk (start i) (finish i)
  isTrail : ∀ i, (walk i).IsTrail
  endpoint_bijective : Function.Bijective (fun x : Fin k × Bool ↦
    if x.2 then start x.1 else finish x.1)
  disjoint : Pairwise fun i j ↦ Disjoint (walk i).toSubgraph.edgeSet (walk j).toSubgraph.edgeSet
  cover : ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (walk i).toSubgraph.edgeSet

lemma all_odd_normal_trail_system {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ho : ∀ v, Odd (G.degree v)) :
    ∃ k : ℕ, 2*k = Fintype.card V ∧ Nonempty (NormalTrailSystem G k) := by
  obtain ⟨k, hk, a, b, p, hp, he, hd, hc⟩ := all_odd_normal_trail_partition G ho
  exact ⟨k, hk, ⟨⟨a, b, p, hp, he, hd, hc⟩⟩⟩

namespace NormalTrailSystem

lemma endpoints_ne {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) : T.start i ≠ T.finish i := by
  intro hi
  have hh := T.endpoint_bijective.1 (show
    (if (i, true).2 then T.start (i, true).1 else T.finish (i, true).1) =
    (if (i, false).2 then T.start (i, false).1 else T.finish (i, false).1) by simpa using hi)
  have := congrArg Prod.snd hh
  contradiction

lemma twice_card {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : 2*k = Fintype.card V := by
  simpa [Nat.mul_comm] using Fintype.card_of_bijective T.endpoint_bijective

/-- Total distinct vertex incidences among the trails. -/
noncomputable def score {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : ℕ :=
  ∑ i, (T.walk i).toSubgraph.verts.ncard

lemma score_le {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : T.score ≤ k * Fintype.card V := by
  unfold score
  calc
    ∑ i, (T.walk i).toSubgraph.verts.ncard ≤ ∑ _i : Fin k, Fintype.card V := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Nat.card_eq_fintype_card] using Set.ncard_le_card (T.walk i).toSubgraph.verts
    _ = _ := by simp

/-- The global incidence optimization has a maximum. This does not assert
that a maximizing system consists of simple paths. -/
lemma exists_max_score {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) :
    ∃ S : NormalTrailSystem G k, ∀ R : NormalTrailSystem G k, R.score ≤ S.score := by
  classical
  let P (m : ℕ) := ∃ S : NormalTrailSystem G k, S.score = m
  have hm : P (Nat.findGreatest P (k * Fintype.card V)) :=
    Nat.findGreatest_spec T.score_le ⟨T, rfl⟩
  obtain ⟨S, hS⟩ := hm
  refine ⟨S, fun R ↦ ?_⟩
  rw [hS]
  exact Nat.le_findGreatest R.score_le ⟨R, rfl⟩

lemma sum_length {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : ∑ i, (T.walk i).length = G.edgeSet.ncard := by
  classical
  let E (i : Fin k) : Finset (Sym2 V) := (T.walk i).edges.toFinset
  have hE : Finset.univ.biUnion E = G.edgeFinset := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_edgeFinset]
    simpa only [E, List.mem_toFinset, Walk.mem_edges_toSubgraph] using (T.cover e).symm
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) E := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hi hj
    exact Set.disjoint_left.mp (T.disjoint hij)
      ((T.walk i).mem_edges_toSubgraph.mpr (List.mem_toFinset.mp hi))
      ((T.walk j).mem_edges_toSubgraph.mpr (List.mem_toFinset.mp hj))
  have hcard (i : Fin k) : (E i).card = (T.walk i).length := by
    change (T.walk i).edges.toFinset.card = (T.walk i).length
    rw [List.toFinset_card_of_nodup (T.isTrail i).edges_nodup, Walk.length_edges]
  calc
    ∑ i, (T.walk i).length = ∑ i, (E i).card := by simp only [hcard]
    _ = (Finset.univ.biUnion E).card := (Finset.card_biUnion hdis).symm
    _ = G.edgeSet.ncard := by rw [hE, ← Set.ncard_coe_finset, coe_edgeFinset]

lemma vertex_incidence_le {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) :
    (T.walk i).toSubgraph.verts.ncard ≤ (T.walk i).length + 1 := by
  classical
  rw [Walk.verts_toSubgraph, ← List.coe_toFinset, Set.ncard_coe_finset]
  simpa only [Walk.length_support] using (T.walk i).support.toFinset_card_le

lemma vertex_incidence_eq_iff {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (i : Fin k) :
    (T.walk i).toSubgraph.verts.ncard = (T.walk i).length + 1 ↔ (T.walk i).IsPath := by
  classical
  rw [Walk.verts_toSubgraph, ← List.coe_toFinset, Set.ncard_coe_finset, ← Walk.length_support]
  simpa only [List.toFinset_coe, Multiset.coe_card, Multiset.coe_nodup, Walk.isPath_def] using
    (Multiset.toFinset_card_eq_card_iff_nodup (m := ((T.walk i).support : Multiset V)))

lemma score_le_edges_add {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : T.score ≤ G.edgeSet.ncard + k := by
  calc
    T.score ≤ ∑ i, ((T.walk i).length + 1) :=
      Finset.sum_le_sum (fun i _ ↦ T.vertex_incidence_le i)
    _ = _ := by rw [Finset.sum_add_distrib, T.sum_length]; simp

/-- The deficit in total distinct vertex incidences is exactly the obstruction
to this particular normal trail system being a simple-path system. -/
lemma score_eq_edges_add_iff {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) : T.score = G.edgeSet.ncard + k ↔
      ∀ i, (T.walk i).IsPath := by
  have he : G.edgeSet.ncard + k = ∑ i, ((T.walk i).length + 1) := by
    rw [Finset.sum_add_distrib, T.sum_length]; simp
  rw [he, score, Finset.sum_eq_sum_iff_of_le (fun i _ ↦ T.vertex_incidence_le i)]
  simp only [Finset.mem_univ, true_implies, T.vertex_incidence_eq_iff]

lemma path_decomposition {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card = k := by
  classical
  let f (i : Fin k) := (T.walk i).toSubgraph
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hnotnil : ¬(T.walk i).Nil := Walk.not_nil_of_ne (T.endpoints_ne i)
    have he : s(T.start i, (T.walk i).snd) ∈ (f i).edgeSet :=
      (T.walk i).toSubgraph_adj_snd hnotnil
    have hej : s(T.start i, (T.walk i).snd) ∈ (f j).edgeSet := by rw [← hij]; exact he
    exact Set.disjoint_left.mp (T.disjoint hne) he hej
  refine ⟨Finset.univ.image f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro H hH
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    exact ⟨T.start i, T.finish i, T.walk i, hp i, rfl⟩
  · intro H hH K hK hHK
    change H ∈ Finset.univ.image f at hH
    change K ∈ Finset.univ.image f at hK
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hK
    exact T.disjoint (fun hh ↦ hHK (congrArg f hh))
  · ext e
    simp only [Set.mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨H, ⟨i, rfl⟩, he⟩
      exact (T.cover e).mpr ⟨i, he⟩
    · intro he
      obtain ⟨i, hi⟩ := (T.cover e).mp he
      exact ⟨f i, ⟨i, rfl⟩, hi⟩
  · rw [Finset.card_image_of_injective _ hf]
    simp


end NormalTrailSystem


/-- Move the first edge of a trail to a second trail starting at its neighbor.
The two starting endpoints are exchanged, and edge-disjointness is preserved.
If the first trail revisits its starting vertex, this never decreases total
vertex incidence; it strictly increases it when the second trail avoids that
vertex. This is only a local move, not a global normalization theorem. -/
lemma trail_endpoint_slide {V : Type*} [Fintype V] {G : SimpleGraph V}
    {v w b c : V} (h : G.Adj v w) (p : G.Walk w b) (q : G.Walk w c)
    (hp : (Walk.cons h p).IsTrail) (hq : q.IsTrail)
    (hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hv : v ∈ p.support) :
    p.IsTrail ∧ (Walk.cons h q).IsTrail ∧
      Disjoint p.toSubgraph.edgeSet (Walk.cons h q).toSubgraph.edgeSet ∧
      ((Walk.cons h p).toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
        p.toSubgraph.edgeSet ∪ (Walk.cons h q).toSubgraph.edgeSet) ∧
      (Walk.cons h p).toSubgraph.verts.ncard + q.toSubgraph.verts.ncard ≤
        p.toSubgraph.verts.ncard + (Walk.cons h q).toSubgraph.verts.ncard ∧
      (v ∉ q.support →
        (Walk.cons h p).toSubgraph.verts.ncard + q.toSubgraph.verts.ncard <
          p.toSubgraph.verts.ncard + (Walk.cons h q).toSubgraph.verts.ncard) := by
  classical
  have hp' := (Walk.isTrail_cons h p).mp hp
  have hnotq : s(v,w) ∉ q.edges := by
    intro he
    exact Set.disjoint_left.mp hd
      ((Walk.cons h p).mem_edges_toSubgraph.mpr (by simp)) (q.mem_edges_toSubgraph.mpr he)
  have hq' : (Walk.cons h q).IsTrail := (Walk.isTrail_cons h q).mpr ⟨hq, hnotq⟩
  have hvp : (Walk.cons h p).toSubgraph.verts = p.toSubgraph.verts := by
    ext x
    simp only [Walk.mem_verts_toSubgraph, Walk.support_cons, List.mem_cons]
    exact or_iff_right_of_imp (fun hx ↦ hx ▸ hv)
  have hvq : (Walk.cons h q).toSubgraph.verts = insert v q.toSubgraph.verts := by
    ext x
    simp only [Walk.mem_verts_toSubgraph, Walk.support_cons, List.mem_cons,
      Set.mem_insert_iff]
  refine ⟨hp'.1, hq', ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e he heq
    have hep := p.mem_edges_toSubgraph.mp he
    have heq' := (Walk.cons h q).mem_edges_toSubgraph.mp heq
    simp only [Walk.edges_cons, List.mem_cons] at heq'
    rcases heq' with rfl | heq'
    · exact hp'.2 hep
    · exact Set.disjoint_left.mp hd
        ((Walk.cons h p).mem_edges_toSubgraph.mpr (by simp [hep]))
        (q.mem_edges_toSubgraph.mpr heq')
  · ext e
    simp only [Set.mem_union, Walk.mem_edges_toSubgraph, Walk.edges_cons, List.mem_cons]
    exact or_assoc.trans or_left_comm
  · rw [hvp, hvq]
    exact Nat.add_le_add_left (Set.ncard_mono (Set.subset_insert _ _)) _
  · intro hnot
    rw [hvp, hvq, Set.ncard_insert_of_notMem (by simpa only [Walk.mem_verts_toSubgraph] using hnot)]
    omega

end Erdos583TrailDevelopment
