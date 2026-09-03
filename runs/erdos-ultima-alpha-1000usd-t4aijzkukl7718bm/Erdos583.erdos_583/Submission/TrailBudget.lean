import Submission.Work

/-! Trail partitions within the Gallai member budget, without simplicity. -/
open SimpleGraph Erdos583Work
open Erdos583Work.RootedTailSystem Erdos583Work.QuotaTrails
namespace Erdos583TrailBudgetDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma splice_closed_at_vertex {V : Type*} {G : SimpleGraph V} {a b v : V}
    (p : G.Walk a b) (c : G.Walk v v) (hp : p.IsTrail) (hc : c.IsTrail)
    (hv : v ∈ p.support) (hd : Disjoint p.toSubgraph.edgeSet c.toSubgraph.edgeSet) :
    ∃ q : G.Walk a b, q.IsTrail ∧ q.toSubgraph=p.toSubgraph ⊔ c.toSubgraph := by
  classical
  let A := p.takeUntil v hv
  let B := p.dropUntil v hv
  have hAB : A.append B=p := p.take_spec hv
  have hp' : (A.append B).IsTrail := hAB.symm ▸ hp
  have hdis := append_trail_disjoint hp'
  have hdc : Disjoint (A.toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet) c.toSubgraph.edgeSet := by
    rw [←Subgraph.edgeSet_sup,←Walk.toSubgraph_append,hAB]
    exact hd
  have hcb := trail_append_of_disjoint hc hp'.of_append_right (disjoint_sup_left.mp hdc).2.symm
  have hacb : Disjoint A.toSubgraph.edgeSet (c.append B).toSubgraph.edgeSet := by
    rw [Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact disjoint_sup_right.mpr ⟨(disjoint_sup_left.mp hdc).1,hdis⟩
  refine ⟨A.append (c.append B),trail_append_of_disjoint hp'.of_append_left hcb hacb,?_⟩
  rw [←hAB,Walk.toSubgraph_append,Walk.toSubgraph_append,Walk.toSubgraph_append]
  simp only [sup_assoc,sup_comm]

lemma extend_trail_family_at_vertex {V I : Type*} {G : SimpleGraph V}
    {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsTrail)
    (hpp : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet)
    {v : V} (c : G.Walk v v) (hc : c.IsTrail)
    (hpc : ∀ i, Disjoint (p i).toSubgraph.edgeSet c.toSubgraph.edgeSet)
    (i : I) (hi : v ∈ (p i).support) :
    ∃ q : ∀ j, G.Walk (a j) (b j),
      (∀ j, (q j).IsTrail) ∧
      (Pairwise fun j k ↦ Disjoint (q j).toSubgraph.edgeSet (q k).toSubgraph.edgeSet) ∧
      (∀ e, (∃ j, e ∈ (q j).toSubgraph.edgeSet) ↔
        (∃ j, e ∈ (p j).toSubgraph.edgeSet) ∨ e ∈ c.toSubgraph.edgeSet) := by
  classical
  obtain ⟨r,hr,hre⟩ := splice_closed_at_vertex (p i) c (hp i) hc hi (hpc i)
  let q := Function.update p i r
  have hqi : q i=r := by simp [q]
  have hqj (j : I) (hj : j ≠ i) : q j=p j := by simp [q,hj]
  have hqe : (q i).toSubgraph.edgeSet=(p i).toSubgraph.edgeSet ∪ c.toSubgraph.edgeSet := by
    rw [hqi,hre,Subgraph.edgeSet_sup]
  refine ⟨q,?_,?_,?_⟩
  · intro j
    by_cases hj : j=i
    · subst j; simpa [hqi] using hr
    · simpa [hqj j hj] using hp j
  · intro j k hjk
    by_cases hj : j=i
    · subst j
      rw [hqe,hqj k hjk.symm]
      exact disjoint_sup_left.mpr ⟨hpp hjk,(hpc k).symm⟩
    · by_cases hk : k=i
      · subst k
        rw [hqj j hj,hqe]
        exact disjoint_sup_right.mpr ⟨hpp hjk,hpc j⟩
      · rw [hqj j hj,hqj k hk]
        exact hpp hjk
  · intro e
    constructor
    · rintro ⟨j,hj⟩
      by_cases hji : j=i
      · subst j
        rw [hqe] at hj
        exact hj.elim (fun h ↦ Or.inl ⟨i,h⟩) Or.inr
      · exact Or.inl ⟨j,by simpa only [hqj j hji] using hj⟩
    · rintro (⟨j,hj⟩|he)
      · by_cases hji : j=i
        · subst j
          exact ⟨i,hqe.symm ▸ Or.inl hj⟩
        · exact ⟨j,by simpa only [hqj j hji] using hj⟩
      · exact ⟨i,hqe.symm ▸ Or.inr he⟩

lemma connected_closed_set {V : Type*} {G : SimpleGraph V} (hG : G.Connected)
    (S : Set V) (hS : S.Nonempty)
    (hclosed : ∀ ⦃x y⦄, G.Adj x y → x ∈ S → y ∈ S) : S=Set.univ := by
  obtain ⟨x,hx⟩ := hS
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨p⟩ := hG.preconnected x y
  have reach {u v : V} (p : G.Walk u v) : u ∈ S → v ∈ S := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hu ↦ ih (hclosed h hu)
  exact reach p hx

lemma cycle_meets_trail {V I : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {a b : I → V} (p : ∀ i, G.Walk (a i) (b i)) (i₀ : I)
    (C : Finset G.Subgraph) (hCn : C.Nonempty) (hC : ∀ K ∈ C, IsCycleSubgraph K)
    (hcover : ∀ e, e ∈ G.edgeSet ↔
      (∃ i, e ∈ (p i).toSubgraph.edgeSet) ∨ ∃ K ∈ C, e ∈ K.edgeSet) :
    ∃ K ∈ C, ∃ i v, v ∈ (p i).support ∧ v ∈ K.verts := by
  classical
  by_contra hn
  have hno (K) (hK : K ∈ C) (i) (v) (hv : v ∈ (p i).support) : v ∉ K.verts := by
    intro hh
    exact hn ⟨K,hK,i,v,hv,hh⟩
  let S : Set V := {v | ∃ i, v ∈ (p i).support}
  have hS : S=Set.univ := connected_closed_set hG S ⟨a i₀,i₀,(p i₀).start_mem_support⟩ (by
    intro x y hxy hx
    obtain ⟨i,hxi⟩ := hx
    rcases (hcover s(x,y)).mp hxy with ⟨j,hj⟩ | ⟨K,hK,heK⟩
    · exact ⟨j,(p j).snd_mem_support_of_mem_edges ((p j).mem_edges_toSubgraph.mp hj)⟩
    · exact (hno K hK i x hxi (K.edge_vert heK)).elim)
  obtain ⟨K,hK⟩ := hCn
  obtain ⟨v,c,_,rfl⟩ := hC K hK
  have hv : v ∈ S := by rw [hS]; trivial
  obtain ⟨i,hi⟩ := hv
  exact hno _ hK i v hi c.start_mem_verts_toSubgraph

lemma absorb_cycles_connected {V I : Type*} {G : SimpleGraph V} (hG : G.Connected)
    {a b : I → V} (i₀ : I) (C : Finset G.Subgraph)
    (hC : ∀ K ∈ C, IsCycleSubgraph K)
    (hCC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun K ↦ K.edgeSet))
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsTrail)
    (hpp : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet)
    (hpc : ∀ i K, K ∈ C → Disjoint (p i).toSubgraph.edgeSet K.edgeSet)
    (hcover : ∀ e, e ∈ G.edgeSet ↔
      (∃ i, e ∈ (p i).toSubgraph.edgeSet) ∨ ∃ K ∈ C, e ∈ K.edgeSet) :
    ∃ q : ∀ i, G.Walk (a i) (b i), (∀ i, (q i).IsTrail) ∧
      (Pairwise fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet) ∧
      ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (q i).toSubgraph.edgeSet := by
  classical
  induction C using Finset.strongInductionOn generalizing p with
  | _ C ih =>
    by_cases hCn : C.Nonempty
    · obtain ⟨K,hK,i,v,hvi,hvK⟩ := cycle_meets_trail hG p i₀ C hCn hC hcover
      obtain ⟨u,c,hc,rfl⟩ := hC K hK
      have hvc : v ∈ c.support := c.mem_verts_toSubgraph.mp hvK
      let d := c.rotate hvc
      have hd : d.toSubgraph=c.toSubgraph := Walk.toSubgraph_rotate c hvc
      have hdt : d.IsTrail := hc.isTrail.rotate hvc
      obtain ⟨q,hq,hqq,hqe⟩ := extend_trail_family_at_vertex p hp hpp d hdt
        (fun j ↦ by rw [hd]; exact hpc j _ hK) i hvi
      have hqpc : ∀ j L, L ∈ C.erase c.toSubgraph → Disjoint (q j).toSubgraph.edgeSet L.edgeSet := by
        intro j L hL
        obtain ⟨hLne,hLC⟩ := Finset.mem_erase.mp hL
        apply Set.disjoint_left.mpr
        intro e he heL
        rcases (hqe e).mp ⟨j,he⟩ with ⟨l,hl⟩ | he
        · exact Set.disjoint_left.mp (hpc l L hLC) hl heL
        · rw [hd] at he
          exact Set.disjoint_left.mp (hCC hK hLC hLne.symm) he heL
      apply ih (C.erase c.toSubgraph) (Finset.erase_ssubset hK)
        (fun L hL ↦ hC L (Finset.mem_of_mem_erase hL))
        (hCC.subset (by intro L hL; exact Finset.mem_of_mem_erase hL)) q hq hqq hqpc
      intro e
      rw [hcover,hqe,hd]
      constructor
      · rintro (he|⟨L,hL,heL⟩)
        · exact Or.inl (Or.inl he)
        · by_cases hLe : L=c.toSubgraph
          · subst L; exact Or.inl (Or.inr heL)
          · exact Or.inr ⟨L,Finset.mem_erase.mpr ⟨hLe,hL⟩,heL⟩
      · rintro ((he|he)|⟨L,hL,heL⟩)
        · exact Or.inl he
        · exact Or.inr ⟨_,hK,he⟩
        · exact Or.inr ⟨L,Finset.mem_of_mem_erase hL,heL⟩
    · have he : C=∅ := Finset.not_nonempty_iff_eq_empty.mp hCn
      exact ⟨p,hp,hpp,by simpa only [he,Finset.notMem_empty,false_and,exists_const,or_false] using hcover⟩


lemma indexed_trail_family {V I : Type*} [Fintype I] {G : SimpleGraph V}
    (a b : I → V) (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet)
    (hc : ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (p i).toSubgraph.edgeSet) :
    Nonempty (TrailFamily G (Fintype.card I)) := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨⟨a ∘ e,b ∘ e,fun i ↦ p (e i),fun i ↦ hp (e i),?_,?_⟩⟩
  · intro i j hij
    exact hd (fun h ↦ hij (e.injective h))
  · intro d
    rw [hc]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨e.symm i,?_⟩
      change d ∈ (p (e (e.symm i))).toSubgraph.edgeSet
      rw [e.apply_symm_apply]
      exact hi
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩

/-- Connectivity suffices for a trail partition within the target count.
These trails may repeat vertices; this is not the path-decomposition theorem. -/
lemma exists_bounded_trail_family {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) :
    ∃ k : ℕ, k ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ ∧ Nonempty (TrailFamily G k) := by
  classical
  obtain ⟨P,C,hP,hC,hD,hPC,_,hcard⟩ := normal_path_cycle_decomposition G
  have hCC : Set.PairwiseDisjoint (C : Set G.Subgraph) (fun K ↦ K.edgeSet) :=
    hD.1.subset (by intro K hK; exact Finset.mem_union_right _ hK)
  have hcover (e : Sym2 V) : e ∈ G.edgeSet ↔
      (∃ K ∈ P, e ∈ K.edgeSet) ∨ ∃ K ∈ C, e ∈ K.edgeSet := by
    rw [←hD.2]
    simp only [Set.mem_iUnion,Finset.mem_union]
    constructor
    · rintro ⟨K,(hK|hK),he⟩
      · exact Or.inl ⟨K,hK,he⟩
      · exact Or.inr ⟨K,hK,he⟩
    · rintro (⟨K,hK,he⟩|⟨K,hK,he⟩)
      · exact ⟨K,Or.inl hK,he⟩
      · exact ⟨K,Or.inr hK,he⟩
  by_cases hPn : P.Nonempty
  · choose a b p hp he using fun K : P ↦ (hP K.val K.property).1
    obtain ⟨K,hK⟩ := hPn
    have hpp : Pairwise fun i j : P ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet := by
      intro i j hij
      rw [←he,←he]
      exact hD.1 (Finset.mem_union_left _ i.property) (Finset.mem_union_left _ j.property)
        (fun h ↦ hij (Subtype.ext h))
    have hpc : ∀ i : P, ∀ K ∈ C, Disjoint (p i).toSubgraph.edgeSet K.edgeSet := by
      intro i K hK
      rw [←he]
      exact hD.1 (Finset.mem_union_left _ i.property) (Finset.mem_union_right _ hK)
        (fun h ↦ Finset.disjoint_left.mp hPC (h ▸ i.property) hK)
    obtain ⟨q,hq,hqq,hqc⟩ := absorb_cycles_connected hG (⟨K,hK⟩ : P) C hC hCC p
      (fun i ↦ (hp i).isTrail) hpp hpc (by
        intro e
        rw [hcover]
        apply or_congr_left
        constructor
        · rintro ⟨K,hK,heK⟩
          exact ⟨⟨K,hK⟩,by rw [←he]; exact heK⟩
        · rintro ⟨i,hi⟩
          exact ⟨i.val,i.property,by rw [he]; exact hi⟩)
    refine ⟨Fintype.card P,?_,indexed_trail_family a b q hq hqq hqc⟩
    have hsub := Fintype.card_subtype_le (fun v ↦ Odd (G.degree v))
    have hc := Nat.le_ceil ((Fintype.card V : ℚ)/2)
    rw [Fintype.card_coe]
    exact_mod_cast (show (P.card : ℚ) ≤ (⌈(Fintype.card V : ℚ)/2⌉₊ : ℚ) by
      have hh : 2*(P.card : ℚ) ≤ Fintype.card V := by exact_mod_cast hcard.le.trans hsub
      linarith)
  · have hP0 : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hPn
    letI : Nonempty V := hG.nonempty
    let v : V := Classical.arbitrary V
    let p (_i : Fin 1) : G.Walk v v := Walk.nil
    obtain ⟨q,hq,hqq,hqc⟩ := absorb_cycles_connected hG (0 : Fin 1) C hC hCC p
      (by intro i; exact Walk.IsTrail.nil) (by intro i j hij; simp [p])
      (by intro i K hK; simp [p]) (by intro e; simpa [hP0,p] using hcover e)
    refine ⟨1,?_,?_⟩
    · apply Nat.succ_le_of_lt
      apply Nat.ceil_pos.mpr
      have hn : 0 < Fintype.card V := Fintype.card_pos
      exact div_pos (by exact_mod_cast hn) (by norm_num)
    · simpa only [Fintype.card_fin] using indexed_trail_family (fun _ : Fin 1 ↦ v) (fun _ ↦ v) q hq hqq hqc


lemma pad_trail_family {V : Type*} {G : SimpleGraph V} {k m : ℕ}
    (T : TrailFamily G k) (hkm : k ≤ m) (v : V) : Nonempty (TrailFamily G m) := by
  classical
  let I := Fin k ⊕ Fin (m-k)
  let a : I → V := Sum.elim T.start (fun _ ↦ v)
  let b : I → V := Sum.elim T.finish (fun _ ↦ v)
  let p : ∀ i : I, G.Walk (a i) (b i) := fun i ↦ match i with
    | .inl j => T.walk j
    | .inr _ => Walk.nil
  have hp : ∀ i, (p i).IsTrail := by
    rintro (i|i)
    · exact T.isTrail i
    · exact Walk.IsTrail.nil
  have hd : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet := by
    rintro (i|i) (j|j) hij
    · exact T.disjoint (fun h ↦ hij (congrArg Sum.inl h))
    · simp [p]
    · simp [p]
    · simp [p]
  have hc : ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (p i).toSubgraph.edgeSet := by
    intro e
    constructor
    · intro he
      obtain ⟨i,hi⟩ := (T.cover e).mp he
      exact ⟨Sum.inl i,hi⟩
    · rintro ⟨(i|i),hi⟩
      · exact (T.cover e).mpr ⟨i,hi⟩
      · simp [p] at hi
  have hcard : Fintype.card I=m := by simp only [I,Fintype.card_sum,Fintype.card_fin]; omega
  have hh := indexed_trail_family a b p hp hd hc
  rwa [hcard] at hh

/-- There is always a global incidence maximum at precisely the conjectured
member budget. The unresolved issue is whether its members are simple paths. -/
lemma exists_budget_maximum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) :
    ∃ T : TrailFamily G ⌈(Fintype.card V : ℚ)/2⌉₊,
      ∀ U : TrailFamily G ⌈(Fintype.card V : ℚ)/2⌉₊, U.score ≤ T.score := by
  obtain ⟨k,hk,⟨T⟩⟩ := exists_bounded_trail_family G hG
  letI : Nonempty V := hG.nonempty
  obtain ⟨S⟩ := pad_trail_family T hk (Classical.arbitrary V)
  exact S.exists_max_score

end Erdos583TrailBudgetDevelopment
