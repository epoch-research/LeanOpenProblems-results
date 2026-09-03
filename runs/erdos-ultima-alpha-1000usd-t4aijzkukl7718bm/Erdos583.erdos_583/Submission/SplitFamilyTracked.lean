import Submission.GeneralQuotaPurification

/-! Splitting one member adds one indexed path slot and two endpoints at the
cut vertex. This records endpoint multiplicities even in the presence of nil
members; the subsequent truncation theorem turns them into genuine endpoints. -/
namespace Erdos583SplitFamilyTrackedDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583GeneralQuotaPurificationDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

lemma indexed_path_family_tracked {V I : Type*} [Fintype I] {G : SimpleGraph V}
    (a b : I → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet)
    (hc : ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (p i).toSubgraph.edgeSet) :
    ∃ T : TrailFamily G (Fintype.card I), (∀ i, (T.walk i).IsPath) ∧
      ∀ x, T.quota x=∑ i, ((if a i=x then 1 else 0)+(if b i=x then 1 else 0) : ℕ) := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let T : TrailFamily G (Fintype.card I) :=
    { start := a ∘ e, finish := b ∘ e, walk := fun i ↦ p (e i),
      isTrail := fun i ↦ (hp (e i)).isTrail,
      disjoint := fun _ _ hij ↦ hd (e.injective.ne hij),
      cover := by
        intro d
        rw [hc]
        constructor
        · rintro ⟨i,hi⟩
          refine ⟨e.symm i,?_⟩
          change d ∈ (p (e (e.symm i))).toSubgraph.edgeSet
          exact (congrArg (fun j ↦ d ∈ (p j).toSubgraph.edgeSet) (e.apply_symm_apply i)).mpr hi
        · rintro ⟨i,hi⟩
          exact ⟨e i,hi⟩ }
  refine ⟨T,fun i ↦ hp (e i),?_⟩
  intro x
  rw [quota_eq_sum_endpoints]
  exact e.sum_comp (fun i ↦ ((if a i=x then 1 else 0)+(if b i=x then 1 else 0) : ℕ))

lemma split_family_member {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {x : V}
    (L : G.Walk (T.start i) x) (R : G.Walk x (T.finish i))
    (hL : L.IsPath) (hR : R.IsPath) (hform : T.walk i=L.append R)
    (hp : ∀ j, j ≠ i → (T.walk j).IsPath) :
    ∃ U : TrailFamily G (k+1), (∀ j, (U.walk j).IsPath) ∧
      ∀ v, U.quota v=T.quota v+2*(if x=v then 1 else 0) := by
  classical
  let a : Option (Fin k) → V := fun s ↦ match s with
    | none => T.start i
    | some j => if j=i then x else T.start j
  let b : Option (Fin k) → V := fun s ↦ match s with
    | none => x
    | some j => T.finish j
  let p : ∀ s, G.Walk (a s) (b s) := fun s ↦ match s with
    | none => L
    | some j => if hj : j=i then R.copy (by simp [a,hj]) (by simp [b,hj])
      else (T.walk j).copy (by simp [a,hj]) rfl
  have hpnone : (p none).toSubgraph=L.toSubgraph := rfl
  have hpi : (p (some i)).toSubgraph=R.toSubgraph := by simp [p,NormalTrailSystem.walk_copy_subgraph]
  have hpj (j : Fin k) (hj : j ≠ i) : (p (some j)).toSubgraph=(T.walk j).toSubgraph := by
    simp [p,hj,NormalTrailSystem.walk_copy_subgraph]
  have hleL : L.toSubgraph.edgeSet ⊆ (T.walk i).toSubgraph.edgeSet := by
    rw [hform,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left
  have hleR : R.toSubgraph.edgeSet ⊆ (T.walk i).toSubgraph.edgeSet := by
    rw [hform,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_right
  have hLR := RootedTailSystem.append_trail_disjoint (hform ▸ T.isTrail i)
  have hpaths (s : Option (Fin k)) : (p s).IsPath := by
    cases s with
    | none => exact hL
    | some j =>
      dsimp only [p]
      split_ifs with hj
      · simpa only [Walk.isPath_copy] using hR
      · simpa only [Walk.isPath_copy] using hp j hj
  have hdis : Pairwise fun s t ↦ Disjoint (p s).toSubgraph.edgeSet (p t).toSubgraph.edgeSet := by
    intro s t hst
    cases s with
    | none =>
      cases t with
      | none => exact (hst rfl).elim
      | some j =>
        rw [hpnone]
        by_cases hj : j=i
        · subst j
          rw [hpi]
          exact hLR
        · rw [hpj j hj]
          exact (T.disjoint (Ne.symm hj)).mono_left hleL
    | some j =>
      cases t with
      | none =>
        rw [hpnone]
        by_cases hj : j=i
        · subst j
          rw [hpi]
          exact hLR.symm
        · rw [hpj j hj]
          exact (T.disjoint hj).mono_right hleL
      | some l =>
        have hjl : j ≠ l := fun hh ↦ hst (congrArg some hh)
        by_cases hj : j=i
        · subst j
          rw [hpi,hpj l hjl.symm]
          exact (T.disjoint hjl).mono_left hleR
        · by_cases hl : l=i
          · subst l
            rw [hpj j hj,hpi]
            exact (T.disjoint hj).mono_right hleR
          · rw [hpj j hj,hpj l hl]
            exact T.disjoint hjl
  have hcover (e : Sym2 V) : e ∈ G.edgeSet ↔ ∃ s, e ∈ (p s).toSubgraph.edgeSet := by
    constructor
    · intro he
      obtain ⟨j,hj⟩ := (T.cover e).mp he
      by_cases hji : j=i
      · subst j
        rw [hform,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hj
        rcases hj with hj|hj
        · exact ⟨none,hj⟩
        · exact ⟨some i,by rwa [hpi]⟩
      · exact ⟨some j,by rwa [hpj j hji]⟩
    · rintro ⟨s,hs⟩
      exact (p s).toSubgraph.edgeSet_subset hs
  obtain ⟨U,hU,hUq⟩ := indexed_path_family_tracked a b p hpaths hdis hcover
  have hq (v : V) : U.quota v=T.quota v+2*(if x=v then 1 else 0) := by
    rw [hUq,quota_eq_sum_endpoints]
    rw [Fintype.sum_option]
    change ((if T.start i=v then 1 else 0)+(if x=v then 1 else 0))+
      (∑ j, ((if (if j=i then x else T.start j)=v then 1 else 0)+
        (if T.finish j=v then 1 else 0))) = _
    have hrest : (∑ j ∈ Finset.univ.erase i,
        ((if (if j=i then x else T.start j)=v then 1 else 0)+(if T.finish j=v then 1 else 0))) =
        ∑ j ∈ Finset.univ.erase i,
          ((if T.start j=v then 1 else 0)+(if T.finish j=v then 1 else 0) : ℕ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.mem_erase.mp hj).1]
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i),hrest]
    simp only [↓reduceIte]
    have hh := Finset.add_sum_erase Finset.univ
      (fun j ↦ ((if T.start j=v then 1 else 0)+(if T.finish j=v then 1 else 0) : ℕ))
      (Finset.mem_univ i)
    dsimp only at hh
    omega
  have hh : Fintype.card (Option (Fin k))=k+1 := by simp
  have hex : ∃ U : TrailFamily G (Fintype.card (Option (Fin k))),
      (∀ j, (U.walk j).IsPath) ∧ ∀ v, U.quota v=T.quota v+2*(if x=v then 1 else 0) :=
    ⟨U,hU,hq⟩
  exact hh ▸ hex

lemma one_defect_path_family_preserves_lower_quotas {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : G.edgeSet.ncard+k ≤ T.score+1) :
    ∃ l ≤ k+1, ∃ U : TrailFamily G l, (∀ i, (U.walk i).IsPath) ∧
      ∀ v, T.quota v ≤ U.quota v := by
  classical
  by_cases hp : ∀ i, (T.walk i).IsPath
  · exact ⟨k,by omega,T,hp,fun _ ↦ le_rfl⟩
  obtain ⟨i,hi⟩ := not_forall.mp hp
  have hs' : T.score+1=G.edgeSet.ncard+k := by
    have hle := T.score_le_edges_add
    have hne : T.score ≠ G.edgeSet.ncard+k := fun hh ↦ hi (T.score_eq_edges_add_iff.mp hh i)
    omega
  obtain ⟨hdef,hother⟩ := T.one_defect_other_paths hs' i hi
  have hc : (T.walk i).toSubgraph.verts.ncard=(T.walk i).length := by
    have hh := T.defect_add_vertices i
    omega
  obtain ⟨x,L,R,hform,hinter⟩ := NilSlot.nonpath_cut (T.walk i) hi
  have hcard := Set.ncard_union_add_ncard_inter L.toSubgraph.verts R.toSubgraph.verts
  have hvl := walk_vertex_ncard_le L
  have hvr := walk_vertex_ncard_le R
  have hu : (L.toSubgraph.verts ∪ R.toSubgraph.verts).ncard=L.length+R.length := by
    simpa only [hform,Walk.toSubgraph_append,Subgraph.verts_sup,Walk.length_append] using hc
  rw [hu] at hcard
  have hL : L.IsPath := (walk_vertex_ncard_eq_iff L).mp (by omega)
  have hR : R.IsPath := (walk_vertex_ncard_eq_iff R).mp (by omega)
  obtain ⟨U,hU,hUq⟩ := split_family_member T i L R hL hR hform hother
  exact ⟨k+1,le_rfl,U,hU,fun v ↦ by rw [hUq]; omega⟩

lemma one_defect_marked_partition {V : Type*} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k)
    (hs : G.edgeSet.ncard+k ≤ T.score+1) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k+1 ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧
      ∀ v, min (T.quota v) (Nat.card (G.neighborSet v)) ≤ endpointMultiplicity D v := by
  obtain ⟨l,hl,U,hU,hUq⟩ := one_defect_path_family_preserves_lower_quotas T hs
  obtain ⟨D,hD,hDc,hDn,hDq⟩ := path_family_partition_truncated_quota U hU
  refine ⟨D,hD,hDc.trans hl,hDn,?_⟩
  intro v
  rw [hDq]
  exact min_le_min (hUq v) le_rfl

end Erdos583SplitFamilyTrackedDevelopment
