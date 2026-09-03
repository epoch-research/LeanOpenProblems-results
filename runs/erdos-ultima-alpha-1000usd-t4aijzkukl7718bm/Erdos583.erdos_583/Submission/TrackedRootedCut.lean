import Submission.Work

/-! Rooted-cut rebuilding with explicit tail-vertex and outside-member
tracking. No normalization theorem is asserted. -/
namespace Erdos583TrackedRootedCutDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted
open Erdos583Work.DistinctTails Erdos583Work.RootedTailSystem
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma RootedCut.rebuild_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (σ : Equiv.Perm (Fin k × Bool)) (hfix : ∀ s, s.1 ∉ A → σ s = s)
    (q : ∀ s : {s : Fin k × Bool // s.1 ∈ A}, G.Walk (T.endpoint (σ s.val)) r)
    (hq : ∀ s, (q s).IsTrail)
    (hqq : Pairwise fun s t ↦ Disjoint (q s).toSubgraph.edgeSet (q t).toSubgraph.edgeSet)
    (hU : ∀ e, (∃ s, e ∈ (q s).toSubgraph.edgeSet) ↔
      ∃ s, e ∈ (R.tail s).toSubgraph.edgeSet)
    (hV : ∀ s, (q s).toSubgraph.verts = (R.tail s).toSubgraph.verts) :
    ∃ S : TrailFamily G k, S.score = T.score ∧ (∀ v, S.quota v = T.quota v) ∧
      (∀ s, S.endpoint s = T.endpoint (σ s)) ∧
      ∃ Q : RootedCut S r A,
        (∀ s, (Q.tail s).toSubgraph = (q s).toSubgraph) ∧
        (∀ i, (S.walk i).toSubgraph.verts=(T.walk i).toSubgraph.verts) ∧
        (∀ i, i ∉ A → (S.walk i).toSubgraph=(T.walk i).toSubgraph) := by
  classical
  let a (i : Fin k) := T.endpoint (σ (i,true))
  let b (i : Fin k) := T.endpoint (σ (i,false))
  have hp (i : Fin k) : ∃ p : G.Walk (a i) (b i), p.IsTrail ∧
      (∀ hi : i ∈ A, p.toSubgraph = (q ⟨(i,true),hi⟩).toSubgraph ⊔
        (q ⟨(i,false),hi⟩).toSubgraph) ∧
      (i ∉ A → p.toSubgraph = (T.walk i).toSubgraph) := by
    by_cases hi : i ∈ A
    · refine ⟨(q ⟨(i,true),hi⟩).append (q ⟨(i,false),hi⟩).reverse, ?_, ?_, ?_⟩
      · exact trail_append_of_disjoint (hq _) (hq _).reverse (by
          simpa using hqq (show (⟨(i,true),hi⟩ : {s : Fin k × Bool // s.1 ∈ A}) ≠
            ⟨(i,false),hi⟩ by intro h; have := congrArg (fun s ↦ s.val.2) h; contradiction))
      · intro _; simp
      · exact fun hn ↦ (hn hi).elim
    · have ha : a i = T.start i := by simp only [a,hfix (i,true) hi,TrailFamily.endpoint]; rfl
      have hb : b i = T.finish i := by simp only [b,hfix (i,false) hi,TrailFamily.endpoint]; rfl
      exact ⟨(T.walk i).copy ha.symm hb.symm, by simpa using T.isTrail i,
        fun hh ↦ (hi hh).elim, fun _ ↦ NormalTrailSystem.walk_copy_subgraph _ _ _⟩
  choose p hp hpA hpO using hp
  have hcross (s : {s : Fin k × Bool // s.1 ∈ A}) (i : Fin k) (hi : i ∉ A) :
      Disjoint (q s).toSubgraph.edgeSet (p i).toSubgraph.edgeSet := by
    rw [hpO i hi]
    apply Set.disjoint_left.mpr
    intro e he hei
    obtain ⟨t,ht⟩ := (hU e).mp ⟨s,he⟩
    have hti : t.val.1 ≠ i := fun hh ↦ hi (hh ▸ t.property)
    exact Set.disjoint_left.mp (T.disjoint hti)
      (Subgraph.edgeSet_mono (R.tail_in_member t) ht) hei
  have hdis : Pairwise fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet := by
    intro i j hij
    by_cases hi : i ∈ A
    · rw [hpA i hi,Subgraph.edgeSet_sup]
      by_cases hj : j ∈ A
      · rw [hpA j hj,Subgraph.edgeSet_sup]
        apply disjoint_sup_left.mpr
        constructor <;> apply disjoint_sup_right.mpr
        all_goals
          constructor <;> apply hqq <;>
            intro hh <;> exact hij (congrArg (fun s ↦ s.val.1) hh)
      · exact disjoint_sup_left.mpr ⟨hcross _ j hj,(hcross _ j hj)⟩
    · by_cases hj : j ∈ A
      · rw [hpA j hj,Subgraph.edgeSet_sup]
        exact disjoint_sup_right.mpr ⟨(hcross _ i hi).symm,(hcross _ i hi).symm⟩
      · rw [hpO i hi,hpO j hj]; exact T.disjoint hij
  have hqmember (s : {s : Fin k × Bool // s.1 ∈ A}) :
      (q s).toSubgraph ≤ (p s.val.1).toSubgraph := by
    rw [hpA _ s.property]
    rcases s with ⟨⟨i,c⟩,hi⟩
    cases c
    · exact le_sup_right
    · exact le_sup_left
  have hcov : ∀ e, e ∈ G.edgeSet ↔ ∃ i, e ∈ (p i).toSubgraph.edgeSet := by
    intro e
    constructor
    · intro he
      obtain ⟨i,hi⟩ := (T.cover e).mp he
      by_cases hiA : i ∈ A
      · rw [R.decomp i hiA,Subgraph.edgeSet_sup] at hi
        have htail : ∃ s, e ∈ (R.tail s).toSubgraph.edgeSet :=
          hi.elim (fun hh ↦ ⟨⟨(i,true),hiA⟩,hh⟩) (fun hh ↦ ⟨⟨(i,false),hiA⟩,hh⟩)
        obtain ⟨s,hs⟩ := (hU e).mpr htail
        exact ⟨s.val.1,Subgraph.edgeSet_mono (hqmember s) hs⟩
      · exact ⟨i,by rw [hpO i hiA]; exact hi⟩
    · rintro ⟨i,hi⟩
      exact (p i).toSubgraph.edgeSet_subset hi
  let S : TrailFamily G k := ⟨a,b,p,hp,hdis,hcov⟩
  have hends (s : Fin k × Bool) : S.endpoint s = T.endpoint (σ s) := by
    rcases s with ⟨i,c⟩
    cases c <;> rfl
  have hv (i : Fin k) : (p i).toSubgraph.verts = (T.walk i).toSubgraph.verts := by
    by_cases hi : i ∈ A
    · rw [hpA i hi,R.decomp i hi]
      change (q ⟨(i,true),hi⟩).toSubgraph.verts ∪ (q ⟨(i,false),hi⟩).toSubgraph.verts =
        (R.tail ⟨(i,true),hi⟩).toSubgraph.verts ∪ (R.tail ⟨(i,false),hi⟩).toSubgraph.verts
      rw [hV,hV]
    · rw [hpO i hi]
  have hscore : S.score = T.score := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg Set.ncard (hv i)
  let q' (s : {s : Fin k × Bool // s.1 ∈ A}) : G.Walk (S.endpoint s.val) r :=
    (q s).copy (hends s.val).symm rfl
  have hq'e (s) : (q' s).toSubgraph = (q s).toSubgraph :=
    NormalTrailSystem.walk_copy_subgraph _ _ _
  let Q : RootedCut S r A :=
    { tail := q',
      trail := fun s ↦ by simpa only [q',Walk.isTrail_copy] using hq s,
      disjoint := by intro s t hst; rw [hq'e,hq'e]; exact hqq hst,
      decomp := by intro i hi; rw [hq'e,hq'e]; exact hpA i hi,
      outside := by
        intro i hi
        rw [← Walk.mem_verts_toSubgraph]
        change r ∉ (p i).toSubgraph.verts
        rw [hpO i hi,Walk.mem_verts_toSubgraph]
        exact R.outside i hi }
  exact ⟨S,hscore,S.quota_eq_of_endpoint_perm T σ hends,hends,Q,hq'e,hv,hpO⟩

lemma RootedCut.rebuild_selected_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (B : Finset V) (hr : r ∈ B)
    (ι : B ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hlabel : ∀ w, T.endpoint (ι w).val = w.val)
    (hn : ¬(R.tail (ι ⟨r,hr⟩)).Nil)
    (F : DistinctTails.TailFamily G r B)
    (hF : Rearranged F (R.selected B hr ι hlabel hn)) :
    ∃ U : TrailFamily G k, U.score = T.score ∧ (∀ v, U.quota v = T.quota v) ∧
      (∀ x, (∃ s : {s : Fin k × Bool // s.1 ∈ A}, U.endpoint s.val = x) ↔
        ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val = x) ∧
      ∃ Q : RootedCut U r A,
        (∀ s, (Q.tail s).toSubgraph.verts=(R.tail s).toSubgraph.verts) ∧
        (∀ i, i ∉ A → (U.walk i).toSubgraph=(T.walk i).toSubgraph) ∧
        ∃ e : B ≃ B,
          (∀ w, U.endpoint (ι w).val=(e w).val) ∧
          (∀ w, (Q.tail (ι w)).toSubgraph=(F.tail (e w)).toSubgraph) ∧
          (∀ s, s ∉ Set.range ι → (Q.tail s).toSubgraph=(R.tail s).toSubgraph) ∧
          (∀ s, s ∉ Set.range ι → U.endpoint s.val=T.endpoint s.val) := by
  classical
  obtain ⟨e,hverts,hcover⟩ := hF
  let j : B ↪ (Fin k × Bool) :=
    ⟨fun w ↦ (ι w).val, Subtype.val_injective.comp ι.injective⟩
  let σ := Equiv.Perm.viaEmbedding e j
  have hsig (w : B) : σ (ι w).val = (ι (e w)).val := Equiv.Perm.viaEmbedding_apply e j w
  have hfix (s : Fin k × Bool) (hs : s.1 ∉ A) : σ s = s := by
    apply Equiv.Perm.viaEmbedding_apply_of_notMem e j s
    rintro ⟨w,hw⟩
    exact hs (hw ▸ (ι w).property)
  have hsigout (s : {s : Fin k × Bool // s.1 ∈ A}) (hs : s ∉ Set.range ι) : σ s.val = s.val := by
    apply Equiv.Perm.viaEmbedding_apply_of_notMem e j s.val
    rintro ⟨w,hw⟩
    exact hs ⟨w,Subtype.ext hw⟩
  have hdata (s : {s : Fin k × Bool // s.1 ∈ A}) :
      ∃ q : G.Walk (T.endpoint (σ s.val)) r, q.IsTrail ∧
        q.toSubgraph.verts = (R.tail s).toSubgraph.verts ∧
        (∀ w, ι w = s → q.toSubgraph = (F.tail (e w)).toSubgraph) ∧
        (s ∉ Set.range ι → q.toSubgraph = (R.tail s).toSubgraph) := by
    by_cases hs : s ∈ Set.range ι
    · obtain ⟨w,rfl⟩ := hs
      have hstart : (e w).val = T.endpoint (σ (ι w).val) := by rw [hsig,hlabel]
      refine ⟨(F.tail (e w)).copy hstart rfl, by simpa using F.trail (e w), ?_, ?_, ?_⟩
      · rw [NormalTrailSystem.walk_copy_subgraph,hverts]
        rw [R.selected_subgraph]
      · intro z hz
        have hzw : z = w := ι.injective hz
        subst z
        exact NormalTrailSystem.walk_copy_subgraph _ _ _
      · exact fun hh ↦ (hh ⟨w,rfl⟩).elim
    · have hstart : T.endpoint s.val = T.endpoint (σ s.val) := by rw [hsigout s hs]
      refine ⟨(R.tail s).copy hstart rfl, by simpa using R.trail s, ?_, ?_, ?_⟩
      · rw [NormalTrailSystem.walk_copy_subgraph]
      · intro w hw; exact (hs ⟨w,hw⟩).elim
      · intro _; exact NormalTrailSystem.walk_copy_subgraph _ _ _
  choose q hq hqv hqin hqout using hdata
  have hqsel (w : B) : (q (ι w)).toSubgraph = (F.tail (e w)).toSubgraph := hqin _ w rfl
  have hcross (w : B) (s : {s : Fin k × Bool // s.1 ∈ A}) (hs : s ∉ Set.range ι) :
      Disjoint (F.tail w).toSubgraph.edgeSet (R.tail s).toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro d hd hds
    obtain ⟨z,hz⟩ := (hcover d).mp ⟨w,hd⟩
    rw [R.selected_subgraph] at hz
    exact Set.disjoint_left.mp (R.disjoint (fun hh ↦ hs ⟨z,hh⟩)) hz hds
  have hqq : Pairwise fun s t ↦ Disjoint (q s).toSubgraph.edgeSet (q t).toSubgraph.edgeSet := by
    intro s t hst
    by_cases hs : s ∈ Set.range ι
    · obtain ⟨w,rfl⟩ := hs
      rw [hqsel]
      by_cases ht : t ∈ Set.range ι
      · obtain ⟨z,rfl⟩ := ht
        rw [hqsel]
        exact F.disjoint (fun hh ↦ hst (congrArg ι (e.injective hh)))
      · rw [hqout t ht]
        exact hcross _ t ht
    · rw [hqout s hs]
      by_cases ht : t ∈ Set.range ι
      · obtain ⟨z,rfl⟩ := ht
        rw [hqsel]
        exact (hcross _ s hs).symm
      · rw [hqout t ht]
        exact R.disjoint hst
  have hU (d : Sym2 V) : (∃ s, d ∈ (q s).toSubgraph.edgeSet) ↔
      ∃ s, d ∈ (R.tail s).toSubgraph.edgeSet := by
    constructor
    · rintro ⟨s,hs⟩
      by_cases hin : s ∈ Set.range ι
      · obtain ⟨w,rfl⟩ := hin
        rw [hqsel] at hs
        obtain ⟨z,hz⟩ := (hcover d).mp ⟨e w,hs⟩
        rw [R.selected_subgraph] at hz
        exact ⟨ι z,hz⟩
      · exact ⟨s,by rw [← hqout s hin]; exact hs⟩
    · rintro ⟨s,hs⟩
      by_cases hin : s ∈ Set.range ι
      · obtain ⟨w,rfl⟩ := hin
        have hh : ∃ z, d ∈ ((R.selected B hr ι hlabel hn).tail z).toSubgraph.edgeSet :=
          ⟨w,by rw [R.selected_subgraph]; exact hs⟩
        obtain ⟨z,hz⟩ := (hcover d).mpr hh
        refine ⟨ι (e.symm z),?_⟩
        rw [hqsel,Equiv.apply_symm_apply]
        exact hz
      · exact ⟨s,by rw [hqout s hin]; exact hs⟩
  obtain ⟨U,hscore,hquota,hends,Q,hQt,_,hOutside⟩ :=
    RootedCut.rebuild_tracked R σ hfix q hq hqq hU hqv
  refine ⟨U,hscore,hquota,active_labels_eq_of_endpoint_perm U T A σ hfix hends,
    Q,?_,hOutside,e,?_,?_,?_,?_⟩
  · intro s
    rw [hQt,hqv]
  · intro w
    rw [hends,hsig,hlabel]
  · intro w
    rw [hQt,hqsel]
  · intro s hs
    rw [hQt,hqout s hs]
  · intro s hs
    rw [hends,hsigout s hs]

end Erdos583TrackedRootedCutDevelopment
