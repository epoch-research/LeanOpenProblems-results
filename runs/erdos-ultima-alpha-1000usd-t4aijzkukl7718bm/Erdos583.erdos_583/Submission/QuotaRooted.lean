import Submission.QuotaTrails

/-! Rooted cuts and slot-permutation rebuilding for arbitrary endpoint quotas. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
open Erdos583DistinctTailsDevelopment Erdos583QuotaTrailsDevelopment
namespace Erdos583QuotaRootedDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

structure RootedCut {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (A : Finset (Fin k)) where
  tail : ∀ s : {s : Fin k × Bool // s.1 ∈ A}, G.Walk (T.endpoint s.val) r
  trail : ∀ s, (tail s).IsTrail
  disjoint : Pairwise fun s t ↦ Disjoint (tail s).toSubgraph.edgeSet (tail t).toSubgraph.edgeSet
  decomp : ∀ i (hi : i ∈ A), (T.walk i).toSubgraph =
    (tail ⟨(i,true),hi⟩).toSubgraph ⊔ (tail ⟨(i,false),hi⟩).toSubgraph
  outside : ∀ i, i ∉ A → r ∉ (T.walk i).support

lemma RootedCut.tail_in_member {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (s : {s : Fin k × Bool // s.1 ∈ A}) :
    (R.tail s).toSubgraph ≤ (T.walk s.val.1).toSubgraph := by
  rw [R.decomp _ s.property]
  rcases s with ⟨⟨i,b⟩,hi⟩
  cases b
  · exact le_sup_right
  · exact le_sup_left

/-- Rebuild after permuting endpoint SLOTS, not all occurrences of a vertex
label. This permits duplicate endpoint labels outside the selected family. -/
lemma RootedCut.rebuild {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
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
      ∃ Q : RootedCut S r A, ∀ s, (Q.tail s).toSubgraph = (q s).toSubgraph := by
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
  exact ⟨S,hscore,S.quota_eq_of_endpoint_perm T σ hends,hends,Q,hq'e⟩

lemma active_labels_eq_of_endpoint_perm {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (U T : TrailFamily G k) (A : Finset (Fin k))
    (σ : Equiv.Perm (Fin k × Bool)) (hfix : ∀ s, s.1 ∉ A → σ s = s)
    (hends : ∀ s, U.endpoint s = T.endpoint (σ s)) (x : V) :
    (∃ s : {s : Fin k × Bool // s.1 ∈ A}, U.endpoint s.val = x) ↔
      ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val = x := by
  have hmem (s : Fin k × Bool) : (σ s).1 ∈ A ↔ s.1 ∈ A := by
    constructor
    · intro hs
      by_contra hn
      rw [hfix s hn] at hs
      exact hn hs
    · intro hs
      by_contra hn
      have he : σ s = s := σ.injective (hfix (σ s) hn)
      rw [he] at hn
      exact hn hs
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨⟨σ s.val,(hmem s.val).mpr s.property⟩,(hends s.val).symm.trans hs⟩
  · rintro ⟨s,hs⟩
    have hm : (σ.symm s.val).1 ∈ A := (hmem (σ.symm s.val)).mp (by simpa using s.property)
    refine ⟨⟨σ.symm s.val,hm⟩,?_⟩
    rw [hends,Equiv.apply_symm_apply]
    exact hs

/-- Select one tail for each DISTINCT vertex label. Any other occurrences
of those labels remain outside the selection. -/
def RootedCut.selected {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (B : Finset V) (hr : r ∈ B)
    (ι : B ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hlabel : ∀ w, T.endpoint (ι w).val = w.val)
    (hn : ¬(R.tail (ι ⟨r,hr⟩)).Nil) :
    Erdos583DistinctTailsDevelopment.TailFamily G r B where
  root_mem := hr
  tail w := (R.tail (ι w)).copy (hlabel w) rfl
  trail w := by simpa only [Walk.isTrail_copy] using R.trail (ι w)
  disjoint := by
    intro w z hwz
    simp only [NormalTrailSystem.walk_copy_subgraph]
    exact R.disjoint (ι.injective.ne hwz)
  root_nonempty := by simpa only [Walk.nil_copy] using hn

lemma RootedCut.selected_subgraph {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (B : Finset V) (hr : r ∈ B)
    (ι : B ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hlabel : ∀ w, T.endpoint (ι w).val = w.val)
    (hn : ¬(R.tail (ι ⟨r,hr⟩)).Nil) (w : B) :
    ((R.selected B hr ι hlabel hn).tail w).toSubgraph = (R.tail (ι w)).toSubgraph := by
  simp only [RootedCut.selected,NormalTrailSystem.walk_copy_subgraph]

/-- Apply a distinct-label rearrangement to selected endpoint slots, leaving
all duplicate occurrences and all outside members untouched. -/
lemma RootedCut.rebuild_selected {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (B : Finset V) (hr : r ∈ B)
    (ι : B ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hlabel : ∀ w, T.endpoint (ι w).val = w.val)
    (hn : ¬(R.tail (ι ⟨r,hr⟩)).Nil)
    (F : Erdos583DistinctTailsDevelopment.TailFamily G r B)
    (hF : Rearranged F (R.selected B hr ι hlabel hn)) :
    ∃ U : TrailFamily G k, U.score = T.score ∧ (∀ v, U.quota v = T.quota v) ∧
      (∀ x, (∃ s : {s : Fin k × Bool // s.1 ∈ A}, U.endpoint s.val = x) ↔
        ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val = x) ∧
      ∃ Q : RootedCut U r A, ∃ ι' : B ↪ {s : Fin k × Bool // s.1 ∈ A},
        (∀ w, U.endpoint (ι' w).val = w.val) ∧
        ∀ w, (Q.tail (ι' w)).toSubgraph = (F.tail w).toSubgraph := by
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
  obtain ⟨U,hscore,hquota,hends,Q,hQt⟩ := R.rebuild σ hfix q hq hqq hU hqv
  let ι' : B ↪ {s : Fin k × Bool // s.1 ∈ A} :=
    ⟨fun w ↦ ι (e.symm w),ι.injective.comp e.symm.injective⟩
  refine ⟨U,hscore,hquota,active_labels_eq_of_endpoint_perm U T A σ hfix hends,Q,ι',?_,?_⟩
  · intro w
    change U.endpoint (ι (e.symm w)).val = w.val
    rw [hends,hsig,Equiv.apply_symm_apply]
    exact hlabel w
  · intro w
    change (Q.tail (ι (e.symm w))).toSubgraph = (F.tail w).toSubgraph
    rw [hQt,hqsel,Equiv.apply_symm_apply]

/-- Cut every member visiting a repeated starting vertex into its two
endpoint-to-root tails, retaining a nonempty closed tail at that start. -/
lemma of_repeated_start {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i₀ : Fin k) {w : V}
    (h : G.Adj (T.start i₀) w) (p : G.Walk w (T.finish i₀))
    (he : T.walk i₀ = Walk.cons h p) (hv : T.start i₀ ∈ p.support) :
    ∃ A : Finset (Fin k), ∃ hi₀ : i₀ ∈ A, ∃ R : RootedCut T (T.start i₀) A,
      ¬(R.tail ⟨(i₀,true),hi₀⟩).Nil := by
  classical
  let v := T.start i₀
  let I := Finset.univ.filter fun i ↦ v ∈ (T.walk i).support
  have hia (i : Fin k) : i ∈ I ↔ v ∈ (T.walk i).support := by simp [I]
  have hi₀ : i₀ ∈ I := (hia i₀).mpr (T.walk i₀).start_mem_support
  let j₀ : I := ⟨i₀,hi₀⟩
  have hcuts (j : I) : ∃ L : G.Walk (T.start j.val) v,
      ∃ Q : G.Walk (T.finish j.val) v,
        T.walk j.val = L.append Q.reverse ∧ (j = j₀ → ¬L.Nil) := by
    by_cases hj : j = j₀
    · subst j
      refine ⟨Walk.cons h (p.takeUntil v hv), (p.dropUntil v hv).reverse, ?_, ?_⟩
      · simp only [Walk.reverse_reverse, Walk.cons_append, Walk.take_spec]
        exact he
      · intro _; simp
    · refine ⟨(T.walk j.val).takeUntil v ((hia j.val).mp j.property),
        ((T.walk j.val).dropUntil v ((hia j.val).mp j.property)).reverse, ?_,
        fun hh ↦ (hj hh).elim⟩
      simp
  choose L Q hc hn using hcuts
  have hpart (j : I) : (T.walk j.val).toSubgraph = (L j).toSubgraph ⊔ (Q j).toSubgraph := by
    rw [hc j,Walk.toSubgraph_append,Walk.toSubgraph_reverse]
  have htr (j : I) : (L j).IsTrail ∧ (Q j).IsTrail ∧
      Disjoint (L j).toSubgraph.edgeSet (Q j).toSubgraph.edgeSet := by
    have ht : ((L j).append (Q j).reverse).IsTrail := hc j ▸ T.isTrail j.val
    refine ⟨ht.of_append_left, ?_, ?_⟩
    · simpa only [Walk.reverse_isTrail_iff] using ht.of_append_right
    · simpa only [Walk.toSubgraph_reverse] using append_trail_disjoint ht
  let tail (s : {s : Fin k × Bool // s.1 ∈ I}) : G.Walk (T.endpoint s.val) v := by
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact Q ⟨j,hj⟩
    · exact L ⟨j,hj⟩
  have hslot (s : {s : Fin k × Bool // s.1 ∈ I}) : (tail s).IsTrail := by
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact (htr ⟨j,hj⟩).2.1
    · exact (htr ⟨j,hj⟩).1
  have hle (s : {s : Fin k × Bool // s.1 ∈ I}) :
      (tail s).toSubgraph ≤ (T.walk s.val.1).toSubgraph := by
    rw [hpart ⟨s.val.1,s.property⟩]
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact le_sup_right
    · exact le_sup_left
  have hdis : Pairwise fun s t ↦ Disjoint (tail s).toSubgraph.edgeSet (tail t).toSubgraph.edgeSet := by
    rintro ⟨⟨i,b⟩,hi⟩ ⟨⟨j,c⟩,hj⟩ hne
    by_cases hij : i = j
    · subst j
      cases b <;> cases c
      · exact (hne rfl).elim
      · exact (htr ⟨i,hi⟩).2.2.symm
      · exact (htr ⟨i,hi⟩).2.2
      · exact (hne rfl).elim
    · exact (T.disjoint hij).mono (Subgraph.edgeSet_mono (hle ⟨(i,b),hi⟩)) (Subgraph.edgeSet_mono (hle ⟨(j,c),hj⟩))
  let R : RootedCut T v I :=
    { tail := tail, trail := hslot, disjoint := hdis,
      decomp := fun i hi ↦ hpart ⟨i,hi⟩,
      outside := fun i hi hv ↦ hi ((hia i).mpr hv) }
  exact ⟨I,hi₀,R,hn j₀ rfl⟩

/-- The distinct labels of active slots admit a section containing any
prescribed root slot. Duplicate occurrences are not identified with slots. -/
lemma RootedCut.select_labels {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (_R : RootedCut T r A)
    (ρ : {s : Fin k × Bool // s.1 ∈ A}) (hρ : T.endpoint ρ.val = r) :
    ∃ B : Finset V, ∃ hr : r ∈ B,
      ∃ ι : B ↪ {s : Fin k × Bool // s.1 ∈ A},
        (∀ w, T.endpoint (ι w).val = w.val) ∧ ι ⟨r,hr⟩ = ρ ∧
        ∀ x, x ∈ B ↔ ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val = x := by
  classical
  let B := Finset.univ.image fun s : {s : Fin k × Bool // s.1 ∈ A} ↦ T.endpoint s.val
  have hB (x : V) : x ∈ B ↔ ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val = x := by
    simp [B]
  have hr : r ∈ B := (hB r).mpr ⟨ρ,hρ⟩
  have hex (w : B) : ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val = w.val :=
    (hB w.val).mp w.property
  choose j hj using hex
  let f := Function.update j ⟨r,hr⟩ ρ
  have hlabel (w : B) : T.endpoint (f w).val = w.val := by
    by_cases hw : w = ⟨r,hr⟩
    · subst w; simpa [f] using hρ
    · rw [show f w = j w by simp [f,hw]]
      exact hj w
  have hinj : Function.Injective f := by
    intro w z hwz
    apply Subtype.ext
    exact (hlabel w).symm.trans ((congrArg (fun s ↦ T.endpoint s.val) hwz).trans (hlabel z))
  exact ⟨B,hr,⟨f,hinj⟩,hlabel,by simp [f],hB⟩

/-- A positive-quota label outside the active label set has an endpoint
owner whose member avoids the root. No uniqueness of ownership is assumed. -/
lemma RootedCut.outside_endpoint {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (B : Finset V)
    (hB : ∀ x, x ∈ B ↔ ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val = x)
    {x : V} (hx : x ∉ B) (hpos : 0 < T.quota x) :
    ∃ s : Fin k × Bool, T.endpoint s = x ∧ s.1 ∉ A ∧ r ∉ (T.walk s.1).support := by
  classical
  have hne : Nonempty {s : Fin k × Bool // T.endpoint s = x} :=
    Fintype.card_pos_iff.mp (by simpa only [TrailFamily.quota,Nat.card_eq_fintype_card] using hpos)
  obtain ⟨⟨s,hs⟩⟩ := hne
  have hsA : s.1 ∉ A := fun hh ↦ hx ((hB x).mpr ⟨⟨s,hh⟩,hs⟩)
  exact ⟨s,hs,hsA,R.outside s.1 hsA⟩

/-- Same-score, same-quota data exposing an edge at a nonempty closed root
tail, with the complete active label set still identified. -/
def ExposedRoot {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (r : V) (A : Finset (Fin k)) (B : Finset V) (z : V) : Prop :=
  ∃ U : TrailFamily G k, U.score = T.score ∧ (∀ v, U.quota v = T.quota v) ∧
    ∃ Q : RootedCut U r A,
      (∀ x, x ∈ B ↔ ∃ s : {s : Fin k × Bool // s.1 ∈ A}, U.endpoint s.val = x) ∧
      ∃ ρ : {s : Fin k × Bool // s.1 ∈ A}, U.endpoint ρ.val = r ∧
        (Q.tail ρ).toSubgraph.Adj r z

/-- The selected-tail argument gives TWO distinct outside-label exposures
for an arbitrary-quota family. Endpoint bijectivity is not assumed. -/
lemma RootedCut.two_root_exposures {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (ρ : {s : Fin k × Bool // s.1 ∈ A}) (hρ : T.endpoint ρ.val = r)
    (hn : ¬(R.tail ρ).Nil) :
    ∃ B : Finset V,
      (∀ x, x ∈ B ↔ ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val = x) ∧
      ∃ x y, x ≠ y ∧ G.Adj r x ∧ G.Adj r y ∧ x ∉ B ∧ y ∉ B ∧
        ExposedRoot T r A B x ∧ ExposedRoot T r A B y := by
  classical
  obtain ⟨B,hr,ι,hlabel,hιr,hB⟩ := R.select_labels ρ hρ
  have hn' : ¬(R.tail (ι ⟨r,hr⟩)).Nil := by rw [hιr]; exact hn
  let F := R.selected B hr ι hlabel hn'
  obtain ⟨x,y,hxy,hrx,hry,hxData,hyData⟩ :=
    Erdos583DistinctTailsDevelopment.two_distinct_escapes F
  obtain ⟨hxB,Fx,hFx,hx⟩ := hxData
  obtain ⟨hyB,Fy,hFy,hy⟩ := hyData
  have hex (z : V) (D : Erdos583DistinctTailsDevelopment.TailFamily G r B)
      (hD : Rearranged D F) (hz : (D.tail ⟨r,D.root_mem⟩).snd = z) :
      ExposedRoot T r A B z := by
    obtain ⟨U,hscore,hquota,hlabels,Q,j,hj,hQt⟩ :=
      R.rebuild_selected B hr ι hlabel hn' D hD
    refine ⟨U,hscore,hquota,Q,fun x ↦ (hB x).trans (hlabels x).symm,
      j ⟨r,D.root_mem⟩,hj _,?_⟩
    rw [hQt]
    rw [← hz]
    exact (D.tail ⟨r,D.root_mem⟩).toSubgraph_adj_snd D.root_nonempty
  exact ⟨B,hB,x,y,hxy,hrx,hry,hxB,hyB,hex x Fx hFx hx,hex y Fy hFy hy⟩

/-- The same rooted-cut construction accepts any trail representative with
the same subgraph and endpoints; literal equality of walk traversals is not
needed. -/
lemma of_repeated_start_rep {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i₀ : Fin k) {w : V}
    (h : G.Adj (T.start i₀) w) (p : G.Walk w (T.finish i₀))
    (he : (T.walk i₀).toSubgraph = (Walk.cons h p).toSubgraph)
    (hrep : (Walk.cons h p).IsTrail) (hv : T.start i₀ ∈ p.support) :
    ∃ A : Finset (Fin k), ∃ hi₀ : i₀ ∈ A, ∃ R : RootedCut T (T.start i₀) A,
      ¬(R.tail ⟨(i₀,true),hi₀⟩).Nil := by
  classical
  let v := T.start i₀
  let I := Finset.univ.filter fun i ↦ v ∈ (T.walk i).support
  have hia (i : Fin k) : i ∈ I ↔ v ∈ (T.walk i).support := by simp [I]
  have hi₀ : i₀ ∈ I := (hia i₀).mpr (T.walk i₀).start_mem_support
  let j₀ : I := ⟨i₀,hi₀⟩
  have hcuts (j : I) : ∃ L : G.Walk (T.start j.val) v,
      ∃ Q : G.Walk (T.finish j.val) v,
        (L.append Q.reverse).IsTrail ∧
        (T.walk j.val).toSubgraph = (L.append Q.reverse).toSubgraph ∧ (j = j₀ → ¬L.Nil) := by
    by_cases hj : j = j₀
    · subst j
      refine ⟨Walk.cons h (p.takeUntil v hv), (p.dropUntil v hv).reverse, ?_, ?_, ?_⟩
      · simpa only [Walk.reverse_reverse,Walk.cons_append,Walk.take_spec] using hrep
      · simpa only [Walk.reverse_reverse,Walk.cons_append,Walk.take_spec] using he
      · intro _; simp
    · refine ⟨(T.walk j.val).takeUntil v ((hia j.val).mp j.property),
        ((T.walk j.val).dropUntil v ((hia j.val).mp j.property)).reverse, ?_, ?_,
        fun hh ↦ (hj hh).elim⟩
      · simpa using T.isTrail j.val
      · simp
  choose L Q htrail hc hn using hcuts
  have hpart (j : I) : (T.walk j.val).toSubgraph = (L j).toSubgraph ⊔ (Q j).toSubgraph := by
    rw [hc j,Walk.toSubgraph_append,Walk.toSubgraph_reverse]
  have htr (j : I) : (L j).IsTrail ∧ (Q j).IsTrail ∧
      Disjoint (L j).toSubgraph.edgeSet (Q j).toSubgraph.edgeSet := by
    have ht : ((L j).append (Q j).reverse).IsTrail := htrail j
    refine ⟨ht.of_append_left, ?_, ?_⟩
    · simpa only [Walk.reverse_isTrail_iff] using ht.of_append_right
    · simpa only [Walk.toSubgraph_reverse] using append_trail_disjoint ht
  let tail (s : {s : Fin k × Bool // s.1 ∈ I}) : G.Walk (T.endpoint s.val) v := by
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact Q ⟨j,hj⟩
    · exact L ⟨j,hj⟩
  have hslot (s : {s : Fin k × Bool // s.1 ∈ I}) : (tail s).IsTrail := by
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact (htr ⟨j,hj⟩).2.1
    · exact (htr ⟨j,hj⟩).1
  have hle (s : {s : Fin k × Bool // s.1 ∈ I}) :
      (tail s).toSubgraph ≤ (T.walk s.val.1).toSubgraph := by
    rw [hpart ⟨s.val.1,s.property⟩]
    rcases s with ⟨⟨j,c⟩,hj⟩
    cases c
    · exact le_sup_right
    · exact le_sup_left
  have hdis : Pairwise fun s t ↦ Disjoint (tail s).toSubgraph.edgeSet (tail t).toSubgraph.edgeSet := by
    rintro ⟨⟨i,b⟩,hi⟩ ⟨⟨j,c⟩,hj⟩ hne
    by_cases hij : i = j
    · subst j
      cases b <;> cases c
      · exact (hne rfl).elim
      · exact (htr ⟨i,hi⟩).2.2.symm
      · exact (htr ⟨i,hi⟩).2.2
      · exact (hne rfl).elim
    · exact (T.disjoint hij).mono (Subgraph.edgeSet_mono (hle ⟨(i,b),hi⟩)) (Subgraph.edgeSet_mono (hle ⟨(j,c),hj⟩))
  let R : RootedCut T v I :=
    { tail := tail, trail := hslot, disjoint := hdis,
      decomp := fun i hi ↦ hpart ⟨i,hi⟩,
      outside := fun i hi hv ↦ hi ((hia i).mpr hv) }
  exact ⟨I,hi₀,R,hn j₀ rfl⟩

/-- A rooted defect is witnessed by a nonempty closed endpoint-to-root tail
in an active cut. Its endpoint slots need not be unique labels. -/
def HasRoot {V : Type*} {G : SimpleGraph V} {k : ℕ} (T : TrailFamily G k) (r : V) : Prop :=
  ∃ A : Finset (Fin k), ∃ R : RootedCut T r A,
    ∃ ρ : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint ρ.val = r ∧ ¬(R.tail ρ).Nil

lemma hasRoot_of_rep {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {a x b : V}
    (ha : T.start i = a) (hb : T.finish i = b)
    (h : G.Adj a x) (p : G.Walk x b)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hrep : (Walk.cons h p).IsTrail) (hv : a ∈ p.support) : HasRoot T a := by
  subst a b
  obtain ⟨A,hi,R,hn⟩ := of_repeated_start_rep T i h p he hrep hv
  exact ⟨A,R,⟨(i,true),hi⟩,rfl,hn⟩

end Erdos583QuotaRootedDevelopment
