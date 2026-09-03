import Submission.QuotaRooted

/-! Endpoint-quota identities and local surgery for general trail families. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem Erdos583Work.TrailNormalization
open Erdos583QuotaTrailsDevelopment Erdos583QuotaRootedDevelopment
namespace Erdos583QuotaSurgeryDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma quota_eq_sum_endpoints {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (v : V) :
    T.quota v = ∑ i, ((if T.start i = v then 1 else 0) +
      (if T.finish i = v then 1 else 0)) := by
  classical
  have hc : T.quota v = ∑ s : Fin k × Bool, if T.endpoint s = v then 1 else 0 := by
    rw [TrailFamily.quota,Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp only [Finset.card_filter]
  rw [hc,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool,TrailFamily.endpoint,Bool.false_eq_true,if_false,if_true]

lemma replace_two_starts_general {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i j : Fin k) (hij : i ≠ j) (u v : V)
    (p : G.Walk u (T.finish i)) (q : G.Walk v (T.finish j))
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hpq : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hu : p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet) :
    ∃ S : TrailFamily G k,
      (S.walk i).toSubgraph = p.toSubgraph ∧
      (S.walk j).toSubgraph = q.toSubgraph ∧
      (∀ l, l ≠ i → l ≠ j → (S.walk l).toSubgraph = (T.walk l).toSubgraph) ∧
      S.start = (fun l ↦ if l=i then u else if l=j then v else T.start l) ∧ S.finish = T.finish ∧
      S.score + (T.walk i).toSubgraph.verts.ncard + (T.walk j).toSubgraph.verts.ncard =
        T.score + p.toSubgraph.verts.ncard + q.toSubgraph.verts.ncard ∧
      ∀ x, S.quota x + (if T.start i=x then 1 else 0) + (if T.start j=x then 1 else 0) =
        T.quota x + (if u=x then 1 else 0) + (if v=x then 1 else 0) := by
  classical
  let a : Fin k → V := fun l ↦ if l=i then u else if l=j then v else T.start l
  have hwalk (l : Fin k) : ∃ r : G.Walk (a l) (T.finish l), r.IsTrail ∧
      r.toSubgraph = if l=i then p.toSubgraph else if l=j then q.toSubgraph else (T.walk l).toSubgraph := by
    by_cases hli : l = i
    · subst l
      rw [show a i = u by simp [a]]
      simp only [↓reduceIte]
      exact ⟨p, hp, rfl⟩
    · by_cases hlj : l = j
      · subst l
        rw [show a j = v by simp [a,hij.symm]]
        simp only [if_neg hij.symm, ↓reduceIte]
        exact ⟨q, hq, rfl⟩
      · have ha : a l = T.start l := by simp [a,hli,hlj]
        rw [ha]
        simp only [if_neg hli, if_neg hlj]
        exact ⟨T.walk l, T.isTrail l, rfl⟩
  choose r hr hre using hwalk
  have hri : (r i).toSubgraph = p.toSubgraph := by simpa using hre i
  have hrj : (r j).toSubgraph = q.toSubgraph := by simpa [hij.symm] using hre j
  have hrl (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
      (r l).toSubgraph = (T.walk l).toSubgraph := by simpa [hli, hlj] using hre l
  have hcross (l : Fin k) (hli : l ≠ i) (hlj : l ≠ j) :
      Disjoint (p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet) (T.walk l).toSubgraph.edgeSet := by
    rw [hu]
    exact disjoint_sup_left.mpr ⟨T.disjoint hli.symm, T.disjoint hlj.symm⟩
  have hdis : Pairwise fun l m ↦ Disjoint (r l).toSubgraph.edgeSet (r m).toSubgraph.edgeSet := by
    intro l m hlm
    by_cases hli : l = i
    · subst l
      rw [hri]
      by_cases hmj : m = j
      · subst m; rw [hrj]; exact hpq
      · rw [hrl m hlm.symm hmj]
        exact (disjoint_sup_left.mp (hcross m hlm.symm hmj)).1
    · by_cases hlj : l = j
      · subst l
        rw [hrj]
        by_cases hmi : m = i
        · subst m; rw [hri]; exact hpq.symm
        · rw [hrl m hmi hlm.symm]
          exact (disjoint_sup_left.mp (hcross m hmi hlm.symm)).2
      · rw [hrl l hli hlj]
        by_cases hmi : m = i
        · subst m; rw [hri]
          exact (disjoint_sup_left.mp (hcross l hli hlj)).1.symm
        · by_cases hmj : m = j
          · subst m; rw [hrj]
            exact (disjoint_sup_left.mp (hcross l hli hlj)).2.symm
          · rw [hrl m hmi hmj]
            exact T.disjoint hlm
  have hcover (e : Sym2 V) : e ∈ G.edgeSet ↔ ∃ l, e ∈ (r l).toSubgraph.edgeSet := by
    constructor
    · intro he
      obtain ⟨l, hl⟩ := (T.cover e).mp he
      by_cases hli : l = i
      · subst l
        have hh : e ∈ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := hu.symm ▸ Or.inl hl
        exact hh.elim (fun h ↦ ⟨i, hri.symm ▸ h⟩) (fun h ↦ ⟨j, hrj.symm ▸ h⟩)
      · by_cases hlj : l = j
        · subst l
          have hh : e ∈ p.toSubgraph.edgeSet ∪ q.toSubgraph.edgeSet := hu.symm ▸ Or.inr hl
          exact hh.elim (fun h ↦ ⟨i, hri.symm ▸ h⟩) (fun h ↦ ⟨j, hrj.symm ▸ h⟩)
        · exact ⟨l, (hrl l hli hlj).symm ▸ hl⟩
    · rintro ⟨l, hl⟩
      exact (r l).toSubgraph.edgeSet_subset hl
  let S : TrailFamily G k :=
    { start := a
      finish := T.finish
      walk := r
      isTrail := hr
      disjoint := hdis
      cover := hcover }
  refine ⟨S, hri, hrj, hrl, rfl, rfl, ?_, ?_⟩
  · have hsum : ∑ l ∈ (Finset.univ.erase i).erase j, (S.walk l).toSubgraph.verts.ncard =
        ∑ l ∈ (Finset.univ.erase i).erase j, (T.walk l).toSubgraph.verts.ncard := by
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hlj, hl⟩ := Finset.mem_erase.mp hl
      have hli := (Finset.mem_erase.mp hl).1
      change (r l).toSubgraph.verts.ncard = _
      rw [hrl l hli hlj]
    have hS := NormalTrailSystem.sum_extract_two (fun l ↦ (S.walk l).toSubgraph.verts.ncard) i j hij
    have hT := NormalTrailSystem.sum_extract_two (fun l ↦ (T.walk l).toSubgraph.verts.ncard) i j hij
    change S.score = (r i).toSubgraph.verts.ncard + (r j).toSubgraph.verts.ncard + _ at hS
    rw [hri, hrj, hsum] at hS
    change T.score = _ at hT
    dsimp only at hS hT
    omega
  · intro x
    have hsum : ∑ l ∈ (Finset.univ.erase i).erase j, (if S.start l=x then 1 else 0) =
        ∑ l ∈ (Finset.univ.erase i).erase j, (if T.start l=x then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hlj,hl⟩ := Finset.mem_erase.mp hl
      have hli := (Finset.mem_erase.mp hl).1
      change (if a l=x then 1 else 0) = _
      simp [a,hli,hlj]
    have hS := NormalTrailSystem.sum_extract_two
      (fun l ↦ if S.start l=x then (1:ℕ) else 0) i j hij
    have hT := NormalTrailSystem.sum_extract_two
      (fun l ↦ if T.start l=x then (1:ℕ) else 0) i j hij
    have hi' : S.start i=u := by simp [S,a]
    have hj' : S.start j=v := by simp [S,a,hij.symm]
    dsimp only at hS hT
    rw [hi',hj',hsum] at hS
    have hSq := quota_eq_sum_endpoints S x
    have hTq := quota_eq_sum_endpoints T x
    rw [Finset.sum_add_distrib] at hSq hTq
    have hfinish : (∑ l, if S.finish l=x then (1:ℕ) else 0) =
        ∑ l, if T.finish l=x then 1 else 0 := rfl
    omega

lemma orient {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (eps : Fin k → Bool) :
    ∃ S : TrailFamily G k, S.score = T.score ∧ (∀ v, S.quota v = T.quota v) ∧
      ∀ i, S.start i = (if eps i then T.finish i else T.start i) ∧
        S.finish i = (if eps i then T.start i else T.finish i) ∧
        (S.walk i).toSubgraph = (T.walk i).toSubgraph := by
  classical
  let a (i : Fin k) := if eps i then T.finish i else T.start i
  let b (i : Fin k) := if eps i then T.start i else T.finish i
  let E : Fin k × Bool ≃ Fin k × Bool :=
    { toFun := fun x ↦ (x.1, if eps x.1 then !x.2 else x.2)
      invFun := fun x ↦ (x.1, if eps x.1 then !x.2 else x.2)
      left_inv := by rintro ⟨i, c⟩; cases h : eps i <;> simp [h]
      right_inv := by rintro ⟨i, c⟩; cases h : eps i <;> simp [h] }
  have hfun : (fun x : Fin k × Bool ↦ if x.2 then a x.1 else b x.1) =
      (fun x : Fin k × Bool ↦ if x.2 then T.start x.1 else T.finish x.1) ∘ E := by
    funext x
    rcases x with ⟨i, c⟩
    cases c <;> cases h : eps i <;> simp [a, b, E, h]
  have hwalk (i : Fin k) : ∃ p : G.Walk (a i) (b i),
      p.IsTrail ∧ p.toSubgraph = (T.walk i).toSubgraph := by
    cases he : eps i
    · rw [show a i = T.start i by simp [a, he], show b i = T.finish i by simp [b, he]]
      exact ⟨T.walk i, T.isTrail i, rfl⟩
    · rw [show a i = T.finish i by simp [a, he], show b i = T.start i by simp [b, he]]
      exact ⟨(T.walk i).reverse, (T.isTrail i).reverse, by simp⟩
  choose p hp hpe using hwalk
  let S : TrailFamily G k :=
    { start := a
      finish := b
      walk := p
      isTrail := hp
      disjoint := by intro i j hij; rw [hpe i, hpe j]; exact T.disjoint hij
      cover := by intro e; simp_rw [hpe]; exact T.cover e }
  have hends (x : Fin k × Bool) : S.endpoint x = T.endpoint (E x) := congrFun hfun x
  refine ⟨S, ?_, S.quota_eq_of_endpoint_perm T E hends, fun i ↦ ⟨rfl, rfl, hpe i⟩⟩
  unfold TrailFamily.score
  apply Finset.sum_congr rfl
  intro i _
  change (p i).toSubgraph.verts.ncard = _
  rw [hpe]

lemma trail_edgeSet_ncard {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsTrail) : p.toSubgraph.edgeSet.ncard = p.length := by
  classical
  rw [Walk.edgeSet_toSubgraph,← List.coe_toFinset,Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hp.edges_nodup,Walk.length_edges]

lemma walk_vertex_ncard_le {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : p.toSubgraph.verts.ncard ≤ p.length + 1 := by
  classical
  rw [Walk.verts_toSubgraph,← List.coe_toFinset,Set.ncard_coe_finset]
  simpa only [Walk.length_support] using p.support.toFinset_card_le

lemma walk_vertex_ncard_eq_iff {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : p.toSubgraph.verts.ncard = p.length + 1 ↔ p.IsPath := by
  classical
  rw [Walk.verts_toSubgraph,← List.coe_toFinset,Set.ncard_coe_finset,← Walk.length_support]
  simpa only [List.toFinset_coe,Multiset.coe_card,Multiset.coe_nodup,Walk.isPath_def] using
    (Multiset.toFinset_card_eq_card_iff_nodup (m := (p.support : Multiset V)))

/-- A repeated-start representative in a deficit-one family has a simple
tail, regardless of how the original member was traversed. -/
lemma simple_tail_of_one_defect_rep {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score + 1 = G.edgeSet.ncard + k) (i : Fin k)
    {a x b : V} (h : G.Adj a x) (p : G.Walk x b)
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (ha : a ∈ p.support) :
    p.IsPath ∧ T.defect i = 1 ∧ ∀ j, j ≠ i → (T.walk j).IsPath := by
  have hsum : ∑ j, T.defect j = 1 := by have := T.sum_defect_add_score; omega
  have hdi : T.defect i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hlen : (T.walk i).length = (Walk.cons h p).length := by
    rw [← trail_edgeSet_ncard _ (T.isTrail i),he,trail_edgeSet_ncard _ hp]
  have hv := T.defect_add_vertices i
  rw [he,cons_ncard_of_mem h p ha,hlen,Walk.length_cons] at hv
  have hb := walk_vertex_ncard_le p
  have hi : T.defect i = 1 := by omega
  have hpPath : p.IsPath := (walk_vertex_ncard_eq_iff p).mp (by omega)
  have hn : ¬(T.walk i).IsPath := by
    intro hpath
    have hz := (T.defect_eq_zero_iff i).mpr hpath
    omega
  exact ⟨hpPath,hi,(T.one_defect_other_paths hs i hn).2⟩

/-- An exposed edge to an outside endpoint owner repairs a deficit-one
family while preserving every endpoint quota. -/
lemma repair_at_outside_start {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score + 1 = G.edgeSet.ncard + k)
    (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph)
    (hv : T.start i ∈ p.support) (havoid : T.start i ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, (∀ x, U.quota x = T.quota x) ∧ ∀ l, (U.walk l).IsPath := by
  classical
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet := by
    rw [← he]; exact T.disjoint hij
  obtain ⟨hp',hq',hd',hu,_,_⟩ := trail_endpoint_slide h p (T.walk j) hp (T.isTrail j) hd hv
  obtain ⟨U,_,_,_,_,_,hscore,hquota⟩ := replace_two_starts_general T i j hij
    (T.start j) (T.start i) p (Walk.cons h (T.walk j)) hp' hq' hd' (by rw [he]; exact hu.symm)
  have hV : (T.walk i).toSubgraph.verts.ncard = p.toSubgraph.verts.ncard := by
    rw [he,cons_ncard_of_mem h p hv]
  have hW : (Walk.cons h (T.walk j)).toSubgraph.verts.ncard = (T.walk j).toSubgraph.verts.ncard + 1 :=
    cons_ncard_of_notMem h (T.walk j) havoid
  have hgain : U.score = T.score + 1 := by rw [hW,← hV] at hscore; omega
  refine ⟨U,fun x ↦ ?_,U.score_eq_edges_add_iff.mp ?_⟩
  · have hh := hquota x
    omega
  · omega

/-- Rotate a closed root tail to an exposed neighbor and attach the other
endpoint tail. This gives a repeated-start representative with that first edge. -/
lemma closed_tail_exposed_rep {V : Type*} {G : SimpleGraph V} {r x b : V}
    (C : G.Walk r r) (B : G.Walk b r) (hC : C.IsTrail) (hB : B.IsTrail)
    (hd : Disjoint C.toSubgraph.edgeSet B.toSubgraph.edgeSet)
    (hx : C.toSubgraph.Adj r x) :
    ∃ h : G.Adj r x, ∃ p : G.Walk x b, (Walk.cons h p).IsTrail ∧
      (Walk.cons h p).toSubgraph = C.toSubgraph ⊔ B.toSubgraph ∧ r ∈ p.support := by
  obtain ⟨D,hD,hDC,hn,hDx⟩ := MultipleEscape.closed_trail_first_at_neighbor C hC hx
  cases hform : D with
  | nil => exact (hn (hform ▸ Walk.Nil.nil)).elim
  | @cons _ w _ h q =>
    have hw : w = x := by simpa only [hform,Walk.snd_cons] using hDx
    subst w
    have ht : ((Walk.cons h q).append B.reverse).IsTrail := by
      apply trail_append_of_disjoint (hform ▸ hD) hB.reverse
      rw [Walk.toSubgraph_reverse,← hform,hDC]
      exact hd
    refine ⟨h,q.append B.reverse,by simpa only [Walk.cons_append] using ht,?_,?_⟩
    · rw [← Walk.cons_append,Walk.toSubgraph_append,Walk.toSubgraph_reverse,← hform,hDC]
    · exact (Walk.mem_support_append_iff q B.reverse).mpr (Or.inl q.end_mem_support)

/-- Extract a first-edge representative from an exposed root cut. The
orientation may agree with or reverse the original member's endpoints. -/
lemma rooted_exposed_rep {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r x : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (ρ : {s : Fin k × Bool // s.1 ∈ A}) (hρ : T.endpoint ρ.val = r)
    (hx : (R.tail ρ).toSubgraph.Adj r x) :
    ∃ i b, ∃ h : G.Adj r x, ∃ p : G.Walk x b, i ∈ A ∧
      ((T.start i = r ∧ T.finish i = b) ∨ (T.finish i = r ∧ T.start i = b)) ∧
      (Walk.cons h p).IsTrail ∧ (T.walk i).toSubgraph = (Walk.cons h p).toSubgraph ∧
      r ∈ p.support := by
  rcases ρ with ⟨⟨i,c⟩,hi⟩
  cases c
  · change T.finish i = r at hρ
    let C := (R.tail ⟨(i,false),hi⟩).copy hρ rfl
    let B := R.tail ⟨(i,true),hi⟩
    have hC : C.toSubgraph = (R.tail ⟨(i,false),hi⟩).toSubgraph :=
      NormalTrailSystem.walk_copy_subgraph _ _ _
    have ht : C.IsTrail := by simpa only [C,Walk.isTrail_copy] using R.trail ⟨(i,false),hi⟩
    have hd : Disjoint C.toSubgraph.edgeSet B.toSubgraph.edgeSet := by
      rw [hC]
      exact R.disjoint (by intro hh; have := congrArg (fun s ↦ s.val.2) hh; contradiction)
    obtain ⟨h,p,hp,he,hv⟩ := closed_tail_exposed_rep C B ht (R.trail _) hd (by rw [hC]; exact hx)
    refine ⟨i,T.start i,h,p,hi,Or.inr ⟨hρ,rfl⟩,hp,?_,hv⟩
    rw [he,R.decomp i hi,hC]
    exact sup_comm _ _
  · change T.start i = r at hρ
    let C := (R.tail ⟨(i,true),hi⟩).copy hρ rfl
    let B := R.tail ⟨(i,false),hi⟩
    have hC : C.toSubgraph = (R.tail ⟨(i,true),hi⟩).toSubgraph :=
      NormalTrailSystem.walk_copy_subgraph _ _ _
    have ht : C.IsTrail := by simpa only [C,Walk.isTrail_copy] using R.trail ⟨(i,true),hi⟩
    have hd : Disjoint C.toSubgraph.edgeSet B.toSubgraph.edgeSet := by
      rw [hC]
      exact R.disjoint (by intro hh; have := congrArg (fun s ↦ s.val.2) hh; contradiction)
    obtain ⟨h,p,hp,he,hv⟩ := closed_tail_exposed_rep C B ht (R.trail _) hd (by rw [hC]; exact hx)
    refine ⟨i,T.finish i,h,p,hi,Or.inl ⟨hρ,rfl⟩,hp,?_,hv⟩
    rw [he,R.decomp i hi,hC]

lemma orient_endpoint_pair {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) (a b : V)
    (he : (T.start i=a ∧ T.finish i=b) ∨ (T.finish i=a ∧ T.start i=b)) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (∀ x, U.quota x=T.quota x) ∧
      U.start i=a ∧ U.finish i=b ∧
      (∀ l, l ≠ i → U.start l=T.start l ∧ U.finish l=T.finish l) ∧
      ∀ l, (U.walk l).toSubgraph=(T.walk l).toSubgraph := by
  classical
  rcases he with he | he
  · exact ⟨T,rfl,fun _ ↦ rfl,he.1,he.2,fun _ _ ↦ ⟨rfl,rfl⟩,fun _ ↦ rfl⟩
  · obtain ⟨U,hs,hq,ht⟩ := orient T (fun l ↦ decide (l=i))
    refine ⟨U,hs,hq,?_,?_,?_,fun l ↦ (ht l).2.2⟩
    · simpa using (ht i).1.trans (by simpa using he.1)
    · simpa using (ht i).2.1.trans (by simpa using he.2)
    · intro l hli
      exact ⟨by simpa [hli] using (ht l).1,by simpa [hli] using (ht l).2.1⟩

lemma orient_endpoint_start {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) (a : V) (he : a=T.start i ∨ a=T.finish i) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (∀ x, U.quota x=T.quota x) ∧
      U.start i=a ∧
      (∀ l, l ≠ i → U.start l=T.start l ∧ U.finish l=T.finish l) ∧
      ∀ l, (U.walk l).toSubgraph=(T.walk l).toSubgraph := by
  rcases he with he | he
  · exact ⟨T,rfl,fun _ ↦ rfl,he.symm,fun _ _ ↦ ⟨rfl,rfl⟩,fun _ ↦ rfl⟩
  · obtain ⟨U,hs,hq,ha,_,hrest,hparts⟩ := orient_endpoint_pair T i a (T.start i)
      (Or.inr ⟨he.symm,rfl⟩)
    exact ⟨U,hs,hq,ha,hrest,hparts⟩

lemma repair_at_outside_start_endpoints {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {a x b : V}
    (hai : T.start i=a) (haj : T.start j=x) (hbi : T.finish i=b)
    (h : G.Adj a x) (p : G.Walk x b) (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hv : a ∈ p.support) (havoid : a ∉ (T.walk j).support) :
    ∃ U : TrailFamily G k, (∀ v, U.quota v=T.quota v) ∧ ∀ l, (U.walk l).IsPath := by
  subst a x b
  exact repair_at_outside_start T hs i j hij h p hp he hv havoid

/-- A positive-quota exposed label gives a full repair. This closes the
positive-label branch without any endpoint-uniqueness assumption. -/
lemma exposedRoot_repair_of_positive {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r z : V} {A : Finset (Fin k)} {B : Finset V}
    (hE : ExposedRoot T r A B z) (hs : T.score+1=G.edgeSet.ncard+k)
    (hz : z ∉ B) (hpos : 0 < T.quota z) :
    ∃ P : TrailFamily G k, (∀ v, P.quota v=T.quota v) ∧ ∀ l, (P.walk l).IsPath := by
  classical
  obtain ⟨U,hscore,hquota,Q,hB,ρ,hρ,hAdj⟩ := hE
  obtain ⟨i,b,h,p,hi,hends,hp,he,hv⟩ := rooted_exposed_rep Q ρ hρ hAdj
  have hposU : 0 < U.quota z := by rw [hquota]; exact hpos
  obtain ⟨s,hsend,hsA,havoid⟩ := Q.outside_endpoint B hB hz hposU
  let j := s.1
  have hij : i ≠ j := by
    intro hh
    apply hsA
    change j ∈ A
    rw [← hh]
    exact hi
  obtain ⟨S,hSs,hSq,hSa,hSb,hSrest,hSparts⟩ := orient_endpoint_pair U i r b hends
  have hjend : z=S.start j ∨ z=S.finish j := by
    obtain ⟨hja,hjb⟩ := hSrest j hij.symm
    rw [hja,hjb]
    rcases s with ⟨j,c⟩
    cases c
    · exact Or.inr hsend.symm
    · exact Or.inl hsend.symm
  obtain ⟨R,hRs,hRq,hRj,hRrest,hRparts⟩ := orient_endpoint_start S j z hjend
  obtain ⟨hRia,hRib⟩ := hRrest i hij
  have hRscore : R.score+1=G.edgeSet.ncard+k := by omega
  have hRi : (R.walk i).toSubgraph=(Walk.cons h p).toSubgraph :=
    (hRparts i).trans ((hSparts i).trans he)
  have hRa : r ∉ (R.walk j).support := by
    rw [← Walk.mem_verts_toSubgraph,hRparts,hSparts,Walk.mem_verts_toSubgraph]
    exact havoid
  obtain ⟨P,hPq,hP⟩ := repair_at_outside_start_endpoints R hRscore i j hij
    (hRia.trans hSa) hRj (hRib.trans hSb) h p hp hRi hv hRa
  exact ⟨P,fun v ↦ (hPq v).trans ((hRq v).trans ((hSq v).trans (hquota v))),hP⟩

/-- A same-root transfer either repairs a deficit-one family or moves its
root to the neighbor. The endpoint-pair balance is recorded exactly. -/
lemma move_at_same_root {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) (hj : T.start j=T.start i)
    {x : V} (h : G.Adj (T.start i) x) (p : G.Walk x (T.finish i))
    (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hv : T.start i ∈ p.support) :
    ∃ U : TrailFamily G k,
      (∀ v, U.quota v + 2*(if T.start i=v then 1 else 0) =
        T.quota v + 2*(if x=v then 1 else 0)) ∧
      ((∀ l, (U.walk l).IsPath) ∨ (U.score=T.score ∧ HasRoot U x)) := by
  classical
  obtain ⟨hpPath,_,hother⟩ := simple_tail_of_one_defect_rep T hs i h p hp he hv
  let q := (T.walk j).copy hj rfl
  have hq : q.IsPath := by simpa only [q,Walk.isPath_copy] using hother j hij.symm
  have hqeq : q.toSubgraph=(T.walk j).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet q.toSubgraph.edgeSet := by
    rw [← he,hqeq]; exact T.disjoint hij
  obtain ⟨_,hnewTrail,hd',hunion⟩ := MobileDefect.same_root_transfer_data h p q hp hq.isTrail hd
  obtain ⟨U,hUi,hUj,_,hstarts,hfinish,hscore,hquota⟩ := replace_two_starts_general T i j hij
    x x p (Walk.cons h.symm q) hpPath.isTrail hnewTrail hd' (by rw [hunion,← he,hqeq])
  have hquot (v : V) : U.quota v + 2*(if T.start i=v then 1 else 0) =
      T.quota v + 2*(if x=v then 1 else 0) := by
    have hh := hquota v
    rw [hj] at hh
    omega
  have hV : (T.walk i).toSubgraph.verts.ncard=p.toSubgraph.verts.ncard := by
    rw [he,cons_ncard_of_mem h p hv]
  refine ⟨U,hquot,?_⟩
  by_cases hx : x ∈ q.support
  · have hW : (Walk.cons h.symm q).toSubgraph.verts.ncard=(T.walk j).toSubgraph.verts.ncard := by
      rw [cons_ncard_of_mem h.symm q hx,hqeq]
    have hsU : U.score=T.score := by rw [hW,← hV] at hscore; omega
    have hja : U.start j=x := by rw [hstarts]; simp [hij.symm]
    have hjb : U.finish j=T.finish j := by rw [hfinish]
    exact Or.inr ⟨hsU,hasRoot_of_rep U j hja hjb h.symm q hUj hnewTrail hx⟩
  · have hW : (Walk.cons h.symm q).toSubgraph.verts.ncard=(T.walk j).toSubgraph.verts.ncard+1 := by
      rw [cons_ncard_of_notMem h.symm q hx,hqeq]
    have hsU : U.score=T.score+1 := by rw [hW,← hV] at hscore; omega
    exact Or.inl (U.score_eq_edges_add_iff.mp (by omega))

/-- Replace one member by a same-subgraph trail with arbitrary new endpoints.
The score is unchanged and the exact two-slot quota balance is retained. -/
lemma replace_one_general {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {a b : V} (p : G.Walk a b) (hp : p.IsTrail)
    (he : p.toSubgraph=(T.walk i).toSubgraph) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ U.start i=a ∧ U.finish i=b ∧
      (∀ l, (U.walk l).toSubgraph=(T.walk l).toSubgraph) ∧
      ∀ v, U.quota v + (if T.start i=v then 1 else 0) + (if T.finish i=v then 1 else 0) =
        T.quota v + (if a=v then 1 else 0) + (if b=v then 1 else 0) := by
  classical
  let a' (l : Fin k) := if l=i then a else T.start l
  let b' (l : Fin k) := if l=i then b else T.finish l
  have hex (l : Fin k) : ∃ q : G.Walk (a' l) (b' l), q.IsTrail ∧ q.toSubgraph=(T.walk l).toSubgraph := by
    by_cases hli : l=i
    · subst l
      rw [show a' i=a by simp [a'],show b' i=b by simp [b']]
      exact ⟨p,hp,he⟩
    · rw [show a' l=T.start l by simp [a',hli],show b' l=T.finish l by simp [b',hli]]
      exact ⟨T.walk l,T.isTrail l,rfl⟩
  choose q hq hqg using hex
  let U : TrailFamily G k :=
    { start := a',finish := b',walk := q,isTrail := hq,
      disjoint := by intro l m hlm; rw [hqg,hqg]; exact T.disjoint hlm,
      cover := by intro e; simp_rw [hqg]; exact T.cover e }
  have ha : U.start i=a := by simp [U,a']
  have hb : U.finish i=b := by simp [U,b']
  have hscore : U.score=T.score := by
    apply Finset.sum_congr rfl
    intro l _
    exact congrArg (fun H : G.Subgraph ↦ H.verts.ncard) (hqg l)
  refine ⟨U,hscore,ha,hb,hqg,?_⟩
  intro v
  let f (S : TrailFamily G k) (l : Fin k) :=
    (if S.start l=v then (1:ℕ) else 0) + (if S.finish l=v then 1 else 0)
  have hsum : ∑ l ∈ Finset.univ.erase i, f U l = ∑ l ∈ Finset.univ.erase i, f T l := by
    apply Finset.sum_congr rfl
    intro l hl
    have hli := (Finset.mem_erase.mp hl).1
    simp [f,U,a',b',hli]
  have hU := Finset.sum_erase_add (s := Finset.univ) (f := f U) (Finset.mem_univ i)
  have hT := Finset.sum_erase_add (s := Finset.univ) (f := f T) (Finset.mem_univ i)
  rw [hsum] at hU
  have hUi : f U i=(if a=v then 1 else 0)+(if b=v then 1 else 0) := by simp only [f,ha,hb]
  have hUq : U.quota v=∑ l, f U l := quota_eq_sum_endpoints U v
  have hTq : T.quota v=∑ l, f T l := quota_eq_sum_endpoints T v
  have hTi : f T i=(if T.start i=v then 1 else 0)+(if T.finish i=v then 1 else 0) := rfl
  omega

lemma finish_eq_root_of_only_root_member {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) (r : V) (ha : T.start i=r) (hpos : 2 ≤ T.quota r)
    (honly : ∀ j, j ≠ i → r ≠ T.start j ∧ r ≠ T.finish j) : T.finish i=r := by
  classical
  have hsum : T.quota r=1+(if T.finish i=r then 1 else 0) := by
    rw [quota_eq_sum_endpoints,Finset.sum_eq_single i]
    · simp [ha]
    · intro j _ hji
      obtain ⟨hja,hjb⟩ := honly j hji
      simp [hja.symm,hjb.symm]
    · simp
  by_contra hn
  rw [if_neg hn] at hsum
  omega

/-- A closed defective member may be rerooted at any of its vertices. -/
lemma reroot_closed_member {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (i : Fin k) {r x : V}
    (ha : T.start i=r) (hb : T.finish i=r)
    (C : G.Walk r r) (ht : C.IsTrail) (hn : ¬C.Nil)
    (he : C.toSubgraph=(T.walk i).toSubgraph) (hx : x ∈ C.support) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ HasRoot U x ∧
      ∀ v, U.quota v+2*(if r=v then 1 else 0)=T.quota v+2*(if x=v then 1 else 0) := by
  classical
  let D := C.rotate hx
  have hD : D.IsTrail := ht.rotate hx
  have hDC : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hx
  have hDn : ¬D.Nil := by
    intro hnil
    have hedge : s(r,C.snd) ∈ C.toSubgraph.edgeSet := C.toSubgraph_adj_snd hn
    rw [← hDC] at hedge
    have hh := D.mem_edges_toSubgraph.mp hedge
    rw [Walk.edges_eq_nil.mpr hnil] at hh
    exact List.not_mem_nil hh
  obtain ⟨U,hs,hUa,hUb,hparts,hquota⟩ := replace_one_general T i D hD (hDC.trans he)
  have hroot : HasRoot U x := by
    cases hform : D with
    | nil => exact (hDn (hform ▸ Walk.Nil.nil)).elim
    | @cons _ w _ h q =>
      exact hasRoot_of_rep U i hUa hUb h q
        ((hparts i).trans ((hDC.trans he).symm.trans (congrArg Walk.toSubgraph hform)))
        (hform ▸ hD) q.end_mem_support
  refine ⟨U,hs,hroot,?_⟩
  intro v
  have hh := hquota v
  rw [ha,hb] at hh
  omega

lemma move_at_same_root_endpoints {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hs : T.score+1=G.edgeSet.ncard+k)
    (i j : Fin k) (hij : i ≠ j) {a x b : V}
    (hai : T.start i=a) (haj : T.start j=a) (hbi : T.finish i=b)
    (h : G.Adj a x) (p : G.Walk x b) (hp : (Walk.cons h p).IsTrail)
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph) (hv : a ∈ p.support) :
    ∃ U : TrailFamily G k,
      (∀ v, U.quota v+2*(if a=v then 1 else 0)=T.quota v+2*(if x=v then 1 else 0)) ∧
      ((∀ l, (U.walk l).IsPath) ∨ (U.score=T.score ∧ HasRoot U x)) := by
  subst a b
  exact move_at_same_root T hs i j hij haj h p hp he hv

/-- When the root has at least two endpoint slots, an exposed neighbor either
repairs the family or receives the free endpoint pair and the defect root. -/
lemma exposedRoot_move_pair_or_repair {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r z : V} {A : Finset (Fin k)} {B : Finset V}
    (hE : ExposedRoot T r A B z) (hs : T.score+1=G.edgeSet.ncard+k)
    (hpos : 2 ≤ T.quota r) :
    ∃ P : TrailFamily G k,
      (∀ v, P.quota v+2*(if r=v then 1 else 0)=T.quota v+2*(if z=v then 1 else 0)) ∧
      ((∀ l, (P.walk l).IsPath) ∨ (P.score=T.score ∧ HasRoot P z)) := by
  classical
  obtain ⟨U,hscore,hquota,Q,_,ρ,hρ,hAdj⟩ := hE
  obtain ⟨i,b,h,p,_,hends,hp,he,hv⟩ := rooted_exposed_rep Q ρ hρ hAdj
  obtain ⟨S,hSs,hSq,hSa,hSb,_,hSparts⟩ := orient_endpoint_pair U i r b hends
  have hposS : 2 ≤ S.quota r := by rw [hSq,hquota]; exact hpos
  by_cases ho : ∃ j, j ≠ i ∧ (r=S.start j ∨ r=S.finish j)
  · obtain ⟨j,hji,hjend⟩ := ho
    obtain ⟨R,hRs,hRq,hRj,hRrest,hRparts⟩ := orient_endpoint_start S j r hjend
    obtain ⟨hRia,hRib⟩ := hRrest i hji.symm
    have hRscore : R.score+1=G.edgeSet.ncard+k := by omega
    have hRi : (R.walk i).toSubgraph=(Walk.cons h p).toSubgraph :=
      (hRparts i).trans ((hSparts i).trans he)
    obtain ⟨P,hPq,hP⟩ := move_at_same_root_endpoints R hRscore i j hji.symm
      (hRia.trans hSa) hRj (hRib.trans hSb) h p hp hRi hv
    refine ⟨P,fun v ↦ ?_,?_⟩
    · have hh := hPq v
      rw [hRq,hSq,hquota] at hh
      exact hh
    · rcases hP with hP | ⟨hPs,hroot⟩
      · exact Or.inl hP
      · exact Or.inr ⟨by omega,hroot⟩
  · have honly : ∀ j, j ≠ i → r ≠ S.start j ∧ r ≠ S.finish j := by
      intro j hji
      exact ⟨fun hh ↦ ho ⟨j,hji,Or.inl hh⟩,fun hh ↦ ho ⟨j,hji,Or.inr hh⟩⟩
    have hbroot : S.finish i=r := finish_eq_root_of_only_root_member S i r hSa hposS honly
    have hbr : b=r := hSb.symm.trans hbroot
    clear hSb
    subst b
    have hzmem : z ∈ (Walk.cons h p).support := List.mem_cons_of_mem _ p.start_mem_support
    obtain ⟨P,hPs,hroot,hPq⟩ := reroot_closed_member S i hSa hbroot (Walk.cons h p) hp
      (by simp) ((hSparts i).trans he).symm hzmem
    refine ⟨P,fun v ↦ ?_,Or.inr ⟨by omega,hroot⟩⟩
    have hh := hPq v
    rw [hSq,hquota] at hh
    exact hh

end Erdos583QuotaSurgeryDevelopment
