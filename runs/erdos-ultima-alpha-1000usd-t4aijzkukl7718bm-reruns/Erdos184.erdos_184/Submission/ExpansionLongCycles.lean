import Submission.LogDeficitExpansion

/-! An auxiliary long-cycle lemma from expansion at a band of set sizes.
This file does not assert a linear cycle-decomposition bound. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.ExpansionLongCycles
open SqrtDeficitSeparator (externalBoundary)
set_option maxHeartbeats 1000000
variable {V : Type*} {G : SimpleGraph V}

/-- Connectivity expressed by ambient simple paths staying in a set. -/
def Within (G : SimpleGraph V) (R : Set V) : Prop :=
  ∀ x ∈ R, ∀ y ∈ R, ∃ p : G.Walk x y, p.IsPath ∧ ∀ z ∈ p.support, z ∈ R

/-- The ambient vertex set of a component of an induced graph. -/
def componentSet (G : SimpleGraph V) (R : Set V)
    (c : (G.induce R).ConnectedComponent) : Set V := Subtype.val '' c.supp

lemma componentSet_subset (R : Set V) (c : (G.induce R).ConnectedComponent) :
    componentSet G R c ⊆ R := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

lemma componentSet_nonempty (R : Set V) (c : (G.induce R).ConnectedComponent) :
    (componentSet G R c).Nonempty := c.nonempty_supp.image _

lemma componentSet_mem {R : Set V} {c : (G.induce R).ConnectedComponent}
    {x : V} (hx : x ∈ R) : x ∈ componentSet G R c ↔ (⟨x,hx⟩ : R) ∈ c.supp := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact (show y = ⟨x,hx⟩ from Subtype.ext hxy) ▸ hy
  · intro h
    exact ⟨⟨x,hx⟩,h,rfl⟩

lemma componentSet_adj_closed {R : Set V} {c : (G.induce R).ConnectedComponent}
    {x y : V} (hx : x ∈ componentSet G R c) (hy : y ∈ R) (hxy : G.Adj x y) :
    y ∈ componentSet G R c := by
  have hxR := componentSet_subset R c hx
  exact (componentSet_mem hy).mpr
    (c.mem_supp_of_adj_mem_supp ((componentSet_mem hxR).mp hx) hxy)

lemma componentSet_disjoint (R : Set V) :
    Pairwise (fun c d : (G.induce R).ConnectedComponent =>
      Disjoint (componentSet G R c) (componentSet G R d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro x hc hd
  have hx := componentSet_subset R c hc
  exact hcd (ConnectedComponent.eq_of_common_vertex
    ((componentSet_mem hx).mp hc) ((componentSet_mem hx).mp hd))

lemma componentSet_cover (R : Set V) :
    (⋃ c : (G.induce R).ConnectedComponent, componentSet G R c) = R := by
  ext x
  constructor
  · rintro ⟨_,⟨c,rfl⟩,hx⟩
    exact componentSet_subset R c hx
  · intro hx
    apply Set.mem_iUnion.mpr
    exact ⟨(G.induce R).connectedComponentMk ⟨x,hx⟩,
      (componentSet_mem hx).mpr ConnectedComponent.connectedComponentMk_mem⟩

lemma componentSet_within (R : Set V) (c : (G.induce R).ConnectedComponent) :
    Within G (componentSet G R c) := by
  intro x hx y hy
  obtain ⟨x',hx',rfl⟩ := hx
  obtain ⟨y',hy',rfl⟩ := hy
  obtain ⟨p,hp⟩ := c.connected_toSimpleGraph.exists_isPath ⟨x',hx'⟩ ⟨y',hy'⟩
  let f : c.toSimpleGraph →g G :=
    ((SimpleGraph.Embedding.induce R).toHom).comp c.toSimpleGraph_hom
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  refine ⟨p.map f,Walk.map_isPath_of_injective hf hp,?_⟩
  intro z hz
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (by simpa only [Walk.support_map] using hz)
  exact ⟨w.val,w.property,rfl⟩

/-- A component beyond the last vertex is attached to that vertex. -/
lemma attached_component {R : Set V} (hR : Within G R) {v : V} (hv : v ∈ R)
    (c : (G.induce (R \ {v})).ConnectedComponent) :
    ∃ w ∈ componentSet G (R \ {v}) c, G.Adj v w := by
  obtain ⟨x,hx⟩ := componentSet_nonempty (R \ {v}) c
  have hxR := componentSet_subset (R \ {v}) c hx
  obtain ⟨p,hp,hs⟩ := hR x hxR.1 v hv
  have hvnot : v ∉ componentSet G (R \ {v}) c := by
    intro h
    exact (componentSet_subset (R \ {v}) c h).2 (Set.mem_singleton v)
  obtain ⟨d,hd,hdx,hdy⟩ := p.exists_boundary_dart (componentSet G (R \ {v}) c) hx hvnot
  have hdR : d.snd ∈ R := hs d.snd (p.dart_snd_mem_support_of_mem_darts hd)
  have hdv : d.snd = v := by
    by_contra hn
    exact hdy (componentSet_adj_closed hdx ⟨hdR,by simpa using hn⟩ d.adj)
  exact ⟨d.fst,hdx,hdv ▸ d.adj.symm⟩

/-- A connected unexplored region whose external boundary is on a path,
and whose only intersection with that path is its last vertex. -/
structure RegionAt {a v : V} (p : G.Walk a v) (R : Set V) : Prop where
  path : p.IsPath
  within : Within G R
  last : v ∈ R
  meeting : ∀ x ∈ R, x ∈ p.support → x = v
  boundary : externalBoundary G R ⊆ {x | x ∈ p.support}

lemma RegionAt.extend {a v : V} {p : G.Walk a v} {R : Set V}
    (hR : RegionAt p R) (c : (G.induce (R \ {v})).ConnectedComponent)
    {w : V} (hw : w ∈ componentSet G (R \ {v}) c) (hvw : G.Adj v w) :
    RegionAt (p.concat hvw) (componentSet G (R \ {v}) c) := by
  have hsub := componentSet_subset (R \ {v}) c
  have hwv : w ≠ v := by simpa using (hsub hw).2
  have hwp : w ∉ p.support := fun h => hwv (hR.meeting w (hsub hw).1 h)
  refine ⟨hR.path.concat hwp hvw,componentSet_within _ c,hw,?_,?_⟩
  · intro x hx hxp
    simp only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] at hxp
    rcases hxp with hxp | hxp
    · exact False.elim ((hsub hx).2 (by simpa using hR.meeting x (hsub hx).1 hxp))
    · exact hxp
  · intro y hy
    obtain ⟨hynot,x,hx,hxy⟩ := hy
    have hxR := (hsub hx).1
    have hyp : y ∈ p.support := by
      by_cases hyR : y ∈ R
      · have hyv : y = v := by
          by_contra hn
          exact hynot (componentSet_adj_closed hx ⟨hyR,by simpa using hn⟩ hxy)
        exact hyv ▸ p.end_mem_support
      · exact hR.boundary ⟨hyR,x,hxR,hxy⟩
    simpa only [Set.mem_setOf_eq,Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
      using (Or.inl hyp : y ∈ p.support ∨ y = w)

variable [Fintype V]

lemma exists_maximal_region (k : ℕ)
    (hex : ∃ (a v : V) (p : G.Walk a v) (R : Set V), RegionAt p R ∧ k < R.ncard) :
    ∃ (a v : V) (p : G.Walk a v) (R : Set V), RegionAt p R ∧ k < R.ncard ∧
      ∀ (b w : V) (q : G.Walk b w) (S : Set V),
        RegionAt q S → k < S.ncard → q.length ≤ p.length := by
  let L : Set ℕ := {n | ∃ (a v : V) (p : G.Walk a v) (R : Set V),
    RegionAt p R ∧ k < R.ncard ∧ p.length = n}
  have hfin : L.Finite := (Set.finite_lt_nat (Fintype.card V)).subset (by
    rintro n ⟨a,v,p,R,hR,hk,rfl⟩
    exact hR.path.length_lt)
  have hne : L.Nonempty := by
    obtain ⟨a,v,p,R,hR,hk⟩ := hex
    exact ⟨p.length,a,v,p,R,hR,hk,rfl⟩
  obtain ⟨m,⟨⟨a,v,p,R,hR,hk,hpm⟩,hm⟩⟩ := hfin.exists_maximal hne
  refine ⟨a,v,p,R,hR,hk,?_⟩
  intro b w q S hS hkS
  have hh := hm (show q.length ∈ L from ⟨b,w,q,S,hS,hkS,rfl⟩)
  omega

omit [Fintype V] in
lemma maximal_region_component_bound {k : ℕ} {a v : V} {p : G.Walk a v} {R : Set V}
    (hR : RegionAt p R)
    (hm : ∀ (b w : V) (q : G.Walk b w) (S : Set V),
      RegionAt q S → k < S.ncard → q.length ≤ p.length)
    (c : (G.induce (R \ {v})).ConnectedComponent) :
    (componentSet G (R \ {v}) c).ncard ≤ k := by
  by_contra! hk
  obtain ⟨w,hw,hvw⟩ := attached_component hR.within hR.last c
  have hh := hm a w (p.concat hvw) _ (hR.extend c hw hvw) hk
  simp only [Walk.length_concat] at hh
  omega

/-- Greedily collect bounded summands to land in a factor-two band. -/
lemma subset_sum_band {ι : Type*} (s : Finset ι) (f : ι → ℕ) (k : ℕ)
    (hb : ∀ i ∈ s, f i ≤ 2*k) (hs : k ≤ ∑ i ∈ s, f i) :
    ∃ t ⊆ s, k ≤ ∑ i ∈ t, f i ∧ (∑ i ∈ t, f i) ≤ 2*k := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simpa using hs,by simp⟩
  | @insert a s ha ih =>
    by_cases hk : k ≤ f a
    · exact ⟨{a},by simp,hk.trans_eq (by simp),(by simpa using hb a (by simp))⟩
    · by_cases ht : k ≤ ∑ i ∈ s, f i
      · obtain ⟨t,hts,htlo,hthi⟩ := ih (fun i hi => hb i (by simp [hi])) ht
        exact ⟨t,hts.trans (Finset.subset_insert _ _),htlo,hthi⟩
      · refine ⟨insert a s,Finset.Subset.refl _,hs,?_⟩
        rw [Finset.sum_insert ha]
        omega

lemma componentUnion_card (R : Set V)
    (s : Finset (G.induce R).ConnectedComponent) :
    (⋃ c ∈ s, componentSet G R c).ncard = ∑ c ∈ s, (componentSet G R c).ncard := by
  have hh := (s.finite_toSet).ncard_biUnion
    (s := componentSet G R) (fun _ _ => Set.toFinite _)
    (fun _ _ _ _ hcd => componentSet_disjoint R hcd)
  rw [finsum_mem_coe_finset] at hh
  exact hh

lemma sum_componentSet_card (R : Set V) :
    (∑ c : (G.induce R).ConnectedComponent, (componentSet G R c).ncard) = R.ncard := by
  have hh := Set.ncard_iUnion_of_finite (fun c : (G.induce R).ConnectedComponent =>
    Set.toFinite (componentSet G R c)) (componentSet_disjoint R)
  rw [finsum_eq_sum_of_fintype,componentSet_cover] at hh
  exact hh.symm

omit [Fintype V] in
lemma componentUnion_subset (R : Set V) (s : Finset (G.induce R).ConnectedComponent) :
    (⋃ c ∈ s, componentSet G R c) ⊆ R := by
  intro x hx
  obtain ⟨c,hc,hx⟩ := Set.mem_iUnion₂.mp hx
  exact componentSet_subset R c hx

/-- Select a union of components in a factor-two band. -/
lemma componentUnion_band (R : Set V) (k : ℕ) (hk : k ≤ R.ncard)
    (hc : ∀ c : (G.induce R).ConnectedComponent, (componentSet G R c).ncard ≤ 2*k) :
    ∃ s : Finset (G.induce R).ConnectedComponent,
      k ≤ (⋃ c ∈ s, componentSet G R c).ncard ∧
      (⋃ c ∈ s, componentSet G R c).ncard ≤ 2*k := by
  obtain ⟨s,hs,hlo,hhi⟩ := subset_sum_band Finset.univ
    (fun c : (G.induce R).ConnectedComponent => (componentSet G R c).ncard) k
    (fun c _ => hc c) (by simpa only [sum_componentSet_card] using hk)
  exact ⟨s,by rwa [componentUnion_card],by rwa [componentUnion_card]⟩

omit [Fintype V] in
lemma componentUnion_boundary {R : Set V} (s : Finset (G.induce R).ConnectedComponent) :
    externalBoundary G (⋃ c ∈ s, componentSet G R c) ⊆ externalBoundary G R := by
  rintro y ⟨hy,x,hx,hxy⟩
  obtain ⟨c,hc,hx⟩ := Set.mem_iUnion₂.mp hx
  refine ⟨?_,x,componentSet_subset R c hx,hxy⟩
  intro hyR
  exact hy (Set.mem_iUnion₂.mpr ⟨c,hc,componentSet_adj_closed hx hyR hxy⟩)

/-- Choose the first point of a nonempty set lying on a path. -/
lemma first_on_path {u v : V} (p : G.Walk u v) (B : Set V) (hB : B.Nonempty)
    (hBp : ∀ x ∈ B, x ∈ p.support) :
    ∃ (a : V) (ha : a ∈ p.support), a ∈ B ∧
      (∀ x ∈ B, x ∈ (p.dropUntil a ha).support) ∧
      B.ncard ≤ (p.dropUntil a ha).length + 1 := by
  let f : B → ℕ := fun x => (p.takeUntil x.val (hBp x.val x.property)).length
  have hn : (Finset.univ : Finset B).Nonempty := by
    obtain ⟨x,hx⟩ := hB
    exact ⟨⟨x,hx⟩,Finset.mem_univ _⟩
  obtain ⟨a,ha,hm⟩ := Finset.univ.exists_min_image f hn
  have hs : ∀ x ∈ B, x ∈ (p.dropUntil a.val (hBp a.val a.property)).support := by
    intro x hx
    let m := (p.takeUntil x (hBp x hx)).length
    have hle : (p.takeUntil a.val (hBp a.val a.property)).length ≤ m :=
      hm ⟨x,hx⟩ (Finset.mem_univ _)
    have heq := congrArg (fun q : G.Walk u v => q.getVert m)
      (p.take_spec (hBp a.val a.property))
    dsimp only at heq
    rw [Walk.getVert_append,if_neg (Nat.not_lt.mpr hle)] at heq
    have hval := heq.trans (p.getVert_length_takeUntil (hBp x hx))
    exact hval ▸ (p.dropUntil a.val (hBp a.val a.property)).getVert_mem_support _
  refine ⟨a.val,hBp a.val a.property,a.property,hs,?_⟩
  have hsub : B ⊆ ((p.dropUntil a.val (hBp a.val a.property)).support.toFinset : Set V) := by
    intro x hx
    exact List.mem_toFinset.mpr (hs x hx)
  have hc := Set.ncard_le_ncard hsub
  simp only [Set.ncard_coe_finset] at hc
  exact hc.trans ((List.toFinset_card_le _).trans_eq (Walk.length_support _))

omit [Fintype V] in
lemma append_path {a b c : V} (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hi : ∀ x, x ∈ p.support → x ∈ q.support → x = b) : (p.append q).IsPath := by
  have hb : b ∉ q.support.tail := by
    have hh := hq.support_nodup
    rw [Walk.support_eq_cons,List.nodup_cons] at hh
    exact hh.1
  rw [Walk.isPath_def,Walk.support_append,List.nodup_append']
  refine ⟨hp.support_nodup,hq.support_nodup.tail,?_⟩
  intro x hx hy
  exact hb ((hi x hx (List.mem_of_mem_tail hy)) ▸ hy)

/-- A set off the path with a large boundary on the path closes a long cycle,
provided each of its components is attached to the last path vertex. -/
lemma cycle_of_boundary_on_path {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (W : Set V) (hdis : ∀ x ∈ W, x ∉ p.support)
    (hbd : ∀ x ∈ externalBoundary G W, x ∈ p.support)
    (hattach : ∀ w ∈ W, ∃ z ∈ W, G.Adj v z ∧
      ∃ q : G.Walk z w, q.IsPath ∧ ∀ x ∈ q.support, x ∈ W)
    (hlarge : 2 ≤ (externalBoundary G W).ncard) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ (externalBoundary G W).ncard + 1 ≤ c.length := by
  obtain ⟨a,ha,haB,hs,hcard⟩ := first_on_path p (externalBoundary G W)
    ((Set.ncard_pos (Set.toFinite _)).mp (by omega)) hbd
  obtain ⟨haW,w,hw,haw⟩ := haB
  obtain ⟨z,hz,hvz,q,hq,hqW⟩ := hattach w hw
  let r := p.dropUntil a ha
  have hr : r.IsPath := hp.dropUntil ha
  have hzp : z ∉ r.support := fun h => hdis z hz (p.support_dropUntil_subset ha h)
  have hrc : (r.concat hvz).IsPath := hr.concat hzp hvz
  have hi : ∀ x, x ∈ (r.concat hvz).support → x ∈ q.support → x = z := by
    intro x hx hxq
    simp only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact False.elim (hdis x (hqW x hxq) (p.support_dropUntil_subset ha hx))
    · exact hx
  have ht := append_path (r.concat hvz) q hrc hq hi
  have hlen : 2 ≤ ((r.concat hvz).append q).length := by
    simp only [Walk.length_append,Walk.length_concat]
    change (externalBoundary G W).ncard ≤ r.length+1 at hcard
    omega
  have hc := path_close_isCycle ((r.concat hvz).append q) ht hlen haw
  refine ⟨w,((r.concat hvz).append q).cons haw,hc,?_⟩
  simp only [Walk.length_cons,Walk.length_append,Walk.length_concat]
  change (externalBoundary G W).ncard ≤ r.length+1 at hcard
  omega

lemma long_cycle_of_region {k t : ℕ} (ht : 2 ≤ t)
    (hex : ∃ (a v : V) (p : G.Walk a v) (R : Set V), RegionAt p R ∧ 2*k < R.ncard)
    (hexp : ∀ X : Set V, k ≤ X.ncard → X.ncard ≤ 2*k →
      t ≤ (externalBoundary G X).ncard) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ t+1 ≤ c.length := by
  obtain ⟨a,v,p,R,hR,hkR,hm⟩ := exists_maximal_region (2*k) hex
  have hc : ∀ c : (G.induce (R \ {v})).ConnectedComponent,
      (componentSet G (R \ {v}) c).ncard ≤ 2*k :=
    maximal_region_component_bound hR hm
  have hk : k ≤ (R \ {v}).ncard := by
    have hh := Set.ncard_diff_singleton_add_one hR.last
    omega
  obtain ⟨s,hslo,hshi⟩ := componentUnion_band (R \ {v}) k hk hc
  let W := ⋃ c ∈ s, componentSet G (R \ {v}) c
  have hWsub : W ⊆ R \ {v} := componentUnion_subset _ s
  have hdis : ∀ x ∈ W, x ∉ p.support := by
    intro x hx hxp
    have hxr := hWsub hx
    exact hxr.2 (by simpa using hR.meeting x hxr.1 hxp)
  have hbd : ∀ x ∈ externalBoundary G W, x ∈ p.support := by
    intro x hx
    have hh := componentUnion_boundary s hx
    obtain ⟨hxnot,y,hy,hxy⟩ := hh
    by_cases hxR : x ∈ R
    · have hxv : x = v := by
        by_contra hn
        exact hxnot ⟨hxR,by simpa using hn⟩
      exact hxv ▸ p.end_mem_support
    · exact hR.boundary ⟨hxR,y,hy.1,hxy⟩
  have ha : ∀ w ∈ W, ∃ z ∈ W, G.Adj v z ∧
      ∃ q : G.Walk z w, q.IsPath ∧ ∀ x ∈ q.support, x ∈ W := by
    intro w hw
    obtain ⟨c,hcs,hwc⟩ := Set.mem_iUnion₂.mp hw
    obtain ⟨z,hz,hvz⟩ := attached_component hR.within hR.last c
    obtain ⟨q,hq,hqC⟩ := componentSet_within (R \ {v}) c z hz w hwc
    refine ⟨z,Set.mem_iUnion₂.mpr ⟨c,hcs,hz⟩,hvz,q,hq,?_⟩
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨c,hcs,hqC x hx⟩
  have hlarge : t ≤ (externalBoundary G W).ncard := hexp W hslo hshi
  obtain ⟨x,c,hcy,hlen⟩ := cycle_of_boundary_on_path p hR.path W hdis hbd ha (ht.trans hlarge)
  exact ⟨x,c,hcy,by omega⟩

/-- Expansion only for sets in the size band [k,2k] forces a long simple cycle.
No connectedness assumption is needed. -/
theorem long_cycle_of_band_expansion {k t : ℕ}
    (hn : 2*k < Fintype.card V) (ht : 2 ≤ t)
    (hexp : ∀ X : Set V, k ≤ X.ncard → X.ncard ≤ 2*k →
      t ≤ (externalBoundary G X).ncard) :
    ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ t+1 ≤ c.length := by
  have hex : ∃ c : (G.induce Set.univ).ConnectedComponent,
      2*k < (componentSet G Set.univ c).ncard := by
    by_contra! hsmall
    obtain ⟨s,hslo,hshi⟩ := componentUnion_band (G := G) Set.univ k
      (by simpa only [Set.ncard_univ,Nat.card_eq_fintype_card] using (show k ≤ Fintype.card V by omega))
      hsmall
    have hh := hexp (⋃ c ∈ s, componentSet G Set.univ c) hslo hshi
    have hb : externalBoundary G (⋃ c ∈ s, componentSet G Set.univ c) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (componentUnion_boundary s hx).1 (Set.mem_univ x)
    rw [hb,Set.ncard_empty] at hh
    omega
  obtain ⟨c,hc⟩ := hex
  obtain ⟨v,hv⟩ := componentSet_nonempty Set.univ c
  apply long_cycle_of_region ht _ hexp
  refine ⟨v,v,Walk.nil,componentSet G Set.univ c,?_,hc⟩
  refine ⟨Walk.IsPath.nil,componentSet_within Set.univ c,hv,?_,?_⟩
  · intro x hx hxp
    simpa only [Walk.support_nil,List.mem_singleton] using hxp
  · intro x hx
    obtain ⟨hxnot,y,hy,hyx⟩ := hx
    exact False.elim (hxnot (componentSet_adj_closed hy (Set.mem_univ x) hyx))

end Erdos184.ExpansionLongCycles
