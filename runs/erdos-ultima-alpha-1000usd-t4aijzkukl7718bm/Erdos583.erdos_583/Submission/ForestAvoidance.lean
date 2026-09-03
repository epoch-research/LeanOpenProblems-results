import Submission.Work

/-! Simultaneous forbidden-partner avoidance for normal partitions of forests.
This is an auxiliary forest theorem, not the unrestricted Gallai conjecture. -/
open SimpleGraph Erdos583Work
open Erdos583Work.TrailNormalization
namespace Erdos583ForestAvoidanceDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

structure AvoidanceData {V : Type*} (G : SimpleGraph V) where
  sources : Set V
  target : V → V
  outside : ∀ a ∈ sources, target a ∉ sources
  not_adj : ∀ a ∈ sources, ¬G.Adj a (target a)

namespace AvoidanceData

lemma target_ne {V : Type*} {G : SimpleGraph V} (M : AvoidanceData G)
    {a : V} (ha : a ∈ M.sources) : M.target a ≠ a :=
  fun h ↦ M.outside a ha (by rw [h]; exact ha)

noncomputable def bad {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : AvoidanceData G) {k : ℕ} (T : NormalTrailSystem G k) : Finset V :=
  Finset.univ.filter fun a ↦ a ∈ M.sources ∧ M.target a ∈ (T.walk (T.owner a)).support

lemma mem_bad {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : AvoidanceData G) {k : ℕ} (T : NormalTrailSystem G k) (a : V) :
    a ∈ M.bad T ↔ a ∈ M.sources ∧ M.target a ∈ (T.walk (T.owner a)).support := by
  simp [bad]

end AvoidanceData

lemma owner_eq_iff_odd {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : NormalTrailSystem G k) (a : V) (i : Fin k) :
    T.owner a=i ↔ Odd ((T.walk i).toSubgraph.neighborSet a).ncard := by
  rw [←T.endpoint_iff_owner,trail_neighbor_ncard_odd_iff (T.isTrail i)]
  exact (and_iff_right (T.endpoints_ne i)).symm

lemma owner_eq_of_parts_eq {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (S T : NormalTrailSystem G k)
    (he : ∀ i, (S.walk i).toSubgraph=(T.walk i).toSubgraph) (a : V) :
    S.owner a=T.owner a := by
  apply (owner_eq_iff_odd S a _).mpr
  rw [he]
  exact (owner_eq_iff_odd T a _).mp rfl

lemma bad_eq_of_parts_eq {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (M : AvoidanceData G) (S T : NormalTrailSystem G k)
    (he : ∀ i, (S.walk i).toSubgraph=(T.walk i).toSubgraph) : M.bad S=M.bad T := by
  ext a
  simp only [M.mem_bad,←Walk.mem_verts_toSubgraph,he]
  rw [owner_eq_of_parts_eq S T he a]

lemma forest_disjoint_paths_inter {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    {w a b x : V} (p : G.Walk w a) (q : G.Walk w b)
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hd : Disjoint p.toSubgraph.edgeSet q.toSubgraph.edgeSet)
    (hx : x ∈ p.support) (hy : x ∈ q.support) : x=w := by
  by_contra hn
  have hd' : Disjoint p.reverse.toSubgraph.edgeSet q.toSubgraph.edgeSet := by simpa using hd
  have hpath := (hG.isPath_iff_isTrail _).mpr (trail_append_of_disjoint hp.reverse hq hd')
  exact hpath.ne_of_mem_support_of_append hn (by simpa using hx) hy rfl

lemma owner_after_slide {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (S T : NormalTrailSystem G k) (i j : Fin k) (_hij : i ≠ j)
    (ha : S.start=(fun l ↦ T.start (Equiv.swap i j l))) (hb : S.finish=T.finish)
    {x : V} (hxi : x ≠ T.start i) (hxj : x ≠ T.start j) : S.owner x=T.owner x := by
  apply (S.endpoint_iff_owner x _).mp
  rcases T.owner_spec x with hx | hx
  · left
    have hoi : T.owner x ≠ i := fun h ↦ hxi (h ▸ hx)
    have hoj : T.owner x ≠ j := fun h ↦ hxj (h ▸ hx)
    simpa only [ha,Equiv.swap_apply_of_ne_of_ne hoi hoj] using hx
  · right
    simpa only [hb] using hx

/-- One violating source can be repaired by shifting the first edge. The only
possible new violating source is the new start of the shortened donor. -/
lemma forest_slide {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : G.IsAcyclic) (M : AvoidanceData G) (T : NormalTrailSystem G k)
    (i j : Fin k) (hij : i ≠ j)
    (h : G.Adj (T.start i) (T.start j)) (p : G.Walk (T.start j) (T.finish i))
    (he : (T.walk i).toSubgraph=(Walk.cons h p).toSubgraph)
    (hp : (Walk.cons h p).IsTrail)
    (ha : T.start i ∈ M.sources) (hbad : M.target (T.start i) ∈ (T.walk i).support) :
    ∃ S : NormalTrailSystem G k,
      M.bad S ⊆ insert (T.start j) ((M.bad T).erase (T.start i)) ∧
      S.owner (T.start j)=i ∧
      (S.walk i).toSubgraph.verts.ncard+1=(T.walk i).toSubgraph.verts.ncard := by
  classical
  obtain ⟨S,hSi,hSj,hSl,hSa,hSb,_⟩ := slide_oriented T i j hij h p hp he
  have haown : S.owner (T.start i)=j := by
    apply (S.endpoint_iff_owner _ _).mp
    left
    simp [hSa]
  have hwown : S.owner (T.start j)=i := by
    apply (S.endpoint_iff_owner _ _).mp
    left
    simp [hSa]
  have hpath := (hG.isPath_iff_isTrail _).mpr hp
  have hpn := (Walk.cons_isPath_iff h p).mp hpath |>.2
  have htargetp : M.target (T.start i) ∈ p.support := by
    rw [←Walk.mem_verts_toSubgraph,he,Walk.mem_verts_toSubgraph,Walk.support_cons,List.mem_cons] at hbad
    exact hbad.resolve_left (M.target_ne ha)
  have htargetw : M.target (T.start i) ≠ T.start j := by
    intro hh
    exact M.not_adj _ ha (hh ▸ h)
  have htargetq : M.target (T.start i) ∉ (T.walk j).support := by
    intro hh
    apply htargetw
    apply forest_disjoint_paths_inter hG p (T.walk j) (Walk.isTrail_cons h p |>.mp hp |>.1)
      (T.isTrail j) _ htargetp hh
    have hd : Disjoint (Walk.cons h p).toSubgraph.edgeSet (T.walk j).toSubgraph.edgeSet := by
      rw [←he]
      exact T.disjoint hij
    exact hd.mono_left (by
      intro e hee
      simpa only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons] using
        (Or.inr (p.mem_edges_toSubgraph.mp hee) : e=s(T.start i,T.start j) ∨ e ∈ p.edges))
  refine ⟨S,?_,hwown,?_⟩
  · intro x hx
    obtain ⟨hxs,hxt⟩ := (M.mem_bad S x).mp hx
    by_cases hxw : x=T.start j
    · subst x; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      have hxa : x ≠ T.start i := by
        rintro rfl
        rw [haown,←Walk.mem_verts_toSubgraph,hSj,Walk.mem_verts_toSubgraph,
          Walk.support_cons,List.mem_cons] at hxt
        exact hxt.elim (M.target_ne ha) htargetq
      refine Finset.mem_erase.mpr ⟨hxa,(M.mem_bad T x).mpr ⟨hxs,?_⟩⟩
      have hown := owner_after_slide S T i j hij hSa hSb hxa hxw
      rw [hown] at hxt
      by_cases hoi : T.owner x=i
      · rw [hoi,←Walk.mem_verts_toSubgraph,hSi,Walk.mem_verts_toSubgraph] at hxt
        rw [hoi,←Walk.mem_verts_toSubgraph,he,Walk.mem_verts_toSubgraph]
        exact List.mem_cons_of_mem _ hxt
      · by_cases hoj : T.owner x=j
        · rw [hoj,←Walk.mem_verts_toSubgraph,hSj,Walk.mem_verts_toSubgraph,
            Walk.support_cons,List.mem_cons] at hxt
          rw [hoj]
          exact hxt.resolve_left (fun hh ↦ M.outside x hxs (hh ▸ ha))
        · simpa only [←Walk.mem_verts_toSubgraph,hSl _ hoi hoj] using hxt
  · rw [hSi,he,cons_ncard_of_notMem h p hpn]


lemma path_ne_ends_of_mem {V : Type*} {G : SimpleGraph V} {a b x : V}
    (p : G.Walk a b) (hp : p.IsPath) (hx : x ∈ p.support) (hxa : x ≠ a) : a ≠ b := by
  rintro rfl
  have he := (Walk.isPath_iff_eq_nil p).mp hp
  exact hxa (by simpa only [he,Walk.support_nil,List.mem_singleton] using hx)

/-- A bad source can either be eliminated or moved to a strictly smaller
indexed member, with no other new bad sources. -/
lemma forest_step {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : G.IsAcyclic) (M : AvoidanceData G) (T : NormalTrailSystem G k)
    (a : V) (ha : a ∈ M.bad T) :
    ∃ S : NormalTrailSystem G k, ∃ w : V,
      M.bad S ⊆ insert w ((M.bad T).erase a) ∧
      (S.walk (S.owner w)).toSubgraph.verts.ncard+1=
        (T.walk (T.owner a)).toSubgraph.verts.ncard := by
  classical
  obtain ⟨has,hat⟩ := (M.mem_bad T a).mp ha
  let i := T.owner a
  obtain ⟨U,_,hUa,_,hUe⟩ := orient_receiver T i a (T.owner_spec a)
  have hnn : ¬(U.walk i).Nil := Walk.not_nil_of_ne (U.endpoints_ne i)
  let y := (U.walk i).snd
  let p := (U.walk i).tail
  have h : G.Adj (U.start i) y := (U.walk i).adj_snd hnn
  have hform : Walk.cons h p=U.walk i := (U.walk i).cons_tail_eq hnn
  have hp : (Walk.cons h p).IsTrail := hform.symm ▸ U.isTrail i
  have hpath := (hG.isPath_iff_isTrail _).mpr hp
  have htarget : M.target a ∈ p.support := by
    have hatU : M.target a ∈ (U.walk i).support := by
      rw [←Walk.mem_verts_toSubgraph,hUe,Walk.mem_verts_toSubgraph]
      exact hat
    rw [←hform,Walk.support_cons,List.mem_cons,hUa] at hatU
    exact hatU.resolve_left (M.target_ne has)
  have hty : M.target a ≠ y := by
    intro hh
    apply M.not_adj a has
    simpa only [hUa,←hh] using h
  have hyb := path_ne_ends_of_mem p ((Walk.cons_isPath_iff h p).mp hpath).1 htarget hty
  let j := U.owner y
  have hij : i ≠ j := by
    intro hh
    have hy := U.owner_spec y
    change y=U.start j ∨ y=U.finish j at hy
    rw [←hh] at hy
    exact hy.elim h.ne.symm hyb
  obtain ⟨R,_,hRy,hRl,hRe⟩ := orient_receiver U j y (U.owner_spec y)
  obtain ⟨hRi,hRf⟩ := hRl i hij
  have hRa : R.start i=a := hRi.trans hUa
  have hR : G.Adj (R.start i) (R.start j) := by rw [hRi,hRy]; exact h
  let q := p.copy hRy.symm hRf.symm
  have hformR : Walk.cons hR q=(Walk.cons h p).copy hRi.symm hRf.symm :=
    cons_copy_vertices h p hRi.symm hRy.symm hRf.symm hR
  have heR : (R.walk i).toSubgraph=(Walk.cons hR q).toSubgraph := by
    rw [hformR,NormalTrailSystem.walk_copy_subgraph,hform,hRe]
  have hpR : (Walk.cons hR q).IsTrail := by rw [hformR]; simpa using hp
  have hatR : M.target (R.start i) ∈ (R.walk i).support := by
    rw [←Walk.mem_verts_toSubgraph,hRe,hUe,Walk.mem_verts_toSubgraph]
    rw [hRa]
    exact hat
  obtain ⟨S,hsub,hown,hs⟩ := forest_slide hG M R i j hij hR q heR hpR
    (hRa.symm ▸ has) hatR
  have hbadR : M.bad R=M.bad T :=
    (bad_eq_of_parts_eq M R U hRe).trans (bad_eq_of_parts_eq M U T hUe)
  refine ⟨S,y,?_,?_⟩
  · simpa only [hRa,hRy,hbadR] using hsub
  · rw [hRy] at hown
    rw [hown,hs,hRe,hUe]

/-- Every normal trail system of a forest has a normal simple-path system
simultaneously avoiding each specified nonneighbor at its source endpoint.
Targets need only lie outside the source set; their injectivity is not required. -/
lemma forest_avoidance {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : G.IsAcyclic) (M : AvoidanceData G) (T₀ : NormalTrailSystem G k) :
    ∃ S : NormalTrailSystem G k, (∀ i, (S.walk i).IsPath) ∧
      ∀ a ∈ M.sources, M.target a ∉ (S.walk (S.owner a)).support := by
  classical
  let P (n : ℕ) := ∃ T : NormalTrailSystem G k, (M.bad T).card=n
  have hex : ∃ n, P n := ⟨_,T₀,rfl⟩
  let n := Nat.find hex
  obtain ⟨T,hT⟩ := Nat.find_spec hex
  have hmin (U : NormalTrailSystem G k) : n ≤ (M.bad U).card :=
    Nat.find_min' hex ⟨U,rfl⟩
  have hn : n=0 := by
    by_contra hn
    have hpos : 0 < (M.bad T).card := by change (M.bad T).card=n at hT; omega
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hpos
    let Q (m : ℕ) := ∃ U : NormalTrailSystem G k, ∃ b : V,
      (M.bad U).card=n ∧ b ∈ M.bad U ∧ (U.walk (U.owner b)).toSubgraph.verts.ncard=m
    have heQ : ∃ m, Q m := ⟨_,T,a,hT,ha,rfl⟩
    obtain ⟨U,b,hU,hb,hm⟩ := Nat.find_spec heQ
    obtain ⟨S,w,hsub,hs⟩ := forest_step hG M U b hb
    have hcb := Finset.card_erase_add_one hb
    have hcs : (M.bad S).card ≤ n := by
      have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le w _)
      omega
    have hS : (M.bad S).card=n := Nat.le_antisymm hcs (hmin S)
    have hw : w ∈ M.bad S := by
      by_contra hwe
      have hsub' : M.bad S ⊆ (M.bad U).erase b := by
        intro x hx
        rcases Finset.mem_insert.mp (hsub hx) with he | he
        · exact (hwe (he ▸ hx)).elim
        · exact he
      have hh := Finset.card_le_card hsub'
      omega
    have hqm := Nat.find_min' heQ (show Q (S.walk (S.owner w)).toSubgraph.verts.ncard from
      ⟨S,w,hS,hw,rfl⟩)
    omega
  refine ⟨T,fun i ↦ (hG.isPath_iff_isTrail _).mpr (T.isTrail i),?_⟩
  intro a ha ht
  have hb := (M.mem_bad T a).mpr ⟨ha,ht⟩
  have hz : M.bad T=∅ := Finset.card_eq_zero.mp (hT.trans hn)
  simp [hz] at hb


/-- The matching-append avoidance certificate exists when the old all-odd
 graph is a forest. This makes no assertion for cyclic old graphs. -/
lemma all_odd_forest_matching_addition {V : Type*} [Fintype V]
    (H G : SimpleGraph V) (hH : H.IsAcyclic) (ho : ∀ v, Odd (H.degree v))
    (hHG : H ≤ G) (M : MatchingAppend.OrientedMatching G)
    (hnew : Disjoint H.edgeSet M.edges) (hcover : G.edgeSet=H.edgeSet ∪ M.edges) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card ≤ Fintype.card V := by
  classical
  let A : AvoidanceData H :=
    { sources := M.sources
      target := M.target
      outside := M.target_outside
      not_adj := by
        intro a ha hab
        exact Set.disjoint_left.mp hnew hab ⟨a,ha,rfl⟩ }
  obtain ⟨k,_,⟨T⟩⟩ := all_odd_normal_trail_system H ho
  obtain ⟨S,hS,havoid⟩ := forest_avoidance hH A T
  apply MatchingAppend.matching_append_certificate hHG M S hS hnew hcover
  intro i a ha hs
  have hown := (S.endpoint_iff_owner a i).mp ha
  have hh := havoid a hs
  change M.target a ∉ (S.walk (S.owner a)).support at hh
  rw [hown] at hh
  exact hh

end Erdos583ForestAvoidanceDevelopment
