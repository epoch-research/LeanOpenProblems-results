import Submission.Work

/-! Permutation-indexed simple-path partitions of finite Eulerian graphs. -/

open SimpleGraph Erdos583Work Erdos583Work.PendantCompletion
namespace Erdos583PermutationDevelopment
open scoped Classical

set_option maxHeartbeats 1200000

/-- A finite positive regular bipartite relation has a perfect matching. -/
lemma regular_relation_matching {I J : Type*} [Fintype I] [Fintype J]
    (r : I → J → Prop) [DecidableRel r] (d : ℕ) (hd : 0 < d)
    (hI : ∀ i, (Finset.univ.filter (r i)).card = d)
    (hJ : ∀ j, (Finset.univ.filter (fun i ↦ r i j)).card = d) :
    ∃ f : I ≃ J, ∀ i, r i (f i) := by
  classical
  have hcard : Fintype.card I = Fintype.card J := by
    have he := Finset.card_mul_eq_card_mul (s := Finset.univ) (t := Finset.univ) r
      (fun i _ ↦ hI i) (fun j _ ↦ hJ j)
    simpa only [Finset.card_univ] using Nat.eq_of_mul_eq_mul_right hd he
  have hall : ∀ A : Finset I, A.card ≤ (Finset.univ.filter (fun j ↦ ∃ i ∈ A, r i j)).card := by
    intro A
    let B := Finset.univ.filter (fun j ↦ ∃ i ∈ A, r i j)
    have hlo (i : I) (hi : i ∈ A) : d ≤ (B.bipartiteAbove r i).card := by
      have he : B.bipartiteAbove r i = Finset.univ.filter (r i) := by
        ext j
        simp only [Finset.mem_bipartiteAbove, B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨i,hi,h⟩,h⟩⟩
      rw [he,hI i]
    have hhi (j : J) (_ : j ∈ B) : (A.bipartiteBelow r j).card ≤ d := by
      rw [← hJ j]
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    exact Nat.le_of_mul_le_mul_right (Finset.card_mul_le_card_mul r hlo hhi) hd
  obtain ⟨f,hf,hfr⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hall
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩),hfr⟩

/-- A two-regular bipartite relation is the disjoint union of two bijections. -/
lemma two_regular_relation {I J : Type*} [Fintype I] [Fintype J]
    (r : I → J → Prop) [DecidableRel r]
    (hI : ∀ i, (Finset.univ.filter (r i)).card = 2)
    (hJ : ∀ j, (Finset.univ.filter (fun i ↦ r i j)).card = 2) :
    ∃ f g : I ≃ J, (∀ i, f i ≠ g i) ∧ ∀ i j, r i j ↔ j = f i ∨ j = g i := by
  classical
  obtain ⟨f,hf⟩ := regular_relation_matching r 2 (by omega) hI hJ
  let s (i : I) (j : J) := r i j ∧ j ≠ f i
  have hI' (i : I) : (Finset.univ.filter (s i)).card = 1 := by
    have he : Finset.univ.filter (s i) = (Finset.univ.filter (r i)).erase (f i) := by
      ext j; simp [s,and_comm]
    rw [he,Finset.card_erase_of_mem (by simp [hf i]),hI i]
  have hJ' (j : J) : (Finset.univ.filter (fun i ↦ s i j)).card = 1 := by
    have he : Finset.univ.filter (fun i ↦ s i j) =
        (Finset.univ.filter (fun i ↦ r i j)).erase (f.symm j) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,s]
      have hh : j ≠ f i ↔ i ≠ f.symm j := by
        constructor
        · intro h he; apply h; exact (f.apply_symm_apply j).symm.trans (congrArg f he.symm)
        · intro h he; apply h; exact (f.symm_apply_apply i).symm.trans (congrArg f.symm he.symm)
      rw [hh,and_comm]
    rw [he,Finset.card_erase_of_mem (by simpa using hf (f.symm j)),hJ j]
  obtain ⟨g,hg⟩ := regular_relation_matching s 1 (by omega)
    (by simpa only [s] using hI') (by simpa only [s] using hJ')
  refine ⟨f,g,fun i ↦ (hg i).2.symm,?_⟩
  intro i j
  have he : Finset.univ.filter (r i) = {f i,g i} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using hf i
      · simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using (hg i).1
    · rw [hI,Finset.card_pair (hg i).2.symm]
  have hh := Finset.ext_iff.mp he j
  simpa using hh

/-- Counting a predicate on a finite subtype agrees with filtering its carrier. -/
lemma card_filter_coe {α : Type*} (D : Finset α) (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : D ↦ P x.val)).card = (D.filter P).card := by
  classical
  apply Finset.card_bij (fun x _ ↦ x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.property,(Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    obtain ⟨hxD,hxP⟩ := Finset.mem_filter.mp hx
    exact ⟨⟨x,hxD⟩,by simpa using hxP,rfl⟩

/-- The endpoints of a normal Eulerian decomposition can be oriented so that
each active vertex occurs exactly once as a start and once as a finish. -/
lemma orient_eulerian_normal {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ v, endpointMultiplicity D v ≤ 2)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ f g : D ≃ {v : V // endpointMultiplicity D v = 2},
      (∀ H, f H ≠ g H) ∧
      ∃ p : ∀ H : D, G.Walk (f H).val (g H).val,
        (∀ H, (p H).IsPath) ∧ ∀ H, H.val = (p H).toSubgraph := by
  classical
  let J := {v : V // endpointMultiplicity D v = 2}
  let r (H : D) (v : J) := (H.val.neighborSet v.val).ncard = 1
  have htwo (H : D) (v : V) (hv : (H.val.neighborSet v).ncard = 1) :
      endpointMultiplicity D v = 2 := by
    have hp : 0 < endpointMultiplicity D v := Finset.card_pos.mpr
      ⟨H.val,Finset.mem_filter.mpr ⟨H.property,hv⟩⟩
    have hbound := hb v
    have hn := Nat.not_odd_iff_even.mpr (heven v)
    have hn1 : endpointMultiplicity D v ≠ 1 := by
      intro he
      apply hn
      apply (hD.odd_endpointMultiplicity_iff v).mp
      rw [he]
      decide
    omega
  have hI (H : D) : (Finset.univ.filter (r H)).card = 2 := by
    obtain ⟨a,b,p,hp,he⟩ := hD.1 H.val H.property
    have hab : a ≠ b := path_endpoints_ne hp (he ▸ hne H.val H.property)
    have hn : ¬p.Nil := Walk.not_nil_of_ne hab
    have hend (v : V) : (H.val.neighborSet v).ncard = 1 ↔ v = a ∨ v = b := by
      rw [he,path_neighbor_ncard_formula hp hn]
      split_ifs <;> simp_all
    let a' : J := ⟨a,htwo H a ((hend a).mpr (Or.inl rfl))⟩
    let b' : J := ⟨b,htwo H b ((hend b).mpr (Or.inr rfl))⟩
    have heq : Finset.univ.filter (r H) = {a',b'} := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton,r,hend]
      exact or_congr
        (show v.val = a ↔ v = a' from ⟨fun h ↦ Subtype.ext h,fun h ↦ congrArg Subtype.val h⟩)
        (show v.val = b ↔ v = b' from ⟨fun h ↦ Subtype.ext h,fun h ↦ congrArg Subtype.val h⟩)
    rw [heq,Finset.card_pair (fun h ↦ hab (congrArg Subtype.val h))]
  have hJ (v : J) : (Finset.univ.filter (fun H ↦ r H v)).card = 2 := by
    change (Finset.univ.filter (fun H : D ↦ (H.val.neighborSet v.val).ncard = 1)).card = 2
    exact (card_filter_coe D (fun H ↦ (H.neighborSet v.val).ncard = 1)).trans v.property
  obtain ⟨f,g,hfg,hrel⟩ := two_regular_relation r hI hJ
  have hw (H : D) : ∃ p : G.Walk (f H).val (g H).val,
      p.IsPath ∧ H.val = p.toSubgraph := by
    have ha : (H.val.neighborSet (f H).val).ncard = 1 := (hrel H (f H)).mpr (Or.inl rfl)
    obtain ⟨b,p,hp,he⟩ := path_endpoint_of_neighbor_ncard_one (hD.1 H.val H.property) ha
    have hab : (f H).val ≠ b := path_endpoints_ne hp (he ▸ hne H.val H.property)
    have hn : ¬p.Nil := Walk.not_nil_of_ne hab
    have hg : (H.val.neighborSet (g H).val).ncard = 1 := (hrel H (g H)).mpr (Or.inr rfl)
    have hb' : (g H).val = b := by
      rw [he,path_neighbor_ncard_formula hp hn] at hg
      have hne' : (g H).val ≠ (f H).val := fun he ↦ hfg H (Subtype.ext he.symm)
      split_ifs at hg <;> simp_all
    exact ⟨p.copy rfl hb'.symm,by simpa using hp,by rw [NormalTrailSystem.walk_copy_subgraph]; exact he⟩
  choose p hp he using hw
  exact ⟨f,g,hfg,p,hp,he⟩

/-- A path leaves each vertex and ends at its image under a permutation.
The nil paths are precisely the fixed points. All edges occur exactly once. -/
structure PermutationPathSystem {V : Type*} (G : SimpleGraph V) where
  perm : Equiv.Perm V
  walk : ∀ v, G.Walk v (perm v)
  isPath : ∀ v, (walk v).IsPath
  disjoint : Pairwise fun v w ↦ Disjoint (walk v).toSubgraph.edgeSet (walk w).toSubgraph.edgeSet
  cover : ∀ e, e ∈ G.edgeSet ↔ ∃ v, e ∈ (walk v).toSubgraph.edgeSet

/-- Every normal Eulerian partition can be represented by a permutation,
with exactly its inactive vertices as fixed points. -/
lemma permutation_of_normal {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ v, endpointMultiplicity D v ≤ 2)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ T : PermutationPathSystem G, (∀ v, T.perm v = v ↔ v ∈ inactive D) ∧
      D = (Finset.univ.filter (fun v ↦ T.perm v ≠ v)).image (fun v ↦ (T.walk v).toSubgraph) := by
  classical
  obtain ⟨f,g,hfg,p,hp,he⟩ := orient_eulerian_normal hD hne hb heven
  let J := {v : V // endpointMultiplicity D v = 2}
  let σ : Equiv.Perm V := Equiv.Perm.subtypeCongr (f.symm.trans g) (Equiv.refl _)
  have hσ (H : D) : σ (f H).val = (g H).val := by simp [σ]
  have hσout (v : V) (hv : endpointMultiplicity D v ≠ 2) : σ v = v := by simp [σ,hv]
  have hzero (v : V) : endpointMultiplicity D v ≠ 2 ↔ endpointMultiplicity D v = 0 := by
    have hbound := hb v
    have hnot1 : endpointMultiplicity D v ≠ 1 := by
      intro hh
      apply Nat.not_odd_iff_even.mpr (heven v)
      apply (hD.odd_endpointMultiplicity_iff v).mp
      rw [hh]
      decide
    omega
  have hfix (v : V) : σ v = v ↔ v ∈ inactive D := by
    by_cases hv : endpointMultiplicity D v = 2
    · have hne' : σ v ≠ v := by
        let H := f.symm ⟨v,hv⟩
        have hfH : (f H).val = v := congrArg Subtype.val (f.apply_symm_apply ⟨v,hv⟩)
        intro hh
        apply hfg H
        apply Subtype.ext
        rw [hfH,← hσ H,hfH,hh]
      simp [hne',inactive,hv]
    · simp [hσout v hv,inactive,(hzero v).mp hv]
  have hw (v : V) : ∃ q : G.Walk v (σ v), q.IsPath ∧
      (∀ hv : endpointMultiplicity D v = 2, q.toSubgraph = (f.symm ⟨v,hv⟩).val) ∧
      (endpointMultiplicity D v ≠ 2 → q.Nil) := by
    by_cases hv : endpointMultiplicity D v = 2
    · let H := f.symm ⟨v,hv⟩
      have ha : (f H).val = v := congrArg Subtype.val (f.apply_symm_apply ⟨v,hv⟩)
      have hz : (g H).val = σ v := (hσ H).symm.trans (congrArg σ ha)
      refine ⟨(p H).copy ha hz,by simpa using hp H,?_,fun hn ↦ (hn hv).elim⟩
      intro _
      rw [NormalTrailSystem.walk_copy_subgraph]
      exact (he H).symm
    · refine ⟨(Walk.nil : G.Walk v v).copy rfl (hσout v hv).symm,by simp,fun h ↦ (hv h).elim,?_⟩
      intro _
      simp
  choose q hq hqsub hqnil using hw
  have hdis : Pairwise fun v w ↦ Disjoint (q v).toSubgraph.edgeSet (q w).toSubgraph.edgeSet := by
    intro v w hvw
    by_cases hv : endpointMultiplicity D v = 2
    · by_cases hw : endpointMultiplicity D w = 2
      · rw [hqsub v hv,hqsub w hw]
        apply hD.2.1 (f.symm ⟨v,hv⟩).property (f.symm ⟨w,hw⟩).property
        intro hh
        apply hvw
        exact congrArg Subtype.val (f.symm.injective (Subtype.ext hh))
      · have hz : (q w).toSubgraph.edgeSet = ∅ := by
          ext e
          simp [Walk.edges_eq_nil.mpr (hqnil w hw)]
        rw [hz]
        exact disjoint_bot_right
    · have hz : (q v).toSubgraph.edgeSet = ∅ := by
        ext e
        simp [Walk.edges_eq_nil.mpr (hqnil v hv)]
      rw [hz]
      exact disjoint_bot_left
  have hcover (e : Sym2 V) : e ∈ G.edgeSet ↔ ∃ v, e ∈ (q v).toSubgraph.edgeSet := by
    constructor
    · intro hedge
      rw [← hD.2.2] at hedge
      obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp hedge
      let H' : D := ⟨H,hH⟩
      refine ⟨(f H').val,?_⟩
      rw [hqsub _ (f H').property]
      simpa using heH
    · rintro ⟨v,hv⟩
      exact (q v).toSubgraph.edgeSet_subset hv
  let T : PermutationPathSystem G :=
    { perm := σ,walk := q,isPath := hq,disjoint := hdis,cover := hcover }
  refine ⟨T,hfix,?_⟩
  ext H
  constructor
  · intro hH
    let H' : D := ⟨H,hH⟩
    refine Finset.mem_image.mpr ⟨(f H').val,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change σ (f H').val ≠ (f H').val
      rw [hσ]
      exact fun hh ↦ hfg H' (Subtype.ext hh.symm)
    · change (q (f H').val).toSubgraph = H
      rw [hqsub _ (f H').property]
      simp [H']
  · intro hH
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hH
    have hv' : endpointMultiplicity D v = 2 := by
      by_contra hn
      exact (Finset.mem_filter.mp hv).2 (hσout v hn)
    change (q v).toSubgraph ∈ D
    rw [hqsub v hv']
    exact (f.symm ⟨v,hv'⟩).property

lemma exists_permutation_path_system {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (heven : ∀ v, Even (G.degree v)) :
    Nonempty (PermutationPathSystem G) := by
  obtain ⟨D,hD,hne,hb⟩ := exists_normal_decomposition G
  obtain ⟨T,_,_⟩ := permutation_of_normal hD hne (fun v ↦ (hb v).1) heven
  exact ⟨T⟩

namespace PermutationPathSystem

lemma nil_iff_fixed {V : Type*} {G : SimpleGraph V} (T : PermutationPathSystem G) (v : V) :
    (T.walk v).Nil ↔ T.perm v = v := by
  constructor
  · intro h
    exact h.eq.symm
  · intro h
    let p := (T.walk v).copy rfl h
    have hp : p.IsPath := by simpa only [p,Walk.isPath_copy] using T.isPath v
    have hh : p = Walk.nil := (Walk.isPath_iff_eq_nil p).mp hp
    have hn : p.Nil := hh ▸ Walk.Nil.nil
    simpa [p] using hn

noncomputable def fixed {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : PermutationPathSystem G) : Finset V := Finset.univ.filter fun v ↦ T.perm v = v

noncomputable def moved {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : PermutationPathSystem G) : Finset V := Finset.univ.filter fun v ↦ T.perm v ≠ v

noncomputable def parts {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : PermutationPathSystem G) : Finset G.Subgraph :=
  T.moved.image fun v ↦ (T.walk v).toSubgraph

lemma edgeSet_nonempty {V : Type*} {G : SimpleGraph V} (T : PermutationPathSystem G)
    {v : V} (hv : T.perm v ≠ v) : (T.walk v).toSubgraph.edgeSet.Nonempty := by
  have hn : ¬(T.walk v).Nil := fun h ↦ hv ((T.nil_iff_fixed v).mp h)
  exact ⟨s(v,(T.walk v).snd),(T.walk v).toSubgraph_adj_snd hn⟩

lemma parts_good {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : PermutationPathSystem G) : GoodDecomposition G T.parts := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro H hH
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hH
    exact ⟨v,T.perm v,T.walk v,T.isPath v,rfl⟩
  · intro H hH K hK hHK
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hK
    exact T.disjoint (fun hh ↦ hHK (congrArg (fun x ↦ (T.walk x).toSubgraph) hh))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨H,_,he⟩
      exact H.edgeSet_subset he
    · intro he
      obtain ⟨v,hv⟩ := (T.cover e).mp he
      have hm : T.perm v ≠ v := by
        intro hh
        have hn := (T.nil_iff_fixed v).mpr hh
        have hnil := Walk.edges_eq_nil.mpr hn
        simp [hnil] at hv
      exact ⟨(T.walk v).toSubgraph,
        Finset.mem_image.mpr ⟨v,by simpa [moved] using hm,rfl⟩,hv⟩

lemma parts_nonempty {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : PermutationPathSystem G) : ∀ H ∈ T.parts, H.edgeSet.Nonempty := by
  intro H hH
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hH
  exact T.edgeSet_nonempty ((Finset.mem_filter.mp hv).2)

lemma parts_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : PermutationPathSystem G) : T.parts.card = T.moved.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro v hv w _ he
  dsimp only at he
  by_contra hne
  obtain ⟨e,hedge⟩ := T.edgeSet_nonempty ((Finset.mem_filter.mp hv).2)
  have hd := T.disjoint hne
  exact Set.disjoint_left.mp hd hedge (by rwa [← he])

lemma parts_card_add_fixed {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : PermutationPathSystem G) : T.parts.card + T.fixed.card = Fintype.card V := by
  classical
  rw [T.parts_card]
  have hd : Disjoint T.moved T.fixed := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hv').2
  have hu : T.moved ∪ T.fixed = Finset.univ := by
    ext v
    simp only [moved,fixed,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    exact iff_true_intro (em (T.perm v = v)).symm
  rw [← Finset.card_union_of_disjoint hd,hu,Finset.card_univ]

/-- In this representation, the numerical Gallai target is exactly the demand
for at least half (rounded down) of the vertices to be fixed points. -/
lemma gallai_iff_fixed {V : Type*} [Fintype V] {G : SimpleGraph V}
    (T : PermutationPathSystem G) :
    T.parts.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ ↔ Fintype.card V / 2 ≤ T.fixed.card := by
  have hc := T.parts_card_add_fixed
  have hlo : Fintype.card V ≤ 2*⌈(Fintype.card V : ℚ)/2⌉₊ := by
    have hh := Nat.le_ceil ((Fintype.card V : ℚ)/2)
    exact_mod_cast (show (Fintype.card V : ℚ) ≤ 2*(⌈(Fintype.card V : ℚ)/2⌉₊ : ℚ) by linarith)
  have hhi : 2*⌈(Fintype.card V : ℚ)/2⌉₊ < Fintype.card V + 2 := by
    have hh := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (Fintype.card V : ℚ)/2 by positivity)
    exact_mod_cast (show 2*(⌈(Fintype.card V : ℚ)/2⌉₊ : ℚ) < (Fintype.card V : ℚ) + 2 by linarith)
  omega

end PermutationPathSystem

end Erdos583PermutationDevelopment
