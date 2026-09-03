import Submission.Work

/-! Marked endpoint projection from two copies joined by one bridge.
Nil pieces at the cut are retained. -/
open SimpleGraph Erdos583Work
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
namespace Erdos583MarkedDoubleDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- Some member has a simple-walk representation starting at the given vertex.
The walk may be nil. -/
def MarkedAt {V : Type*} {G : SimpleGraph V} (D : Finset G.Subgraph) (v : V) : Prop :=
  ∃ a, ∃ p : G.Walk v a, p.IsPath ∧ p.toSubgraph ∈ D

lemma MarkedAt.mono {V : Type*} {G : SimpleGraph V} {D E : Finset G.Subgraph} {v : V}
    (h : MarkedAt D v) (hDE : D ⊆ E) : MarkedAt E v := by
  obtain ⟨a,p,hp,hm⟩ := h
  exact ⟨a,p,hp,hDE hm⟩

lemma split_path_delete_edge_marked {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (e : Sym2 V) :
    ∃ E : Finset (G.deleteEdges {e}).Subgraph,
      (∀ H ∈ E, IsPathSubgraph H) ∧
      Set.PairwiseDisjoint (E : Set (G.deleteEdges {e}).Subgraph) (fun H ↦ H.edgeSet) ∧
      (⋃ H ∈ E, H.edgeSet) = p.toSubgraph.edgeSet \ {e} ∧
      (E.card ≤ if e ∈ p.edges then 2 else 1) ∧
      ∀ a b, e=s(a,b) → e ∈ p.edges → MarkedAt E a ∧ MarkedAt E b := by
  classical
  by_cases he : e ∈ p.edges
  · obtain ⟨a, b, hab, q, r, rfl, rfl⟩ := walk_split_at_edge p e he
    have hq := hp.of_append_left
    have hr := (Walk.cons_isPath_iff hab r).mp hp.of_append_right |>.1
    have hn := hp.isTrail.edges_nodup
    simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append, List.nodup_cons] at hn
    have heq : s(a, b) ∉ q.edges := fun h ↦ hn.2.2 _ h _ (List.mem_cons_self ..) rfl
    have her : s(a, b) ∉ r.edges := hn.2.1.1
    have hqF : ∀ z ∈ q.edges, z ∈ (G.deleteEdges {s(a, b)}).edgeSet := by
      intro z hz
      rw [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
      exact ⟨q.edges_subset_edgeSet hz, fun h ↦ heq (h ▸ hz)⟩
    have hrF : ∀ z ∈ r.edges, z ∈ (G.deleteEdges {s(a, b)}).edgeSet := by
      intro z hz
      rw [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
      exact ⟨r.edges_subset_edgeSet hz, fun h ↦ her (h ▸ hz)⟩
    let A := (q.transfer _ hqF).toSubgraph
    let B := (r.transfer _ hrF).toSubgraph
    have hAe : A.edgeSet = q.edgeSet := by
      ext z; simp [A, Walk.edgeSet_toSubgraph, Walk.mem_edgeSet]
    have hBe : B.edgeSet = r.edgeSet := by
      ext z; simp [B, Walk.edgeSet_toSubgraph, Walk.mem_edgeSet]
    have hd : Disjoint A.edgeSet B.edgeSet := by
      rw [hAe, hBe]
      apply Set.disjoint_left.mpr
      intro z hz hz'
      exact hn.2.2 _ hz _ (List.mem_cons_of_mem _ hz') rfl
    refine ⟨{A, B}, ?_, ?_, ?_, ?_, ?_⟩
    · intro H hH
      simp only [Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact ⟨u, a, _, hq.transfer _, rfl⟩
      · exact ⟨b, v, _, hr.transfer _, rfl⟩
    · intro X hX Y hY hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hX hY
      rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
      · exact (hne rfl).elim
      · exact hd
      · exact hd.symm
      · exact (hne rfl).elim
    · ext z
      simp only [Set.mem_iUnion, Finset.mem_insert, Finset.mem_singleton, Set.mem_diff,
        Walk.edgeSet_toSubgraph, Walk.edges_append, Walk.edges_cons,
        List.mem_append, List.mem_cons, Set.mem_singleton_iff]
      constructor
      · rintro ⟨H, rfl | rfl, hz⟩
        · rw [hAe] at hz
          exact ⟨Or.inl hz, fun h ↦ heq (h ▸ hz)⟩
        · rw [hBe] at hz
          exact ⟨Or.inr (Or.inr hz), fun h ↦ her (h ▸ hz)⟩
      · rintro ⟨hz | hz | hz, hne⟩
        · exact ⟨A, Or.inl rfl, hAe.symm ▸ hz⟩
        · exact (hne hz).elim
        · exact ⟨B, Or.inr rfl, hBe.symm ▸ hz⟩
    · rw [if_pos he]
      exact (Finset.card_insert_le A {B}).trans (by simp)
    · intro x y hxy _
      have hmA : MarkedAt ({A,B} : Finset (G.deleteEdges {s(a,b)}).Subgraph) a := by
        refine ⟨u,(q.transfer _ hqF).reverse,(hq.transfer _).reverse,?_⟩
        simpa only [Walk.toSubgraph_reverse] using Finset.mem_insert_self A {B}
      have hmB : MarkedAt ({A,B} : Finset (G.deleteEdges {s(a,b)}).Subgraph) b :=
        ⟨v,r.transfer _ hrF,hr.transfer _,Finset.mem_insert_of_mem (Finset.mem_singleton_self B)⟩
      rcases Sym2.eq_iff.mp hxy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨hmA,hmB⟩
      · exact ⟨hmB,hmA⟩
  · have hpF : ∀ z ∈ p.edges, z ∈ (G.deleteEdges {e}).edgeSet := by
      intro z hz
      rw [edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
      exact ⟨p.edges_subset_edgeSet hz, fun h ↦ he (h ▸ hz)⟩
    let A := (p.transfer _ hpF).toSubgraph
    have hAe : A.edgeSet = p.toSubgraph.edgeSet := by simp [A, Walk.edgeSet_toSubgraph]
    refine ⟨{A}, ?_, ?_, ?_, ?_, ?_⟩
    · intro H hH
      have : H = A := Finset.mem_singleton.mp hH
      subst H
      exact ⟨u, v, _, hp.transfer _, rfl⟩
    · intro X hX Y hY hne
      simp only [Finset.mem_coe, Finset.mem_singleton] at hX hY
      exact (hne (hX.trans hY.symm)).elim
    · simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, hAe]
      exact (Set.diff_singleton_eq_self (by simpa using he)).symm
    · simp only [Finset.card_singleton]
      split_ifs; omega
    · intro _ _ _ hm; exact (he hm).elim

lemma refine_decomposition_tracked {V : Type*} {G J : SimpleGraph V} (hJG : J ≤ G)
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (f : D → Finset J.Subgraph)
    (hp : ∀ H, ∀ L ∈ f H, IsPathSubgraph L)
    (hd : ∀ H, Set.PairwiseDisjoint (f H : Set J.Subgraph) (fun L ↦ L.edgeSet))
    (hc : ∀ H, (⋃ L ∈ f H, L.edgeSet) = H.val.edgeSet ∩ J.edgeSet) :
    ∃ E : Finset J.Subgraph, GoodDecomposition J E ∧ E.card ≤ ∑ H, (f H).card ∧
      ∀ H, f H ⊆ E := by
  classical
  let E := Finset.univ.biUnion f
  have hsub (H : D) (L : J.Subgraph) (hL : L ∈ f H) : L.edgeSet ⊆ H.val.edgeSet := by
    intro e he
    have h : e ∈ ⋃ L ∈ f H, L.edgeSet := Set.mem_iUnion.mpr ⟨L, Set.mem_iUnion.mpr ⟨hL, he⟩⟩
    rw [hc] at h
    exact h.1
  refine ⟨E, ⟨?_, ?_, ?_⟩, Finset.card_biUnion_le,fun H L hL ↦ Finset.mem_biUnion.mpr ⟨H,Finset.mem_univ _,hL⟩⟩
  · intro L hL
    obtain ⟨H, _, hL⟩ := Finset.mem_biUnion.mp hL
    exact hp H L hL
  · intro L hL M hM hne
    obtain ⟨H, _, hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨K, _, hM⟩ := Finset.mem_biUnion.mp hM
    by_cases hHK : H = K
    · subst K
      exact hd H hL hM hne
    · exact (hD.2.1 H.property K.property (fun h ↦ hHK (Subtype.ext h))).mono
        (hsub H L hL) (hsub K M hM)
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨L, _, he⟩
      exact L.edgeSet_subset he
    · intro he
      have heG : e ∈ G.edgeSet := edgeSet_mono hJG he
      rw [← hD.2.2] at heG
      obtain ⟨H, hH, heH⟩ := Set.mem_iUnion.mp heG |>.imp (fun _ h ↦ Set.mem_iUnion.mp h)
      have hh : e ∈ ⋃ L ∈ f ⟨H, hH⟩, L.edgeSet := (hc ⟨H, hH⟩).symm ▸ ⟨heH, he⟩
      simp only [Set.mem_iUnion] at hh
      obtain ⟨L, hL, heL⟩ := hh
      exact ⟨L, Finset.mem_biUnion.mpr ⟨⟨H, hH⟩, Finset.mem_univ _, hL⟩, heL⟩


lemma delete_edge_decomposition_marked {V : Type*} {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D) (e : G.edgeSet) :
    ∃ E : Finset (G.deleteEdges {e.val}).Subgraph,
      GoodDecomposition (G.deleteEdges {e.val}) E ∧ E.card ≤ D.card + 1 ∧
        ∀ a b, e.val=s(a,b) → MarkedAt E a ∧ MarkedAt E b := by
  classical
  have heG : e.val ∈ ⋃ H ∈ D, H.edgeSet := hD.2.2.symm ▸ e.property
  simp only [Set.mem_iUnion] at heG
  obtain ⟨H₀, hH₀, heH₀⟩ := heG
  let H0 : D := ⟨H₀, hH₀⟩
  have hparts (H : D) :
      ∃ E : Finset (G.deleteEdges {e.val}).Subgraph,
        (∀ L ∈ E, IsPathSubgraph L) ∧
        Set.PairwiseDisjoint (E : Set (G.deleteEdges {e.val}).Subgraph) (fun L ↦ L.edgeSet) ∧
        (⋃ L ∈ E, L.edgeSet) = H.val.edgeSet ∩ (G.deleteEdges {e.val}).edgeSet ∧
        (E.card ≤ if H = H0 then 2 else 1) ∧
        ∀ a b, e.val=s(a,b) → e.val ∈ H.val.edgeSet → MarkedAt E a ∧ MarkedAt E b := by
    obtain ⟨u, v, p, hp, hHp⟩ := hD.1 H.val H.property
    obtain ⟨E, hpE, hdE, hcE, hnE, hmE⟩ := split_path_delete_edge_marked p hp e.val
    refine ⟨E, hpE, hdE, ?_, ?_, ?_⟩
    · rw [hcE, ← hHp, edgeSet_deleteEdges]
      ext z
      constructor
      · rintro ⟨h, hn⟩
        exact ⟨h, H.val.edgeSet_subset h, hn⟩
      · rintro ⟨h, _, hn⟩
        exact ⟨h, hn⟩
    · have heiff : e.val ∈ p.edges ↔ H = H0 := by
        rw [← p.mem_edges_toSubgraph, ← hHp]
        constructor
        · intro heH
          apply Subtype.ext
          by_contra hne
          exact Set.disjoint_left.mp (hD.2.1 H.property hH₀ hne) heH heH₀
        · rintro rfl
          exact heH₀
      simpa only [heiff] using hnE
    · intro a b hab heH
      exact hmE a b hab (by simpa only [←Walk.mem_edges_toSubgraph,←hHp] using heH)
  choose f hp hd hc hn hm using hparts
  obtain ⟨E, hE, hnE, hpartsE⟩ := refine_decomposition_tracked (G.deleteEdges_le _) hD f hp hd hc
  refine ⟨E, hE, hnE.trans ((Finset.sum_le_sum fun H _ ↦ hn H).trans ?_),?_⟩
  · have hi (H : D) : (if H = H0 then 2 else 1) = 1 + if H = H0 then 1 else 0 := by
      split_ifs <;> rfl
    simp_rw [hi, Finset.sum_add_distrib]
    simp
  · intro a b hab
    obtain ⟨ha,hb⟩ := hm H0 a b hab heH₀
    exact ⟨ha.mono (hpartsE H0),hb.mono (hpartsE H0)⟩


lemma project_unpaired_path_tracked {V : Type*} {G : SimpleGraph V}
    {H : (pairedCopies G ∅).Subgraph} (hpH : IsPathSubgraph H) :
    ∃ (b : Bool) (K : G.Subgraph), IsPathSubgraph K ∧
      H.edgeSet = Sym2.map (fun v ↦ (b, v)) '' K.edgeSet ∧
      H.map (unpairedCopies_projection G)=K ∧ ∀ x ∈ H.verts, x.1=b := by
  obtain ⟨u, v, p, hp, rfl⟩ := hpH
  let q := p.map (unpairedCopies_projection G)
  have hq : q.IsPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_map]
    apply List.Nodup.map_on _ hp.support_nodup
    intro x hx y hy he
    exact Prod.ext ((unpairedCopies_walk_support p x hx).trans
      (unpairedCopies_walk_support p y hy).symm) he
  refine ⟨u.1, q.toSubgraph, ⟨u.2, v.2, q, hq, rfl⟩, ?_, ?_, ?_⟩
  · have hl (e : Sym2 (Bool × V)) (he : e ∈ p.edgeSet) :
        Sym2.map (fun w ↦ (u.1, w)) (Sym2.map Prod.snd e) = e := by
      induction e using Sym2.ind with
      | h x y =>
        have hx := unpairedCopies_walk_support p x (Walk.mem_support_of_mem_edges he (by simp))
        have hy := unpairedCopies_walk_support p y (Walk.mem_support_of_mem_edges he (by simp))
        have hex : (u.1, x.2) = x := Prod.ext hx.symm rfl
        have hey : (u.1, y.2) = y := Prod.ext hy.symm rfl
        simpa using congrArg₂ (fun a b ↦ s(a, b)) hex hey
    simp only [Walk.edgeSet_toSubgraph, ← Walk.mem_edgeSet, Set.setOf_mem_eq]
    change p.edgeSet = Sym2.map (fun w ↦ (u.1, w)) '' q.edgeSet
    rw [Walk.edgeSet_map, Set.image_image]
    change p.edgeSet = (fun e ↦ Sym2.map (fun w ↦ (u.1, w)) (Sym2.map Prod.snd e)) '' p.edgeSet
    ext e
    constructor
    · intro he
      exact ⟨e, he, hl e he⟩
    · rintro ⟨z, hz, rfl⟩
      change Sym2.map (fun w ↦ (u.1, w)) (Sym2.map Prod.snd z) ∈ p.edgeSet
      rw [hl z hz]
      exact hz
  · simp only [q,Walk.toSubgraph_map]
  · intro x hx
    exact unpairedCopies_walk_support p x (p.mem_verts_toSubgraph.mp hx)

lemma decompose_one_of_two_copies_marked {V : Type*} {G : SimpleGraph V}
    {D : Finset (pairedCopies G ∅).Subgraph} (hD : GoodDecomposition (pairedCopies G ∅) D) (u : V)
    (hmarks : ∀ c : Bool, MarkedAt D (c,u)) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ 2 * E.card ≤ D.card ∧ MarkedAt E u := by
  classical
  choose b f hp hl hf hv using (fun H : D ↦ project_unpaired_path_tracked (hD.1 H.val H.property))
  let I (c : Bool) : Finset D := Finset.univ.filter (fun H ↦ b H = c)
  let E (c : Bool) : Finset G.Subgraph := (I c).image f
  have hgood (c : Bool) : GoodDecomposition G (E c) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K hK
      obtain ⟨H, _, rfl⟩ := Finset.mem_image.mp hK
      exact hp H
    · intro K hK L hL hne
      obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hK
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hL
      have hbH := (Finset.mem_filter.mp hH).2
      have hbJ := (Finset.mem_filter.mp hJ).2
      apply Set.disjoint_left.mpr
      intro e heH heJ
      have hneval : H.val ≠ J.val := fun heq ↦ hne (congrArg f (Subtype.ext heq))
      have hiH : Sym2.map (fun v ↦ (c, v)) e ∈ H.val.edgeSet := by
        rw [hl H, hbH]
        exact ⟨e, heH, rfl⟩
      have hiJ : Sym2.map (fun v ↦ (c, v)) e ∈ J.val.edgeSet := by
        rw [hl J, hbJ]
        exact ⟨e, heJ, rfl⟩
      exact Set.disjoint_left.mp (hD.2.1 H.property J.property hneval) hiH hiJ
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨K, _, he⟩
        exact K.edgeSet_subset he
      · intro he
        have hec : Sym2.map (fun v ↦ (c, v)) e ∈ (pairedCopies G ∅).edgeSet := by
          induction e using Sym2.ind with
          | h x y => exact Or.inl ⟨rfl, he⟩
        have heD : Sym2.map (fun v ↦ (c, v)) e ∈ ⋃ H ∈ D, H.edgeSet := hD.2.2.symm ▸ hec
        simp only [Set.mem_iUnion] at heD
        obtain ⟨H, hH, heH⟩ := heD
        rw [hl ⟨H, hH⟩] at heH
        obtain ⟨e', he', heq⟩ := heH
        obtain ⟨hb, rfl⟩ := copy_edge_injective heq
        exact ⟨f ⟨H, hH⟩, Finset.mem_image.mpr ⟨⟨H, hH⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩, he'⟩
  have hmarked (c : Bool) : MarkedAt (E c) u := by
    obtain ⟨a,p,hp,hm⟩ := hmarks c
    have hb : b ⟨p.toSubgraph,hm⟩=c :=
      (hv ⟨p.toSubgraph,hm⟩ (c,u) (p.mem_verts_toSubgraph.mpr p.start_mem_support)).symm
    let q := p.map (unpairedCopies_projection G)
    have hq : q.IsPath := by
      apply Walk.IsPath.mk'
      rw [Walk.support_map]
      apply List.Nodup.map_on _ hp.support_nodup
      intro x hx y hy he
      exact Prod.ext ((unpairedCopies_walk_support p x hx).trans
        (unpairedCopies_walk_support p y hy).symm) he
    have hqe : q.toSubgraph=f ⟨p.toSubgraph,hm⟩ := by
      simpa only [q,Walk.toSubgraph_map] using hf ⟨p.toSubgraph,hm⟩
    refine ⟨a.2,q,hq,?_⟩
    rw [hqe]
    exact Finset.mem_image.mpr ⟨⟨p.toSubgraph,hm⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩
  have hsum : (I false).card + (I true).card = D.card := by
    simpa [I, Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D)) (fun H ↦ b H = false))
  have hfalse : (E false).card ≤ (I false).card := Finset.card_image_le
  have htrue : (E true).card ≤ (I true).card := Finset.card_image_le
  by_cases h : 2 * (E false).card ≤ D.card
  · exact ⟨E false, hgood false, h,hmarked false⟩
  · exact ⟨E true, hgood true, by omega,hmarked true⟩


lemma marked_of_double_bridge {V : Type*} [Fintype V] {G : SimpleGraph V} (u : V)
    {D : Finset (pairedCopies G {u}).Subgraph} (hD : GoodDecomposition (pairedCopies G {u}) D)
    (hn : D.card ≤ Fintype.card V) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ ∧ MarkedAt E u := by
  have he : s((false,u),(true,u)) ∈ (pairedCopies G {u}).edgeSet := Or.inr ⟨by simp,rfl,rfl⟩
  have hdel := delete_edge_decomposition_marked hD ⟨_,he⟩
  rw [pairedCopies_delete_bridge] at hdel
  obtain ⟨E,hE,hEc,hm⟩ := hdel
  obtain ⟨F,hF,hFc,hFm⟩ := decompose_one_of_two_copies_marked hE u (by
    intro c
    have hh := hm (false,u) (true,u) rfl
    cases c
    · exact hh.1
    · exact hh.2)
  exact ⟨F,hF,by rw [ceil_half]; omega,hFm⟩

/-- Strictly below half the minimal order, the smaller-order hypothesis gives
the ordinary ceiling budget with an arbitrary specified marked vertex. -/
lemma marked_of_twice_order_lt {n : ℕ} (hsmall : SmallerOrders n)
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (u : V)
    (hsize : 2*Fintype.card V < n) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ ∧ MarkedAt D u := by
  obtain ⟨D,hD,hDc⟩ := hsmall.on_finite (pairedCopies G {u})
    (by simpa only [Fintype.card_prod,Fintype.card_bool] using hsize)
    (pairedCopies_connected G hG {u} ⟨u,rfl⟩)
  apply marked_of_double_bridge u hD
  simp only [Fintype.card_prod,Fintype.card_bool,ceil_half] at hDc
  omega

lemma failure_cut_side_half_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) (hS : 2 ≤ S.ncard) :
    n ≤ 2*S.ncard := by
  classical
  by_contra hn
  have hconn := CutVertexReduction.single_boundary_connected hG S u hu
    (fun x hx y hy hxy ↦ (hcross x hx y hy hxy).1)
  have hcard : Fintype.card S=S.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨D,hD,hDc,a,p,hp,hm⟩ := marked_of_twice_order_lt hsmall (G.induce S) hconn ⟨u,hu⟩
    (by rw [hcard]; omega)
  exact hfail (MarkedBudgets.gallai_of_marked_bridge_side hsmall hG S h hu hv hcross hS hD p hp hm
    (by simpa only [hcard] using hDc))

/-- A nontrivial bridge cut of a smallest-order failure has two equal,
even-order sides. -/
lemma failure_cut_balanced {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    (hS : 2 ≤ S.ncard) (hcS : 2 ≤ Sᶜ.ncard) :
    S.ncard=Sᶜ.ncard ∧ 2*S.ncard=n ∧ Even S.ncard := by
  have ha := failure_cut_side_half_bound hsmall hG hfail S h hu hv hcross hS
  have hcross' : ∀ x ∈ Sᶜ, ∀ y ∉ Sᶜ, G.Adj x y → x=v ∧ y=u := by
    intro x hx y hy hxy
    have hyS : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
    exact (hcross y hyS x hx hxy.symm).symm
  have hb := failure_cut_side_half_bound hsmall hG hfail Sᶜ h.symm hv (not_not.mpr hu) hcross' hcS
  have hs : S.ncard+Sᶜ.ncard=n := by simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using S.ncard_add_ncard_compl
  have he := hsmall.bridge_cut_even hG hfail S h hu hv hcross hS hcS
  exact ⟨by omega,by omega,he.1⟩

lemma failure_bridge_balanced {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hb : G.IsBridge s(u,v)) :
    ∃ S : Set (Fin n), u ∈ S ∧ v ∉ S ∧
      (∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) ∧
      (S.ncard=1 ∨ Sᶜ.ncard=1 ∨ ∃ k, 0 < k ∧ S.ncard=2*k ∧ Sᶜ.ncard=2*k ∧ n=4*k) := by
  obtain ⟨S,hu,hv,hcross⟩ := bridge_cut hb
  refine ⟨S,hu,hv,hcross,?_⟩
  have hS : 0 < S.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨u,hu⟩
  have hcS : 0 < Sᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v,hv⟩
  by_cases hs : S.ncard=1
  · exact Or.inl hs
  by_cases ht : Sᶜ.ncard=1
  · exact Or.inr (Or.inl ht)
  obtain ⟨heq,hn,k,hk⟩ := failure_cut_balanced hsmall hG hfail S (isBridge_iff.mp hb).1 hu hv hcross
    (by omega) (by omega)
  exact Or.inr (Or.inr ⟨k,by omega,by omega,by omega,by omega⟩)

/-- Unless four divides the minimal order, every bridge is a leaf edge. -/
lemma bridge_leaf_or_four_dvd {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hb : G.IsBridge s(u,v)) :
    Nat.card (G.neighborSet u)=1 ∨ Nat.card (G.neighborSet v)=1 ∨ 4 ∣ n := by
  obtain ⟨S,hu,hv,hcross,hS|hS|⟨k,_,_,_,hk⟩⟩ := failure_bridge_balanced hsmall hG hfail hb
  · exact Or.inl (cut_singleton_degree S (isBridge_iff.mp hb).1 hu hcross hS)
  · apply Or.inr ∘ Or.inl
    apply cut_singleton_degree Sᶜ (isBridge_iff.mp hb).1.symm hv _ hS
    intro x hx y hy hxy
    have hyS : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
    exact (hcross y hyS x hx hxy.symm).symm
  · exact Or.inr (Or.inr ⟨k,hk⟩)

end Erdos583MarkedDoubleDevelopment
