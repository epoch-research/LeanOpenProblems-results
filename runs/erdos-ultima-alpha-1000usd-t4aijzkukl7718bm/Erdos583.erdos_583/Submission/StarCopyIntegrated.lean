import Submission.SingleIntersectionIntegrated

/-! Hub projection and odd-order amplification. -/
namespace Erdos583Work
/- Projection away from an added hub, and amplification of path bounds. -/
namespace StarCopyAmplification
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.StarPathPieces
open _root_.Erdos583Work.BridgeGlue _root_.Erdos583Work.MatchingCutGlue
open scoped Classical
set_option maxHeartbeats 2400000

section Projection
variable {W : Type*} (H : SimpleGraph (Option W)) (w₀ : W)

def projectHom : within H ({none}ᶜ : Set (Option W)) →g H.comap Option.some where
  toFun := fun x ↦ x.getD w₀
  map_rel' := by
    rintro x y ⟨hxy,hx,hy⟩
    cases x with
    | none => exact (hx rfl).elim
    | some x =>
      cases y with
      | none => exact (hy rfl).elim
      | some y => exact hxy

lemma outside_edges {a b : Option W} (p : H.Walk a b) (hn : none ∉ p.support) :
    ∀ e ∈ p.edges, e ∈ (within H ({none}ᶜ : Set (Option W))).edgeSet := by
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    have hxy : p.toSubgraph.Adj x y := p.mem_edges_toSubgraph.mpr he
    exact ⟨p.toSubgraph.adj_sub hxy,
      fun hx ↦ hn (hx ▸ Walk.mem_support_of_adj_toSubgraph hxy),
      fun hy ↦ hn (hy ▸ Walk.mem_support_of_adj_toSubgraph hxy.symm)⟩

noncomputable def project {a b : Option W} (p : H.Walk a b) (hn : none ∉ p.support) :
    (H.comap Option.some).Walk (a.getD w₀) (b.getD w₀) :=
  (p.transfer _ (outside_edges H p hn)).map (projectHom H w₀)

lemma project_support {a b : Option W} (p : H.Walk a b) (hn : none ∉ p.support) :
    (project H w₀ p hn).support = p.support.map (fun x ↦ x.getD w₀) := by
  simp [project,Walk.support_map,projectHom]

lemma project_isPath {a b : Option W} (p : H.Walk a b)
    (hn : none ∉ p.support) (hp : p.IsPath) : (project H w₀ p hn).IsPath := by
  rw [Walk.isPath_def,project_support]
  apply List.Nodup.map_on _ hp.support_nodup
  intro x hx y hy he
  cases x with
  | none => exact (hn hx).elim
  | some x =>
    cases y with
    | none => exact (hn hy).elim
    | some y => simpa using congrArg Option.some he

lemma project_edges {a b : Option W} (p : H.Walk a b) (hn : none ∉ p.support) :
    Sym2.map Option.some '' (project H w₀ p hn).toSubgraph.edgeSet = p.toSubgraph.edgeSet := by
  have inv (e : Sym2 (Option W)) (he : e ∈ p.edgeSet) :
      Sym2.map Option.some (Sym2.map (fun x ↦ x.getD w₀) e)=e := by
    induction e using Sym2.ind with
    | h x y =>
      have hxy : p.toSubgraph.Adj x y := p.mem_edges_toSubgraph.mpr he
      cases x with
      | none => exact (hn (Walk.mem_support_of_adj_toSubgraph hxy)).elim
      | some x =>
        cases y with
        | none => exact (hn (Walk.mem_support_of_adj_toSubgraph hxy.symm)).elim
        | some y => rfl
  simp only [Walk.edgeSet_toSubgraph,←Walk.mem_edgeSet,Set.setOf_mem_eq]
  rw [project,Walk.edgeSet_map,Walk.edgeSet_transfer,Set.image_image]
  change (fun e ↦ Sym2.map Option.some (Sym2.map (fun x ↦ x.getD w₀) e)) '' p.edgeSet=p.edgeSet
  ext e
  constructor
  · rintro ⟨f,hf,rfl⟩
    dsimp only
    rwa [inv f hf]
  · intro he
    exact ⟨e,he,inv e he⟩

include w₀ in
/-- Deleting a hub and projecting to its original vertex type costs at most
half its degree. Nil pieces are harmless: the finset image can only shrink. -/
lemma project_hub_partition [Fintype W] {k : ℕ} (T : TrailFamily H k)
    (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset (H.comap Option.some).Subgraph, GoodDecomposition (H.comap Option.some) D ∧
      2*D.card ≤ 2*k + Nat.card (H.neighborSet none) := by
  classical
  let I := AvoidIndex T none ⊕ ArmIndex T hp none
  let A (i : I) : Σ a b : Option W, H.Walk a b := match i with
    | .inl i => ⟨T.start i.val,T.finish i.val,T.walk i.val⟩
    | .inr e => ⟨(familyHalf T hp none e.val).walk.snd,
        (familyHalf T hp none e.val).finish,(familyHalf T hp none e.val).walk.tail⟩
  have hA (i : I) : (A i).2.2.IsPath ∧ none ∉ (A i).2.2.support := by
    cases i with
    | inl i => exact ⟨hp i.val,i.property⟩
    | inr e => exact ⟨(familyHalf T hp none e.val).isPath.tail,tail_avoids_center T hp none e⟩
  have hdis : Pairwise (fun i j : I ↦ Disjoint (A i).2.2.toSubgraph.edgeSet (A j).2.2.toSubgraph.edgeSet) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact T.disjoint (fun he ↦ hij (congrArg Sum.inl (Subtype.ext he)))
      | inr e =>
        have hne : i.val ≠ e.val.1 := fun he ↦ i.property (he ▸ arm_owner_touches T hp none e)
        exact (T.disjoint hne).mono_right
          ((tail_edges_subset _ e.property).trans (half_edges_subset _ (hp e.val.1) none e.val.2))
    | inr e =>
      cases j with
      | inl i =>
        have hne : i.val ≠ e.val.1 := fun he ↦ i.property (he ▸ arm_owner_touches T hp none e)
        exact ((T.disjoint hne).mono_right
          ((tail_edges_subset _ e.property).trans (half_edges_subset _ (hp e.val.1) none e.val.2))).symm
      | inr f => exact tail_disjoint T hp none (fun he ↦ hij (congrArg Sum.inr he))
  let f (i : I) := (project H w₀ (A i).2.2 (hA i).2).toSubgraph
  have hf (i : I) : Sym2.map Option.some '' (f i).edgeSet = (A i).2.2.toSubgraph.edgeSet :=
    project_edges H w₀ _ _
  obtain ⟨D,hD,hDc⟩ := indexed_decomposition f
    (fun i ↦ ⟨_,_,_,project_isPath H w₀ _ _ (hA i).1,rfl⟩)
    (by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro e hi hj
      exact Set.disjoint_left.mp (hdis hij)
        ((hf i) ▸ Set.mem_image_of_mem (Sym2.map Option.some) hi)
        ((hf j) ▸ Set.mem_image_of_mem (Sym2.map Option.some) hj))
    (by
      ext e
      constructor
      · intro he
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
        exact (f i).edgeSet_subset hi
      · intro he
        have heH : Sym2.map Option.some e ∈ (within H ({none}ᶜ : Set (Option W))).edgeSet := by
          induction e using Sym2.ind with
          | h x y => exact ⟨he,by simp,by simp⟩
        rw [outside_cover T hp none] at heH
        have hex : ∃ i : I, Sym2.map Option.some e ∈ (A i).2.2.toSubgraph.edgeSet := by
          rcases heH with heH|heH
          · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp heH
            exact ⟨Sum.inl i,hi⟩
          · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp heH
            exact ⟨Sum.inr i,hi⟩
        obtain ⟨i,hi⟩ := hex
        rw [←hf i] at hi
        obtain ⟨e',he',heq⟩ := hi
        have : e'=e := Sym2.map.injective (Option.some_injective W) heq
        subst e'
        exact Set.mem_iUnion.mpr ⟨i,he'⟩)
  have ha := Nat.card_congr (Equiv.ofBijective _ (tip_bijective_neighbor T hp none))
  change Nat.card (ArmIndex T hp none)=Nat.card (H.neighborSet none) at ha
  rw [Nat.card_eq_fintype_card] at ha
  have hb := degree_add_twice_avoid_le T hp none
  have hc : Fintype.card I=Fintype.card (AvoidIndex T none)+Nat.card (H.neighborSet none) := by
    rw [Fintype.card_sum,ha]
  simp only [←Nat.card_eq_fintype_card] at hc hDc hb
  exact ⟨D,hD,by omega⟩

end Projection
section FourCopies
variable {V : Type*} (G : SimpleGraph V) (u : V)

abbrev Four (V : Type*) := Bool × (Bool × V)

def fourGraph : SimpleGraph (Four V) := pairedCopies (pairedCopies G ∅) ∅

def fourHub : SimpleGraph (Option (Four V)) where
  Adj
    | none, none => False
    | none, some y => y.2.2=u
    | some x, none => x.2.2=u
    | some x, some y => (fourGraph G).Adj x y
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    intro x
    cases x
    · exact id
    · exact (fourGraph G).loopless _

lemma fourHub_core : (fourHub G u).comap Option.some=fourGraph G := rfl

lemma fourHub_degree : Nat.card ((fourHub G u).neighborSet none)=4 := by
  let f : Bool × Bool → (fourHub G u).neighborSet none := fun z ↦ ⟨some (z.1,(z.2,u)),rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have h' : (x.1,(x.2,u))=(y.1,(y.2,u)) := Option.some.inj (congrArg Subtype.val h)
      exact Prod.ext (congrArg (fun z : Four V ↦ z.1) h') (congrArg (fun z : Four V ↦ z.2.1) h')
    · rintro ⟨x,hx⟩
      cases x with
      | none => exact hx.elim
      | some x =>
        rcases x with ⟨b,c,v⟩
        change v=u at hx
        subst v
        exact ⟨(b,c),rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm]
  norm_num [Nat.card_eq_fintype_card]

lemma fourHub_connected (hG : G.Connected) : (fourHub G u).Connected := by
  let inc : fourGraph G →g fourHub G u := ⟨Option.some,fun h ↦ h⟩
  have hr (x : Option (Four V)) : (fourHub G u).Reachable none x := by
    cases x with
    | none => exact Reachable.refl _
    | some x =>
      rcases x with ⟨b,c,v⟩
      have hh : (fourHub G u).Adj none (some (b,(c,u))) := rfl
      exact hh.reachable.trans
        ((((hG.preconnected u v).map (pairedCopies_inclusion G ∅ c)).map
          (pairedCopies_inclusion (pairedCopies G ∅) ∅ b)).map inc)
  exact ⟨fun x y ↦ (hr x).symm.trans (hr y)⟩

lemma fourHub_card [Fintype V] :
    Fintype.card (Option (Four V))=4*Fintype.card V+1 := by
  simp only [Four,Fintype.card_option,Fintype.card_prod,Fintype.card_bool]
  omega

lemma fourHub_odd [Fintype V] : Odd (Fintype.card (Option (Four V))) := by
  rw [fourHub_card]
  exact ⟨2*Fintype.card V,by omega⟩

/-- A path partition of the four-copy hub graph yields a partition in at
least one copy. The central four edges can create at most two extra pieces. -/
lemma fourHub_project [Fintype V] {D : Finset (fourHub G u).Subgraph}
    (hD : GoodDecomposition (fourHub G u) D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ 4*E.card ≤ D.card+2 := by
  obtain ⟨T,hT,_⟩ := EdgeDefect.decomposition_path_family D hD
  obtain ⟨F,hF,hFc⟩ := project_hub_partition (fourHub G u) (false,(false,u)) T hT
  change GoodDecomposition (pairedCopies (pairedCopies G ∅) ∅) F at hF
  rw [fourHub_degree] at hFc
  obtain ⟨E,hE,hEc⟩ := decompose_one_of_two_copies hF
  obtain ⟨B,hB,hBc⟩ := decompose_one_of_two_copies hE
  exact ⟨B,hB,by omega⟩

end FourCopies

universe uStarCopy

/-- It suffices to establish the original bound on connected graphs of odd
order. Four disjoint copies joined through a new degree-four hub amplify
any failure, and the projection estimate rules out a rounding loss. -/
lemma gallai_of_odd_order
    (hodd : ∀ {W : Type uStarCopy} [Fintype W] (J : SimpleGraph W),
      Odd (Fintype.card W) → J.Connected →
      ∃ D : Finset J.Subgraph, GoodDecomposition J D ∧
        D.card ≤ ⌈(Fintype.card W : ℚ)/2⌉₊)
    {V : Type uStarCopy} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  let u : V := Classical.choice hG.nonempty
  obtain ⟨D,hD,hDc⟩ := hodd (fourHub G u) (fourHub_odd (V := V)) (fourHub_connected G u hG)
  obtain ⟨E,hE,hEc⟩ := fourHub_project G u hD
  rw [BridgeGlue.ceil_half,fourHub_card] at hDc
  rw [BridgeGlue.ceil_half]
  exact ⟨E,hE,by omega⟩

/-- Odd-order rounding absorbs a single extra path in the doubled bridge. -/
lemma odd_double_bridge_one_slack {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u : V) (ho : Odd (Fintype.card V))
    {D : Finset (pairedCopies G {u}).Subgraph}
    (hD : GoodDecomposition (pairedCopies G {u}) D) (hcard : D.card ≤ Fintype.card V+1) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  have he : s((false,u),(true,u)) ∈ (pairedCopies G {u}).edgeSet := Or.inr ⟨by simp,rfl,rfl⟩
  have hdel := delete_edge_decomposition hD ⟨_,he⟩
  rw [pairedCopies_delete_bridge] at hdel
  obtain ⟨E,hE,hEc⟩ := hdel
  obtain ⟨F,hF,hFc⟩ := decompose_one_of_two_copies hE
  refine ⟨F,hF,?_⟩
  rw [BridgeGlue.ceil_half]
  obtain ⟨q,hq⟩ := ho
  omega

/-- In the connected triangle-free matching-deletion reduction, one extra
path is harmless. Amplification removes the parity-dependent loss. This is
conditional: the asserted matching-deletion bound is not proved here. -/
lemma gallai_of_matching_deletion_one_slack
    (hcase : ∀ {W : Type uStarCopy} [Fintype W] (H F : SimpleGraph W),
      (∀ w, Odd (Nat.card (H.neighborSet w))) → F ≤ H →
      (∀ w, (F.neighborSet w).Subsingleton) → TriangleFreeMatching.TriangleFreeEdges H F →
      (H \ F).Connected →
      ∃ D : Finset (H \ F).Subgraph, GoodDecomposition (H \ F) D ∧
        2*D.card ≤ Fintype.card W+2)
    {V : Type uStarCopy} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  apply gallai_of_odd_order _ G hG
  intro W _ J ho hJ
  by_cases heven : ∃ v, Even (Nat.card (J.neighborSet v))
  · obtain ⟨v,hv⟩ := heven
    let S : Set W := {v | Even (Nat.card (J.neighborSet v))}
    let H := pairedCopies J S
    let K := pairedCopies J {v}
    have hKH : K ≤ H := pairedCopies_mono J (by simpa [S] using hv)
    have heq : H \ (H \ K)=K := sdiff_sdiff_eq_self hKH
    have hc := hcase H (H \ K) (pairedCopies_even_odd J) sdiff_le
      (pairedCopies_sdiff_matching J S {v})
      (TriangleFreeMatching.pairedCopies_difference_triangleFree J S {v})
    rw [heq] at hc
    obtain ⟨D,hD,hDc⟩ := hc (pairedCopies_connected J hJ {v} ⟨v,rfl⟩)
    apply odd_double_bridge_one_slack J v ho hD
    simp only [Fintype.card_prod,Fintype.card_bool] at hDc
    omega
  · have hj (v : W) : Odd (Nat.card (J.neighborSet v)) :=
      Nat.not_even_iff_odd.mp (fun hv ↦ heven ⟨v,hv⟩)
    have hc := hcase J ⊥ hj bot_le (by intro v a ha; exact ha.elim)
      (by intro a b hab; exact hab.elim)
    have heq : J \ ⊥=J := by ext a b; simp
    rw [heq] at hc
    obtain ⟨D,hD,hDc⟩ := hc hJ
    refine ⟨D,hD,?_⟩
    rw [BridgeGlue.ceil_half]
    obtain ⟨q,hq⟩ := ho
    omega

/-- The full conjecture follows from terminal weight at least |F|-1, rather
than the previously required |F|. No such selection theorem is asserted. -/
lemma gallai_of_terminal_weight_one_slack
    (hselect : ∀ {W : Type uStarCopy} [Fintype W] (H F : SimpleGraph W),
      (∀ w, Odd (Nat.card (H.neighborSet w))) → F ≤ H →
      (∀ w, (F.neighborSet w).Subsingleton) → TriangleFreeMatching.TriangleFreeEdges H F →
      (H \ F).Connected →
      ∃ D : Finset H.Subgraph, GoodDecomposition H D ∧
        (∀ K ∈ D, K.edgeSet.Nonempty) ∧ 2*D.card=Fintype.card W ∧
        F.edgeSet.ncard ≤ MatchingTrim.terminalWeight D F+1)
    {V : Type uStarCopy} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  apply gallai_of_matching_deletion_one_slack _ G hG
  intro W _ H F ho hFH hm ht hconn
  obtain ⟨D,hD,hne,hDc,hw⟩ := hselect H F ho hFH hm ht hconn
  obtain ⟨E,hE,hEc⟩ := MatchingTrim.trim_decomposition F hFH hm hD hne
  exact ⟨E,hE,by omega⟩

end StarCopyAmplification

end Erdos583Work
