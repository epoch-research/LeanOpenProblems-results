import Submission.TerminalCapacity

/-! Project both unpaired copies, retaining zero endpoint multiplicities. -/
namespace Erdos583TerminalCopyBoundsDevelopment
open SimpleGraph Erdos583Work Erdos583TerminalCapacityDevelopment
open scoped Classical
set_option maxHeartbeats 2400000

lemma neighbor_ncard_of_copy_edges {V : Type*} [Fintype V]
    {G : SimpleGraph V} {H : (pairedCopies G ∅).Subgraph} {K : G.Subgraph} {b : Bool}
    (he : H.edgeSet=Sym2.map (fun v ↦ (b,v)) '' K.edgeSet) (c : Bool) (v : V) :
    (H.neighborSet (c,v)).ncard=if c=b then (K.neighborSet v).ncard else 0 := by
  have ha (x y : Bool × V) : H.Adj x y ↔ x.1=b ∧ y.1=b ∧ K.Adj x.2 y.2 := by
    change s(x,y) ∈ H.edgeSet ↔ _
    rw [he]
    constructor
    · rintro ⟨e,heK,heq⟩
      induction e using Sym2.ind with
      | h u w =>
        rcases Sym2.eq_iff.mp heq with hh|hh
        · obtain ⟨rfl,rfl⟩ := hh
          exact ⟨rfl,rfl,heK⟩
        · obtain ⟨rfl,rfl⟩ := hh
          exact ⟨rfl,rfl,heK.symm⟩
    · rintro ⟨hx,hy,hxy⟩
      refine ⟨s(x.2,y.2),hxy,?_⟩
      have hx' : (b,x.2)=x := Prod.ext hx.symm rfl
      have hy' : (b,y.2)=y := Prod.ext hy.symm rfl
      simpa using congrArg₂ (fun a b ↦ s(a,b)) hx' hy'
  have hn : H.neighborSet (c,v)=if c=b then (fun w ↦ (b,w)) '' K.neighborSet v else ∅ := by
    ext x
    change H.Adj (c,v) x ↔ _
    rw [ha]
    by_cases hcb : c=b
    · subst c
      simp only [true_and]
      constructor
      · rintro ⟨hx,hK⟩
        exact ⟨x.2,hK,Prod.ext hx.symm rfl⟩
      · rintro ⟨w,hw,rfl⟩
        exact ⟨rfl,hw⟩
    · simp [hcb]
  rw [hn]
  split_ifs
  · exact Set.ncard_image_of_injective _ (fun x y h ↦ Prod.mk.inj h |>.2)
  · simp

/-- Both projected partitions fit in the original count. A vertex with no
endpoint in the unpaired graph remains unmarked in its projected copy. -/
lemma decompose_both_copies {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset (pairedCopies G ∅).Subgraph} (hD : GoodDecomposition (pairedCopies G ∅) D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) :
    ∃ E : Bool → Finset G.Subgraph,
      (∀ b, GoodDecomposition G (E b)) ∧
      (∀ b, ∀ K ∈ E b, K.edgeSet.Nonempty) ∧
      (E false).card+(E true).card ≤ D.card ∧
      ∀ b v, endpointMultiplicity D (b,v)=0 → endpointMultiplicity (E b) v=0 := by
  choose b f hp hl using (fun H : D ↦ project_unpaired_path (hD.1 H.val H.property))
  let I (c : Bool) : Finset D := Finset.univ.filter (fun H ↦ b H=c)
  let E (c : Bool) : Finset G.Subgraph := (I c).image f
  have hgood (c : Bool) : GoodDecomposition G (E c) := by
    refine ⟨?_,?_,?_⟩
    · intro K hK
      obtain ⟨H,_,rfl⟩ := Finset.mem_image.mp hK
      exact hp H
    · intro K hK L hL hne
      obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hK
      obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hL
      have hbH := (Finset.mem_filter.mp hH).2
      have hbJ := (Finset.mem_filter.mp hJ).2
      apply Set.disjoint_left.mpr
      intro e heH heJ
      have hneval : H.val ≠ J.val := fun heq ↦ hne (congrArg f (Subtype.ext heq))
      have hiH : Sym2.map (fun v ↦ (c,v)) e ∈ H.val.edgeSet := by
        rw [hl H,hbH]
        exact ⟨e,heH,rfl⟩
      have hiJ : Sym2.map (fun v ↦ (c,v)) e ∈ J.val.edgeSet := by
        rw [hl J,hbJ]
        exact ⟨e,heJ,rfl⟩
      exact Set.disjoint_left.mp (hD.2.1 H.property J.property hneval) hiH hiJ
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨K,_,he⟩
        exact K.edgeSet_subset he
      · intro he
        have hec : Sym2.map (fun v ↦ (c,v)) e ∈ (pairedCopies G ∅).edgeSet := by
          induction e using Sym2.ind with
          | h x y => exact Or.inl ⟨rfl,he⟩
        have heD : Sym2.map (fun v ↦ (c,v)) e ∈ ⋃ H ∈ D, H.edgeSet := hD.2.2.symm ▸ hec
        simp only [Set.mem_iUnion] at heD
        obtain ⟨H,hH,heH⟩ := heD
        rw [hl ⟨H,hH⟩] at heH
        obtain ⟨e',he',heq⟩ := heH
        obtain ⟨hb,rfl⟩ := copy_edge_injective heq
        exact ⟨f ⟨H,hH⟩,Finset.mem_image.mpr ⟨⟨H,hH⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩,he'⟩
  have hsum : (I false).card+(I true).card=D.card := by
    simpa [I,Bool.not_eq_false] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun H : D ↦ b H=false))
  refine ⟨E,hgood,?_,?_,?_⟩
  · intro c K hK
    obtain ⟨H,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨e,he⟩ := hne H.val H.property
    rw [hl] at he
    obtain ⟨e',he',_⟩ := he
    exact ⟨e',he'⟩
  · exact (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans_eq hsum
  · intro c v hv
    unfold endpointMultiplicity
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro K hK
    obtain ⟨hKE,hKv⟩ := Finset.mem_filter.mp hK
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hKE
    have hbc := (Finset.mem_filter.mp hH).2
    have hHv : (H.val.neighborSet (c,v)).ncard=1 := by
      rw [neighbor_ncard_of_copy_edges (hl H),if_pos hbc.symm]
      exact hKv
    have hm : H.val ∈ D.filter (fun K ↦ (K.neighborSet (c,v)).ncard=1) :=
      Finset.mem_filter.mpr ⟨H.property,hHv⟩
    have hzero : D.filter (fun K ↦ (K.neighborSet (c,v)).ncard=1)=∅ := Finset.card_eq_zero.mp hv
    rw [hzero] at hm
    exact Finset.notMem_empty _ hm

lemma terminalVertices_mono {V : Type*} [Fintype V] {H F M : SimpleGraph V}
    (hFM : F ≤ M) (K : H.Subgraph) :
    MatchingTrim.terminalVertices K F ⊆ MatchingTrim.terminalVertices K M := by
  intro v hv
  have ht := (Finset.mem_filter.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,ht.1,?_⟩
  have hlo : ((K.spanningCoe ⊓ F).neighborSet v).ncard ≤
      ((K.spanningCoe ⊓ M).neighborSet v).ncard := by
    apply Set.ncard_le_ncard _ (Set.toFinite _)
    intro w hw
    exact ⟨hw.1,hFM hw.2⟩
  have hhi : ((K.spanningCoe ⊓ M).neighborSet v).ncard ≤ (K.neighborSet v).ncard := by
    apply Set.ncard_le_ncard _ (Set.toFinite _)
    intro w hw
    exact hw.1
  omega

lemma terminalWeight_mono {V : Type*} [Fintype V] {H F M : SimpleGraph V}
    (hFM : F ≤ M) (D : Finset H.Subgraph) :
    MatchingTrim.terminalWeight D F ≤ MatchingTrim.terminalWeight D M := by
  apply Finset.sum_le_sum
  intro K _
  exact Finset.card_le_card (terminalVertices_mono hFM K)

end Erdos583TerminalCopyBoundsDevelopment
