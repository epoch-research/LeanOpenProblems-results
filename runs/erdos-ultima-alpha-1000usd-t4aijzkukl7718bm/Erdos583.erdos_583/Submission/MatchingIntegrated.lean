import Submission.CycleIntegrated

/-! Integrated two-sided matching-cut gluing and marked-center reductions. -/
namespace Erdos583Work
/- Two-sided contraction and path gluing along an odd matching cut. -/
namespace MatchingCutGlue
open SimpleGraph _root_.Erdos583Work
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.BridgeGlue
open _root_.Erdos583Work.StarPathPieces _root_.Erdos583Work.StarContraction
open _root_.Erdos583Work.StarExternalPaths _root_.Erdos583Work.BoundaryPorts
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {S : Set V}

noncomputable def flip (b : Boundary G S) : Boundary G Sᶜ :=
  ⟨(b.val.2,⟨b.val.1.val,by simpa only [compl_compl] using b.val.1.property⟩),b.property.symm⟩

lemma flip_injective : Function.Injective (flip (G := G) (S := S)) := by
  intro b c h
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (congrArg (outer G Sᶜ) h))
    (Subtype.ext (congrArg (inner G Sᶜ) h))

lemma flip_surjective : Function.Surjective (flip (G := G) (S := S)) := by
  rintro ⟨⟨⟨x,hx⟩,⟨y,hy⟩⟩,h⟩
  exact ⟨⟨(⟨y,by simpa only [compl_compl] using hy⟩,⟨x,hx⟩),h.symm⟩,rfl⟩

lemma boundary_degree [Fintype V] {r : V} (hr : r ∈ S)
    (ho : Function.Injective (outer G S)) :
    Nat.card ((contract G S r hr).neighborSet r)=Fintype.card (Boundary G S) := by
  let f : Boundary G S → (contract G S r hr).neighborSet r := fun b ↦
    ⟨outer G S b,(adj_center G S r hr).mpr
      ⟨outer_not_mem G S b,inner G S b,inner_mem G S b,adj G S b⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro b c h
      exact ho (congrArg (fun z : (contract G S r hr).neighborSet r ↦ z.val) h)
    · rintro ⟨v,hv⟩
      obtain ⟨hv,x,hx,hxv⟩ := (adj_center G S r hr).mp hv
      exact ⟨⟨(⟨x,hx⟩,⟨v,hv⟩),hxv⟩,rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm,Nat.card_eq_fintype_card]

lemma degree_add_twice_avoid_le [Fintype V] {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) (x : V) :
    Nat.card (G.neighborSet x)+2*Fintype.card (AvoidIndex T x) ≤ 2*k := by
  let P : Fin k → Prop := fun i ↦ x ∈ (T.walk i).support
  let f : ArmIndex T hp x → {i : Fin k // P i} × Bool :=
    fun e ↦ (⟨e.val.1,arm_owner_touches T hp x e⟩,e.val.2)
  have hf : Function.Injective f := by
    intro e d h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : {i : Fin k // P i} × Bool ↦ z.1.val) h)
      (congrArg (fun z : {i : Fin k // P i} × Bool ↦ z.2) h)
  have hb := Fintype.card_le_of_injective f hf
  have he := Nat.card_congr (Equiv.ofBijective _ (tip_bijective_neighbor T hp x))
  have hs : Fintype.card {i : Fin k // P i}+Fintype.card {i : Fin k // ¬P i}=k := by
    rw [Fintype.card_subtype_compl P,Nat.add_sub_of_le (Fintype.card_subtype_le P),Fintype.card_fin]
  change Nat.card (ArmIndex T hp x)=Nat.card (G.neighborSet x) at he
  rw [Nat.card_eq_fintype_card (α := ArmIndex T hp x)] at he
  simp only [Fintype.card_prod,Fintype.card_bool] at hb
  change Nat.card (G.neighborSet x)+2*Fintype.card {i : Fin k // ¬P i} ≤ 2*k
  omega

lemma degree_quota_twice_avoid [Fintype V] {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) (x : V) :
    Nat.card (G.neighborSet x)+T.quota x+2*Fintype.card (AvoidIndex T x)=2*k := by
  have he : Nat.card (G.neighborSet x)+T.quota x=
      2*(Finset.univ.filter fun i ↦ x ∈ (T.walk i).support).card := by
    rw [QuotaParity.degree_sum T x,QuotaSurgery.quota_eq_sum_endpoints T x,←Finset.sum_add_distrib]
    simp_rw [RootCapacity.path_incidence _ (hp _) x]
    rw [←Finset.mul_sum,←Finset.card_filter]
  have hs := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i : Fin k ↦ x ∈ (T.walk i).support)
  rw [Finset.card_univ,Fintype.card_fin] at hs
  rw [he]
  change 2*(Finset.univ.filter fun i ↦ x ∈ (T.walk i).support).card+
    2*Fintype.card {i : Fin k // x ∉ (T.walk i).support}=2*k
  rw [Fintype.card_subtype]
  omega

lemma indexed_decomposition {I : Type*} [Fintype I] (f : I → G.Subgraph)
    (hp : ∀ i, IsPathSubgraph (f i))
    (hd : Pairwise (fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet))
    (hc : (⋃ i, (f i).edgeSet)=G.edgeSet) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ Fintype.card I := by
  let D := Finset.univ.image f
  refine ⟨D,⟨?_,?_,?_⟩,by simpa only [Finset.card_univ] using Finset.card_image_le (s := Finset.univ) (f := f)⟩
  · intro K hK
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    exact hp i
  · intro K hK L hL hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    exact hd (fun he ↦ hne (congrArg f he))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨K,_,he⟩
      exact K.edgeSet_subset he
    · intro he
      rw [←hc] at he
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
      exact ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩

section Gluing
variable {r t : V} (hr : r ∈ S) (ht : t ∈ Sᶜ)
  {k l : ℕ} (T : TrailFamily (contract G S r hr) k)
  (U : TrailFamily (contract G Sᶜ t ht) l)
  (hT : ∀ i, (T.walk i).IsPath) (hU : ∀ i, (U.walk i).IsPath)

noncomputable def insideArm (b : Boundary G S) : Arm G (inner G S b) :=
  exterior ht U hU (flip b)

lemma insideArm_mem : ∀ b, ∀ x ∈ (insideArm ht U hU b).walk.support, x ∈ S := by
  intro b x hx
  exact not_not.mp (exterior_outside ht U hU (flip b) x hx)

lemma insideArm_disjoint : Pairwise (fun b c : Boundary G S ↦
    Disjoint (insideArm ht U hU b).walk.toSubgraph.edgeSet
      (insideArm ht U hU c).walk.toSubgraph.edgeSet) := by
  intro b c hbc
  exact exterior_disjoint ht U hU (fun he ↦ hbc (flip_injective he))

noncomputable def joined (b : Boundary G S) : G.Subgraph :=
  (PortSplicing.splice (inner G S) (insideArm ht U hU) (Function.Embedding.refl _) (fun _ ↦ rfl)
    (exterior hr T hT) b).toSubgraph

lemma joined_edges (b : Boundary G S) :
    (joined hr ht T U hT hU b).edgeSet=(insideArm ht U hU b).walk.toSubgraph.edgeSet ∪
      ({edge G S b} ∪ (exterior hr T hT b).walk.toSubgraph.edgeSet) :=
  PortSplicing.splice_edges _ _ _ _ _ b

lemma joined_isPath (b : Boundary G S) : IsPathSubgraph (joined hr ht T U hT hU b) :=
  ⟨_,_,_,PortSplicing.splice_isPath _ _ _ _ _ (insideArm_mem ht U hU)
    (exterior_outside hr T hT) b,rfl⟩

lemma joined_disjoint : Pairwise (fun b c ↦
    Disjoint (joined hr ht T U hT hU b).edgeSet (joined hr ht T U hT hU c).edgeSet) :=
  PortSplicing.splice_disjoint _ _ _ _ _ (insideArm_mem ht U hU)
    (exterior_outside hr T hT) (insideArm_disjoint ht U hU) (exterior_disjoint hr T hT)

lemma inside_avoiding_joined (a : AvoidIndex U t) (b : Boundary G S) :
    Disjoint (avoiding ht U a).edgeSet (joined hr ht T U hT hU b).edgeSet := by
  rw [joined_edges,Set.disjoint_union_right,Set.disjoint_union_right]
  have ha : (avoiding ht U a).edgeSet ⊆ (within G S).edgeSet := by
    simpa only [compl_compl] using avoiding_subset ht U a
  refine ⟨avoiding_exterior_disjoint ht U hU a (flip b),?_,?_⟩
  · exact Set.disjoint_singleton_right.mpr (fun he ↦ edge_not_inside G S b (ha he))
  · exact (inside_disjoint_outside G S).mono ha
      (PortSplicing.path_edges_inside (exterior hr T hT b) (exterior_outside hr T hT b))

lemma outside_avoiding_joined (a : AvoidIndex T r) (b : Boundary G S) :
    Disjoint (avoiding hr T a).edgeSet (joined hr ht T U hT hU b).edgeSet :=
  PortSplicing.avoid_splice_disjoint _ _ _ _ _ _ (insideArm_mem ht U hU)
    (avoiding_subset hr T) (avoiding_exterior_disjoint hr T hT) a b

include hT hU in
lemma glue [Fintype V] : ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
    D.card ≤ Fintype.card (Boundary G S)+Fintype.card (AvoidIndex T r)+Fintype.card (AvoidIndex U t) := by
  let f : Boundary G S ⊕ (AvoidIndex T r ⊕ AvoidIndex U t) → G.Subgraph :=
    Sum.elim (joined hr ht T U hT hU) (Sum.elim (avoiding hr T) (avoiding ht U))
  have hp : ∀ i, IsPathSubgraph (f i) := by
    rintro (b|a|c)
    · exact joined_isPath hr ht T U hT hU b
    · exact avoiding_isPath hr T hT a
    · exact avoiding_isPath ht U hU c
  have hcross (a : AvoidIndex T r) (c : AvoidIndex U t) :
      Disjoint (avoiding hr T a).edgeSet (avoiding ht U c).edgeSet := by
    apply (inside_disjoint_outside G S).symm.mono (avoiding_subset hr T a)
    simpa only [compl_compl] using avoiding_subset ht U c
  have hd : Pairwise (fun i j ↦ Disjoint (f i).edgeSet (f j).edgeSet) := by
    rintro (b|a|c) (d|e|g) hne
    · exact joined_disjoint hr ht T U hT hU (fun he ↦ hne (congrArg Sum.inl he))
    · exact (outside_avoiding_joined hr ht T U hT hU e b).symm
    · exact (inside_avoiding_joined hr ht T U hT hU g b).symm
    · exact outside_avoiding_joined hr ht T U hT hU a d
    · exact avoiding_disjoint hr T (fun he ↦ hne (congrArg (Sum.inr ∘ Sum.inl) he))
    · exact hcross a g
    · exact inside_avoiding_joined hr ht T U hT hU c d
    · exact (hcross e c).symm
    · exact avoiding_disjoint ht U (fun he ↦ hne (congrArg (Sum.inr ∘ Sum.inr) he))
  have hc : (⋃ i, (f i).edgeSet)=G.edgeSet := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i ↦ (f i).edgeSet_subset
    · intro e he
      rw [←cover G S] at he
      rcases he with he|⟨b,rfl⟩|he
      · have he' : e ∈ (within G Sᶜᶜ).edgeSet := by simpa only [compl_compl] using he
        rw [←exterior_cover ht U hU] at he'
        rcases he' with he'|he'
        · obtain ⟨a,ha⟩ := Set.mem_iUnion.mp he'
          exact Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inr a),ha⟩
        · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he'
          obtain ⟨c,rfl⟩ := flip_surjective b
          refine Set.mem_iUnion.mpr ⟨Sum.inl c,?_⟩
          change e ∈ (joined hr ht T U hT hU c).edgeSet
          rw [joined_edges]
          exact Or.inl hb
      · refine Set.mem_iUnion.mpr ⟨Sum.inl b,?_⟩
        change edge G S b ∈ (joined hr ht T U hT hU b).edgeSet
        rw [joined_edges]
        exact Or.inr (Or.inl rfl)
      · rw [←exterior_cover hr T hT] at he
        rcases he with he|he
        · obtain ⟨a,ha⟩ := Set.mem_iUnion.mp he
          exact Set.mem_iUnion.mpr ⟨Sum.inr (Sum.inl a),ha⟩
        · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
          refine Set.mem_iUnion.mpr ⟨Sum.inl b,?_⟩
          change e ∈ (joined hr ht T U hT hU b).edgeSet
          rw [joined_edges]
          exact Or.inr (Or.inr hb)
  obtain ⟨D,hD,hDc⟩ := indexed_decomposition f hp hd hc
  exact ⟨D,hD,by simpa only [Fintype.card_sum,Nat.add_assoc] using hDc⟩

include hr ht T U hT hU in
lemma matching_glue_quota [Fintype V] (hi : Function.Injective (inner G S))
    (ho : Function.Injective (outer G S)) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+T.quota r+U.quota t ≤ 2*(k+l) := by
  have hi' : Function.Injective (outer G Sᶜ) := by
    intro b c he
    obtain ⟨b,rfl⟩ := flip_surjective b
    obtain ⟨c,rfl⟩ := flip_surjective c
    exact congrArg flip (hi he)
  have he : Fintype.card (Boundary G Sᶜ)=Fintype.card (Boundary G S) :=
    (Fintype.card_congr (Equiv.ofBijective _ ⟨flip_injective,flip_surjective⟩)).symm
  have hbT := degree_quota_twice_avoid T hT r
  have hbU := degree_quota_twice_avoid U hU t
  rw [boundary_degree hr ho] at hbT
  rw [boundary_degree ht hi'] at hbU
  simp only [←Nat.card_eq_fintype_card] at hbT hbU he
  rw [he] at hbU
  obtain ⟨D,hD,hDc⟩ := glue hr ht T U hT hU
  simp only [←Nat.card_eq_fintype_card] at hDc
  exact ⟨D,hD,by omega⟩

include hr ht T U hT hU in
lemma matching_glue_saving [Fintype V] (hi : Function.Injective (inner G S))
    (ho : Function.Injective (outer G S)) (s : ℕ) (hs : 2*s ≤ T.quota r+U.quota t) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card+s ≤ k+l := by
  obtain ⟨D,hD,hDc⟩ := matching_glue_quota hr ht T U hT hU hi ho
  exact ⟨D,hD,by omega⟩

include hr ht T U hT hU in
lemma odd_matching_glue [Fintype V] (hi : Function.Injective (inner G S))
    (ho : Function.Injective (outer G S)) (hodd : Odd (Fintype.card (Boundary G S))) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card+1 ≤ k+l := by
  have hi' : Function.Injective (outer G Sᶜ) := by
    intro b c he
    obtain ⟨b,rfl⟩ := flip_surjective b
    obtain ⟨c,rfl⟩ := flip_surjective c
    exact congrArg flip (hi he)
  have he : Fintype.card (Boundary G Sᶜ)=Fintype.card (Boundary G S) :=
    (Fintype.card_congr (Equiv.ofBijective _ ⟨flip_injective,flip_surjective⟩)).symm
  have hbT := degree_add_twice_avoid_le T hT r
  have hbU := degree_add_twice_avoid_le U hU t
  rw [boundary_degree hr ho] at hbT
  rw [boundary_degree ht hi'] at hbU
  simp only [←Nat.card_eq_fintype_card] at hbT hbU he hodd
  rw [he] at hbU
  obtain ⟨D,hD,hDc⟩ := glue hr ht T U hT hU
  simp only [←Nat.card_eq_fintype_card] at hDc
  obtain ⟨m,hm⟩ := hodd
  exact ⟨D,hD,by omega⟩

end Gluing
lemma contraction_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    [Fintype V] (hn : Fintype.card V=n) (hG : G.Connected) {r : V} (hr : r ∈ S)
    (hs : 2 ≤ S.ncard) :
    ∃ k, ∃ T : TrailFamily (contract G S r hr) k,
      (∀ i, (T.walk i).IsPath) ∧ k ≤ ⌈((Sᶜ.ncard+1 : ℕ) : ℚ)/2⌉₊ := by
  let K := contract G S r hr
  let R := Sᶜ ∪ {r}
  have hc : R.ncard+S.ncard=Fintype.card V+1 := card_vertices S r hr
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hsum
  have hR : R.ncard=Sᶜ.ncard+1 := by omega
  obtain ⟨D,hD,hDc⟩ := hsmall.on_induce K R (by omega) (connected_induce G S r hr hG)
  obtain ⟨E,hE,hEc⟩ := lift_induce_within R D hD
  have hKR : within K R=K := within_eq G S r hr
  have hex : ∃ E : Finset K.Subgraph, GoodDecomposition K E ∧ E.card ≤ D.card := by
    exact Eq.mp (congrArg (fun J : SimpleGraph V ↦
      ∃ F : Finset J.Subgraph, GoodDecomposition J F ∧ F.card ≤ D.card) hKR) ⟨E,hE,hEc⟩
  obtain ⟨E,hE,hEc⟩ := hex
  obtain ⟨T,hT,_⟩ := EdgeDefect.decomposition_path_family E hE
  refine ⟨E.card,T,hT,?_⟩
  rw [hR] at hDc
  exact hEc.trans hDc

lemma odd_matching_cut_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    [Fintype V] (hn : Fintype.card V=n) (hG : G.Connected)
    (hs : 2 ≤ S.ncard) (ht : 2 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S))
    (hodd : Odd (Fintype.card (Boundary G S))) (hpar : Odd S.ncard ∨ Odd Sᶜ.ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨r,hr⟩ := (Set.ncard_pos (Set.toFinite S)).mp (by omega : 0 < S.ncard)
  obtain ⟨t,htS⟩ := (Set.ncard_pos (Set.toFinite Sᶜ)).mp (by omega : 0 < Sᶜ.ncard)
  obtain ⟨k,T,hT,hk⟩ := contraction_partition hsmall hn hG hr hs
  obtain ⟨l,U,hU,hl⟩ := contraction_partition hsmall hn hG htS ht
  obtain ⟨D,hD,hDc⟩ := odd_matching_glue hr htS T U hT hU hi ho hodd
  have hb := augmented_budget S.ncard Sᶜ.ncard hpar
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hsum
  simp only [compl_compl] at hl
  rw [hsum] at hb
  exact ⟨D,hD,by omega⟩

lemma failure_odd_matching_cut_even_sides {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    [Fintype V] (hn : Fintype.card V=n) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (hs : 2 ≤ S.ncard) (ht : 2 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S))
    (hodd : Odd (Fintype.card (Boundary G S))) : Even S.ncard ∧ Even Sᶜ.ncard := by
  have hp : ¬(Odd S.ncard ∨ Odd Sᶜ.ncard) := fun hpar ↦
    hfail (odd_matching_cut_reduction hsmall hn hG hs ht hi ho hodd hpar)
  exact ⟨Nat.not_odd_iff_even.mp (fun h ↦ hp (Or.inl h)),
    Nat.not_odd_iff_even.mp (fun h ↦ hp (Or.inr h))⟩

lemma odd_failure_no_odd_matching_cut {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    [Fintype V] (hn : Fintype.card V=n) (hG : G.Connected) (hnodd : Odd n)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (hs : 2 ≤ S.ncard) (ht : 2 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S)) :
    Even (Fintype.card (Boundary G S)) := by
  apply Nat.not_odd_iff_even.mp
  intro hodd
  obtain ⟨heS,heT⟩ := failure_odd_matching_cut_even_sides hsmall hn hG hfail hs ht hi ho hodd
  have he := heS.add heT
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card,hn] at hsum
  rw [hsum] at he
  exact (Nat.not_even_iff_odd.mpr hnodd) he

end MatchingCutGlue

/- Marked contraction centers save two paths across an even matching cut. -/
namespace MatchingCutMarked
open SimpleGraph _root_.Erdos583Work _root_.Erdos583Work.MatchingCutGlue
open _root_.Erdos583Work.QuotaTrails _root_.Erdos583Work.BridgeGlue
open _root_.Erdos583Work.StarPathPieces _root_.Erdos583Work.StarContraction
open _root_.Erdos583Work.BoundaryPorts
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V}

lemma lift_marked_contraction {r : V} (hr : r ∈ S) {b : ℕ}
    (hmark : ∃ D : Finset ((contract G S r hr).induce (Sᶜ ∪ {r})).Subgraph,
      GoodDecomposition _ D ∧ D.card ≤ b ∧
        MarkedDouble.MarkedAt D ⟨r,Or.inr rfl⟩) :
    ∃ k, ∃ T : TrailFamily (contract G S r hr) k,
      (∀ i, (T.walk i).IsPath) ∧ k ≤ b ∧ 0 < T.quota r := by
  let K := contract G S r hr
  let R := Sᶜ ∪ {r}
  obtain ⟨D,hD,hDc,a,p,hp,hpD⟩ := hmark
  obtain ⟨E,q,hE,hq,hqm,hEc⟩ := MarkedBudgets.lift_induce_marked R hD p hp hpD
  have hKR : within K R=K := within_eq G S r hr
  have hex : ∃ E : Finset K.Subgraph, ∃ q : K.Walk r a.val,
      GoodDecomposition K E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card := by
    exact Eq.mp (congrArg (fun J : SimpleGraph V ↦
      ∃ F : Finset J.Subgraph, ∃ q : J.Walk r a.val,
        GoodDecomposition J F ∧ q.IsPath ∧ q.toSubgraph ∈ F ∧ F.card ≤ D.card) hKR)
      ⟨E,q,hE,hq,hqm,hEc⟩
  obtain ⟨E,q,hE,hq,hqm,hEc⟩ := hex
  obtain ⟨T,hT,hparts⟩ := EdgeDefect.decomposition_path_family E hE
  obtain ⟨i,hi⟩ := hparts q.toSubgraph hqm
  have hend := MarkedBudgets.endpoint_of_path_rep q hq (T.walk i) (T.isTrail i) hi
  exact ⟨E.card,T,hT,hEc.trans hDc,DeletionEndpoint.quota_pos_of_endpoint T i hend⟩

lemma marked_contraction_partition {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected) {r : V} (hr : r ∈ S)
    (hs : 3 ≤ S.ncard) :
    ∃ k, ∃ T : TrailFamily (contract G S r hr) k,
      (∀ i, (T.walk i).IsPath) ∧ k ≤ ⌈((Sᶜ.ncard+2 : ℕ) : ℚ)/2⌉₊ ∧ 0 < T.quota r := by
  let K := contract G S r hr
  let R := Sᶜ ∪ {r}
  have hc : R.ncard+S.ncard=Fintype.card V+1 := card_vertices S r hr
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hsum
  have hR : R.ncard=Sᶜ.ncard+1 := by omega
  have hcard : Fintype.card R=R.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  obtain ⟨D,a,p,hD,hp,hpD,hDc⟩ := CutVertexReduction.smaller_order_marked hsmall
    (K.induce R) (connected_induce G S r hr hG) ⟨r,Or.inr rfl⟩ (by omega)
  apply lift_marked_contraction hr
  refine ⟨D,hD,?_,a,p,hp,hpD⟩
  simpa only [hcard,hR,Nat.add_assoc] using hDc

lemma marked_even_matching_glue {r t : V} (hr : r ∈ S) (ht : t ∈ Sᶜ)
    {k l : ℕ} (T : TrailFamily (contract G S r hr) k)
    (U : TrailFamily (contract G Sᶜ t ht) l)
    (hT : ∀ i, (T.walk i).IsPath) (hU : ∀ i, (U.walk i).IsPath)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S))
    (heven : Even (Fintype.card (Boundary G S))) (hmT : 0 < T.quota r) (hmU : 0 < U.quota t) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card+2 ≤ k+l := by
  have hi' : Function.Injective (outer G Sᶜ) := by
    intro b c he
    obtain ⟨b,rfl⟩ := flip_surjective b
    obtain ⟨c,rfl⟩ := flip_surjective c
    exact congrArg _root_.Erdos583Work.MatchingCutGlue.flip (hi he)
  have he : Fintype.card (Boundary G Sᶜ)=Fintype.card (Boundary G S) :=
    (Fintype.card_congr (Equiv.ofBijective _ ⟨flip_injective,flip_surjective⟩)).symm
  have hqT : Even (T.quota r) := (QuotaParity.quota_even_iff T r).mpr (by
    rw [boundary_degree hr ho]
    simpa only [←Nat.card_eq_fintype_card] using heven)
  have hqU : Even (U.quota t) := (QuotaParity.quota_even_iff U t).mpr (by
    rw [boundary_degree ht hi']
    simp only [←Nat.card_eq_fintype_card] at he heven ⊢
    rwa [he])
  apply matching_glue_saving hr ht T U hT hU hi ho 2
  obtain ⟨a,ha⟩ := hqT
  obtain ⟨b,hb⟩ := hqU
  omega

lemma twice_marked_budget (a b : ℕ) (hpar : Even a ∨ Even b) :
    ⌈((a+2 : ℕ) : ℚ)/2⌉₊+⌈((b+2 : ℕ) : ℚ)/2⌉₊ ≤ ⌈((a+b : ℕ) : ℚ)/2⌉₊+2 := by
  simp only [ceil_half]
  rcases hpar with ⟨k,hk⟩|⟨k,hk⟩ <;> omega

lemma even_matching_cut_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected)
    (hs : 3 ≤ S.ncard) (ht : 3 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S))
    (heven : Even (Fintype.card (Boundary G S))) (hpar : Even S.ncard ∨ Even Sᶜ.ncard) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨r,hr⟩ := (Set.ncard_pos (Set.toFinite S)).mp (by omega : 0 < S.ncard)
  obtain ⟨t,htS⟩ := (Set.ncard_pos (Set.toFinite Sᶜ)).mp (by omega : 0 < Sᶜ.ncard)
  obtain ⟨k,T,hT,hk,hmT⟩ := marked_contraction_partition hsmall hn hG hr hs
  obtain ⟨l,U,hU,hl,hmU⟩ := marked_contraction_partition hsmall hn hG htS ht
  obtain ⟨D,hD,hDc⟩ := marked_even_matching_glue hr htS T U hT hU hi ho heven hmT hmU
  have hb := twice_marked_budget S.ncard Sᶜ.ncard hpar
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card] at hsum
  simp only [compl_compl] at hl
  rw [hsum] at hb
  exact ⟨D,hD,by omega⟩

lemma failure_even_matching_cut_odd_sides {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (hs : 3 ≤ S.ncard) (ht : 3 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S))
    (heven : Even (Fintype.card (Boundary G S))) : Odd S.ncard ∧ Odd Sᶜ.ncard := by
  have hp : ¬(Even S.ncard ∨ Even Sᶜ.ncard) := fun hpar ↦
    hfail (even_matching_cut_reduction hsmall hn hG hs ht hi ho heven hpar)
  exact ⟨Nat.not_even_iff_odd.mp (fun h ↦ hp (Or.inl h)),
    Nat.not_even_iff_odd.mp (fun h ↦ hp (Or.inr h))⟩

lemma odd_failure_no_matching_cut {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected) (hnodd : Odd n)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (hs : 3 ≤ S.ncard) (ht : 3 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S)) : False := by
  have he := odd_failure_no_odd_matching_cut hsmall hn hG hnodd hfail (by omega) (by omega) hi ho
  obtain ⟨hoS,hoT⟩ := failure_even_matching_cut_odd_sides hsmall hn hG hfail hs ht hi ho he
  have hp := hoS.add_odd hoT
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card,hn] at hsum
  rw [hsum] at hp
  exact (Nat.not_even_iff_odd.mpr hnodd) hp

lemma degree_le_matching_side (hi : Function.Injective (inner G S)) {x : V} (hx : x ∈ S) :
    Nat.card (G.neighborSet x) ≤ S.ncard := by
  let f : G.neighborSet x → S := fun y ↦ if hy : y.val ∈ S then ⟨y.val,hy⟩ else ⟨x,hx⟩
  have hf : Function.Injective f := by
    intro y z he
    have he' := congrArg (fun v : S ↦ v.val) he
    by_cases hy : y.val ∈ S <;> by_cases hz : z.val ∈ S
    · exact Subtype.ext (by simpa only [f,dif_pos hy,dif_pos hz] using he')
    · have heq : y.val=x := by simpa only [f,dif_pos hy,dif_neg hz] using he'
      exact (y.property.ne heq.symm).elim
    · have heq : z.val=x := by simpa only [f,dif_neg hy,dif_pos hz] using he'.symm
      exact (z.property.ne heq.symm).elim
    · let b : Boundary G S := ⟨(⟨x,hx⟩,⟨y.val,hy⟩),y.property⟩
      let c : Boundary G S := ⟨(⟨x,hx⟩,⟨z.val,hz⟩),z.property⟩
      exact Subtype.ext (congrArg (outer G S) (hi (show inner G S b=inner G S c from rfl)))
  have hh := Fintype.card_le_of_injective f hf
  simpa only [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hh

lemma odd_failure_no_proper_matching_cut {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) (hnodd : Odd n)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) (hs : S.Nonempty) (ht : Sᶜ.Nonempty)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S)) : False := by
  obtain ⟨x,hx⟩ := hs
  obtain ⟨y,hy⟩ := ht
  have hxdeg := DegreeFourReduction.min_degree_five_of_odd_failure hsmall hnodd hG hfail x
  have hydeg := DegreeFourReduction.min_degree_five_of_odd_failure hsmall hnodd hG hfail y
  have hxbound := degree_le_matching_side hi hx
  have ho' : Function.Injective (inner G Sᶜ) := by
    intro b c he
    obtain ⟨b,rfl⟩ := flip_surjective b
    obtain ⟨c,rfl⟩ := flip_surjective c
    exact congrArg _root_.Erdos583Work.MatchingCutGlue.flip (ho he)
  have hybound := degree_le_matching_side ho' hy
  exact odd_failure_no_matching_cut hsmall (Fintype.card_fin n) hG hnodd hfail
    (by omega) (by omega) hi ho

lemma failure_matching_cut_parity {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    (hn : Fintype.card V=n) (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊)
    (hs : 3 ≤ S.ncard) (ht : 3 ≤ Sᶜ.ncard)
    (hi : Function.Injective (inner G S)) (ho : Function.Injective (outer G S)) :
    Even n ∧ (Even (Fintype.card (Boundary G S)) ↔ Odd S.ncard) ∧
      (Even S.ncard ↔ Even Sᶜ.ncard) := by
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_eq_fintype_card,hn] at hsum
  by_cases he : Even (Fintype.card (Boundary G S))
  · obtain ⟨ha,hb⟩ := failure_even_matching_cut_odd_sides hsmall hn hG hfail hs ht hi ho he
    have hnE := ha.add_odd hb
    rw [hsum] at hnE
    exact ⟨hnE,⟨fun _ ↦ ha,fun _ ↦ he⟩,
      ⟨fun h ↦ ((Nat.not_even_iff_odd.mpr ha) h).elim,
        fun h ↦ ((Nat.not_even_iff_odd.mpr hb) h).elim⟩⟩
  · obtain ⟨ha,hb⟩ := failure_odd_matching_cut_even_sides hsmall hn hG hfail
      (by omega) (by omega) hi ho (Nat.not_even_iff_odd.mp he)
    have hnE := ha.add hb
    rw [hsum] at hnE
    exact ⟨hnE,⟨fun h ↦ (he h).elim,fun h ↦ ((Nat.not_odd_iff_even.mpr ha) h).elim⟩,
      ⟨fun _ ↦ hb,fun _ ↦ ha⟩⟩

end MatchingCutMarked

end Erdos583Work
