import Submission.Work

/-! Exact endpoint control when splitting a path at an inactive vertex. -/

open SimpleGraph Erdos583Work Erdos583Work.PendantCompletion
namespace Erdos583ActivationDevelopment

set_option maxHeartbeats 1200000

open scoped Classical in
lemma split_member {V : Type*} {G : SimpleGraph V} {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) {K A B : G.Subgraph} (hK : K ∈ D)
    (hA : IsPathSubgraph A) (hB : IsPathSubgraph B)
    (hneA : A.edgeSet.Nonempty) (hneB : B.edgeSet.Nonempty)
    (hd : Disjoint A.edgeSet B.edgeSet) (hc : A.edgeSet ∪ B.edgeSet = K.edgeSet)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) :
    let E := insert A (insert B (D.erase K))
    GoodDecomposition G E ∧ E.card = D.card + 1 ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ ∀ x,
        endpointMultiplicity E x + (if (K.neighborSet x).ncard = 1 then 1 else 0) =
        endpointMultiplicity D x + (if (A.neighborSet x).ncard = 1 then 1 else 0) +
          (if (B.neighborSet x).ncard = 1 then 1 else 0) := by
  classical
  let R := D.erase K
  let E := insert A (insert B R)
  have hAB : A ≠ B := by
    rintro rfl
    obtain ⟨e,he⟩ := hneA
    exact Set.disjoint_left.mp hd he he
  have hsep (H : G.Subgraph) (hH : H ∈ R) : Disjoint K.edgeSet H.edgeSet :=
    hD.2.1 hK (Finset.mem_of_mem_erase hH) (Finset.mem_erase.mp hH).1.symm
  have hAout : A ∉ R := by
    intro hh
    obtain ⟨e,he⟩ := hneA
    exact Set.disjoint_left.mp (hsep A hh) (hc ▸ Or.inl he) he
  have hBout : B ∉ R := by
    intro hh
    obtain ⟨e,he⟩ := hneB
    exact Set.disjoint_left.mp (hsep B hh) (hc ▸ Or.inr he) he
  have hgood : GoodDecomposition G E := by
    refine ⟨?_,?_,?_⟩
    · intro H hH
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact hA
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact hB
      exact hD.1 H (Finset.mem_of_mem_erase hH)
    · change Set.PairwiseDisjoint (↑(insert A (insert B R)) : Set G.Subgraph) _
      rw [Finset.coe_insert,Set.pairwiseDisjoint_insert]
      refine ⟨?_,?_⟩
      · rw [Finset.coe_insert,Set.pairwiseDisjoint_insert]
        refine ⟨?_,?_⟩
        · intro H hH L hL hHL
          exact hD.2.1 (Finset.mem_of_mem_erase hH) (Finset.mem_of_mem_erase hL) hHL
        · intro H hH _
          exact (hsep H hH).mono_left (fun e he ↦ hc ▸ Or.inr he)
      · intro H hH _
        rcases Finset.mem_insert.mp hH with rfl | hH
        · exact hd
        · exact (hsep H hH).mono_left (fun e he ↦ hc ▸ Or.inl he)
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨H,_,he⟩; exact H.edgeSet_subset he
      · intro he
        have he' : e ∈ ⋃ H ∈ D, H.edgeSet := hD.2.2.symm ▸ he
        simp only [Set.mem_iUnion] at he'
        obtain ⟨H,hH,heH⟩ := he'
        by_cases hHK : H = K
        · subst H
          rcases (show e ∈ A.edgeSet ∪ B.edgeSet from hc.symm ▸ heH) with heA | heB
          · exact ⟨A,Finset.mem_insert_self _ _,heA⟩
          · exact ⟨B,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),heB⟩
        · exact ⟨H,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hHK,hH⟩)),heH⟩
  have hAout' : A ∉ insert B R := by simp only [Finset.mem_insert,not_or]; exact ⟨hAB,hAout⟩
  have hcard : E.card = D.card + 1 := by
    have hRcard := Finset.card_erase_add_one hK
    simp only [E,Finset.card_insert_of_notMem hAout',
      Finset.card_insert_of_notMem hBout]
    dsimp [R] at *
    omega
  refine ⟨hgood,hcard,?_⟩
  refine ⟨?_,?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hneA
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hneB
    exact hne H (Finset.mem_of_mem_erase hH)
  · intro x
    simp only [endpointMultiplicity,Finset.card_filter]
    rw [Finset.sum_insert hAout',Finset.sum_insert hBout]
    have hh := Finset.sum_erase_add D
      (fun H : G.Subgraph ↦ if (H.neighborSet x).ncard = 1 then 1 else 0) hK
    dsimp only at hh
    dsimp only [R]
    omega

lemma path_neighbor_one_iff {V : Type*} {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) (hn : ¬p.Nil) (x : V) :
    (p.toSubgraph.neighborSet x).ncard = 1 ↔ x = a ∨ x = b := by
  classical
  rw [path_neighbor_ncard_formula hp hn]
  split_ifs <;> simp_all

open scoped Classical in
/-- An inactive vertex in the graph support can be activated by splitting one
path there. All other endpoint multiplicities are preserved exactly. -/
lemma activate_vertex {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) {v : V} (hv : v ∈ G.support)
    (hz : endpointMultiplicity D v = 0) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ E.card = D.card + 1 ∧
      (endpointMultiplicity E v = 2) ∧
      (∀ x, x ≠ v → endpointMultiplicity E x = endpointMultiplicity D x) ∧
      inactive E = (inactive D).erase v := by
  classical
  obtain ⟨a,b,p,hp,hpn,hvp,hmem⟩ := hD.path_through_support hv
  have hab : a ≠ b := path_endpoints_ne hp (hne _ hmem)
  have hvends : ¬(v = a ∨ v = b) := by
    intro hh
    have h1 := (path_neighbor_one_iff hp hpn v).mpr hh
    have hm : p.toSubgraph ∈ D.filter (fun H ↦ (H.neighborSet v).ncard = 1) :=
      Finset.mem_filter.mpr ⟨hmem,h1⟩
    have hn := Finset.card_pos.mpr ⟨_,hm⟩
    change endpointMultiplicity D v > 0 at hn
    omega
  have hva : v ≠ a := (not_or.mp hvends).1
  have hvb : v ≠ b := (not_or.mp hvends).2
  let q := p.takeUntil v hvp
  let r := p.dropUntil v hvp
  have hq : q.IsPath := hp.takeUntil hvp
  have hr : r.IsPath := hp.dropUntil hvp
  have hqn : ¬q.Nil := Walk.not_nil_of_ne hva.symm
  have hrn : ¬r.Nil := Walk.not_nil_of_ne hvb
  have hqne : q.toSubgraph.edgeSet.Nonempty := ⟨s(a,q.snd),q.toSubgraph_adj_snd hqn⟩
  have hrne : r.toSubgraph.edgeSet.Nonempty := ⟨s(v,r.snd),r.toSubgraph_adj_snd hrn⟩
  have hdis : Disjoint q.toSubgraph.edgeSet r.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heq her
    exact List.disjoint_left.mp (hp.isTrail.disjoint_edges_takeUntil_dropUntil hvp)
      (q.mem_edges_toSubgraph.mp heq) (r.mem_edges_toSubgraph.mp her)
  have hcover : q.toSubgraph.edgeSet ∪ r.toSubgraph.edgeSet = p.toSubgraph.edgeSet := by
    rw [←Subgraph.edgeSet_sup,←Walk.toSubgraph_append]
    simp only [q,r,Walk.take_spec]
  obtain ⟨hE,hcard,hEne,hends⟩ := split_member hD hmem
    ⟨a,v,q,hq,rfl⟩ ⟨v,b,r,hr,rfl⟩ hqne hrne hdis hcover hne
  let E := insert q.toSubgraph (insert r.toSubgraph (D.erase p.toSubgraph))
  have hformula (x : V) : endpointMultiplicity E x = endpointMultiplicity D x +
      2*(if x = v then 1 else 0) := by
    have hh := hends x
    simp only [path_neighbor_one_iff hp hpn,path_neighbor_one_iff hq hqn,
      path_neighbor_one_iff hr hrn] at hh
    by_cases hxv : x = v
    · subst x
      simp only [hva,hvb,or_self,↓reduceIte,or_true,true_or] at hh
      simpa only [↓reduceIte,mul_one] using hh
    · by_cases hxa : x = a
      · subst x
        simp only [hxv,hab,or_self,↓reduceIte,true_or] at hh
        simp only [hxv,↓reduceIte,mul_zero,add_zero]
        change endpointMultiplicity E a + 1 = endpointMultiplicity D a + 1 + 0 at hh
        omega
      · by_cases hxb : x = b
        · subst x
          simp only [hxv,hxa,or_self,↓reduceIte,or_true] at hh
          simp only [hxv,↓reduceIte,mul_zero,add_zero]
          change endpointMultiplicity E b + 1 = endpointMultiplicity D b + 0 + 1 at hh
          omega
        · simp only [hxv,hxa,hxb,or_self,↓reduceIte,add_zero] at hh
          simpa only [hxv,↓reduceIte,mul_zero,add_zero] using hh
  have hEv : endpointMultiplicity E v = 2 := by simpa [hz] using hformula v
  have hEx (x : V) (hx : x ≠ v) : endpointMultiplicity E x = endpointMultiplicity D x := by
    simpa [hx] using hformula x
  refine ⟨E,hE,hEne,hcard,hEv,hEx,?_⟩
  ext x
  simp only [inactive,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
  by_cases hx : x = v
  · subst x
    simp [hEv]
  · simp [hx,hEx x hx]

/-- Exact downward closure, with the increase in the number of paths recorded.
The support hypothesis excludes the unavoidable inactive isolated vertices. -/
lemma realize_subset {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hsupp : ∀ v, v ∈ G.support) {D : Finset G.Subgraph}
    (hD : GoodDecomposition G D) (hne : ∀ H ∈ D, H.edgeSet.Nonempty)
    (hb : ∀ v, endpointMultiplicity D v ≤ 2) (A : Finset V) (hA : A ⊆ inactive D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ (∀ v, endpointMultiplicity E v ≤ 2) ∧
      inactive E = A ∧ E.card + A.card = D.card + (inactive D).card := by
  classical
  generalize hn : ((inactive D) \ A).card = n
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases heq : inactive D = A
    · exact ⟨D,hD,hne,hb,heq,by rw [heq]⟩
    have hss : A ⊂ inactive D := Finset.ssubset_iff_subset_ne.mpr ⟨hA,Ne.symm heq⟩
    obtain ⟨v,hvI,hvA⟩ := Finset.exists_of_ssubset hss
    have hz : endpointMultiplicity D v = 0 := (Finset.mem_filter.mp hvI).2
    obtain ⟨E,hE,hEne,hc,hEv,hEx,hEi⟩ := activate_vertex hD hne (hsupp v) hz
    have hbE (x : V) : endpointMultiplicity E x ≤ 2 := by
      by_cases hx : x = v
      · simp [hx,hEv]
      · rw [hEx x hx]; exact hb x
    have hAE : A ⊆ inactive E := by
      rw [hEi]
      intro x hx
      exact Finset.mem_erase.mpr ⟨fun he ↦ hvA (he ▸ hx),hA hx⟩
    have hdiff : inactive E \ A = (inactive D \ A).erase v := by
      ext x
      simp only [hEi,Finset.mem_sdiff,Finset.mem_erase]
      tauto
    have hvdiff : v ∈ inactive D \ A := Finset.mem_sdiff.mpr ⟨hvI,hvA⟩
    have hlt : (inactive E \ A).card < n := by
      rw [hdiff,←hn]
      exact Finset.card_erase_lt_of_mem hvdiff
    obtain ⟨F,hF,hFne,hFb,hFi,hFc⟩ := ih _ hlt hE hEne hbE hAE rfl
    have hci : (inactive E).card + 1 = (inactive D).card := by
      rw [hEi]
      exact Finset.card_erase_add_one hvI
    exact ⟨F,hF,hFne,hFb,hFi,by omega⟩

/-- Exact feasible inactive sets, without a cardinal bound. -/
def FeasibleInactive {V : Type*} [Fintype V] (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
    (∀ H ∈ D, H.edgeSet.Nonempty) ∧ (∀ v, endpointMultiplicity D v ≤ 2) ∧ inactive D = A

lemma feasible_downward_closed {V : Type*} [Fintype V] [Nontrivial V]
    {G : SimpleGraph V} (hG : G.Connected) {A B : Finset V}
    (hB : FeasibleInactive G B) (hAB : A ⊆ B) : FeasibleInactive G A := by
  obtain ⟨D,hD,hne,hb,hI⟩ := hB
  obtain ⟨E,hE,hEne,hEb,hEi,_⟩ := realize_subset
    (fun v ↦ hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ v)
    hD hne hb A (hI.symm ▸ hAB)
  exact ⟨E,hE,hEne,hEb,hEi⟩

/-- When an original vertex is paired with its own leaf, no projected nonempty
path can have that original vertex as an endpoint. -/
lemma projection_inactive_of_owner_eq {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} {k : ℕ} (T : NormalTrailSystem (leafCompletion G S) k)
    (hp : ∀ i, (T.walk i).IsPath) {D : Finset G.Subgraph}
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty)
    (htrack : ∀ H ∈ D, ∃ i, H = (projectWalk (T.walk i)).toSubgraph)
    (v : S) (hown : NormalTrailSystem.owner T (.inl v.val) = NormalTrailSystem.owner T (.inr v)) :
    endpointMultiplicity D v.val = 0 := by
  classical
  by_contra hz
  have hpos : 0 < (D.filter fun H ↦ (H.neighborSet v.val).ncard = 1).card := by
    change 0 < endpointMultiplicity D v.val
    omega
  obtain ⟨H,hH⟩ := Finset.card_pos.mp hpos
  obtain ⟨hHD,hdeg⟩ := Finset.mem_filter.mp hH
  obtain ⟨i,rfl⟩ := htrack H hHD
  have hpn : ¬(projectWalk (T.walk i)).Nil := by
    intro hn
    obtain ⟨e,he⟩ := hne _ hHD
    have he' := (projectWalk (T.walk i)).mem_edges_toSubgraph.mp he
    rw [Walk.edges_eq_nil.mpr hn] at he'
    exact List.not_mem_nil he' 
  have hend := (path_neighbor_one_iff (project_path_support _ (hp i)).1 hpn v.val).mp hdeg
  have howner (x : V ⊕ S) (hx : root x = v.val) :
      NormalTrailSystem.owner T x = NormalTrailSystem.owner T (.inl v.val) := by
    cases x with
    | inl x => have he : x=v.val := hx; subst x; rfl
    | inr x =>
      have he : x=v := Subtype.ext hx
      subst x
      exact hown.symm
  have hi : NormalTrailSystem.owner T (.inl v.val) = i := by
    rcases hend with hh | hh
    · rw [← howner (T.start i) hh.symm]
      exact (NormalTrailSystem.endpoint_iff_owner T _ i).mp (Or.inl rfl)
    · rw [← howner (T.finish i) hh.symm]
      exact (NormalTrailSystem.endpoint_iff_owner T _ i).mp (Or.inr rfl)
  have hstart := (NormalTrailSystem.endpoint_iff_owner T (.inl v.val) i).mpr hi
  have hfinish := (NormalTrailSystem.endpoint_iff_owner T (.inr v) i).mpr (hown.symm.trans hi)
  have he : root (T.start i) = root (T.finish i) := by
    rcases hstart with hs | hs <;> rcases hfinish with hf | hf
    · exact (Sum.inl_ne_inr (hs.trans hf.symm)).elim
    · rw [←hs,←hf]; rfl
    · rw [←hs,←hf]; rfl
    · exact (Sum.inl_ne_inr (hs.trans hf.symm)).elim
  exact hpn ((project_nil_iff (T.walk i) (hp i)).mpr he)

/-- Any one specified even vertex can be made inactive in a normal partition.
There is still no simultaneous cardinality assertion here. -/
lemma exists_normal_inactive_at {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (hv : Even (Nat.card (G.neighborSet v))) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ (∀ x, endpointMultiplicity D x ≤ 2) ∧
      endpointMultiplicity D v = 0 := by
  classical
  let S : Set V := {x | Even (Nat.card (G.neighborSet x))}
  let H := leafCompletion G S
  let v' : S := ⟨v,hv⟩
  have ho (x : V ⊕ S) : Odd (H.degree x) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using leafCompletion_odd G x
  obtain ⟨k,_,⟨T⟩⟩ := all_odd_normal_trail_system H ho
  obtain ⟨R,hR⟩ := T.exists_max_score
  have hadj : H.Adj (.inl v) (.inr v') := rfl
  obtain ⟨U,hU,t,q,hq,hmem⟩ := TrailNormalization.force_first_edge R hR hadj
  have hUmax : ∀ X : NormalTrailSystem H k, X.score ≤ U.score := by
    intro X; rw [hU]; exact hR X
  have hpq := TrailNormalization.max_score_member_isPath U hUmax _ hq hmem
  have hqn : q.Nil := by
    by_contra hn
    have hs : q.snd = .inl v := (leaf_adj v' _).mp (q.adj_snd hn)
    have hh : Sum.inl v ∈ q.support := hs ▸ q.getVert_mem_support 1
    exact (Walk.cons_isPath_iff hadj q).mp hpq |>.2 hh
  cases hqn
  obtain ⟨i,hends,_⟩ := hmem
  have hown : NormalTrailSystem.owner U (.inl v) = NormalTrailSystem.owner U (.inr v') := by
    have h1 : NormalTrailSystem.owner U (.inl v) = i := by
      apply (NormalTrailSystem.endpoint_iff_owner U _ i).mp
      exact hends.elim (fun h ↦ Or.inl h.1.symm) (fun h ↦ Or.inr h.2.symm)
    have h2 : NormalTrailSystem.owner U (.inr v') = i := by
      apply (NormalTrailSystem.endpoint_iff_owner U _ i).mp
      exact hends.elim (fun h ↦ Or.inr h.2.symm) (fun h ↦ Or.inl h.1.symm)
    exact h1.trans h2.symm
  have hpU := TrailNormalization.max_score_isPath U hUmax
  obtain ⟨D,hD,hne,_,hb,htrack⟩ := project_system_tracked U hpU
  refine ⟨D,hD,hne,fun x ↦ (hb x).trans (by split_ifs <;> omega),?_⟩
  exact projection_inactive_of_owner_eq U hpU hne htrack v' hown

lemma feasible_singleton {V : Type*} [Fintype V] [Nontrivial V]
    {G : SimpleGraph V} (hG : G.Connected) (v : V)
    (hv : Even (Nat.card (G.neighborSet v))) : FeasibleInactive G {v} := by
  classical
  obtain ⟨D,hD,hne,hb,hvD⟩ := exists_normal_inactive_at G v hv
  apply feasible_downward_closed hG (A := {v}) (B := inactive D)
  · exact ⟨D,hD,hne,hb,rfl⟩
  · simp only [Finset.singleton_subset_iff]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvD⟩

open scoped Classical in
/-- The reverse controlled operation: concatenate two paths through an active
vertex, when their concatenation is simple. Only that vertex is deactivated. -/
lemma deactivate_by_append {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty)
    {a v b : V} (p : G.Walk a v) (q : G.Walk v b)
    (hp : p.IsPath) (hq : q.IsPath) (hpq : (p.append q).IsPath)
    (hP : p.toSubgraph ∈ D) (hQ : q.toSubgraph ∈ D)
    (hv : endpointMultiplicity D v = 2) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ E.card + 1 = D.card ∧
      endpointMultiplicity E v = 0 ∧
      (∀ x, x ≠ v → endpointMultiplicity E x = endpointMultiplicity D x) ∧
      inactive E = insert v (inactive D) := by
  classical
  let P := p.toSubgraph
  let Q := q.toSubgraph
  let K := (p.append q).toSubgraph
  have hpn : ¬p.Nil := Walk.not_nil_of_ne (path_endpoints_ne hp (hne _ hP))
  have hqn : ¬q.Nil := Walk.not_nil_of_ne (path_endpoints_ne hq (hne _ hQ))
  have hav : a ≠ v := path_endpoints_ne hp (hne _ hP)
  have hvb : v ≠ b := path_endpoints_ne hq (hne _ hQ)
  have hdis : Disjoint P.edgeSet Q.edgeSet := RootedTailSystem.append_trail_disjoint hpq.isTrail
  have hPQ : P ≠ Q := by
    intro hh
    obtain ⟨e,he⟩ := hne _ hP
    exact Set.disjoint_left.mp hdis he (hh ▸ he)
  let R := (D.erase P).erase Q
  let E := insert K R
  have hKe : K = P ⊔ Q := Walk.toSubgraph_append p q
  have hE : GoodDecomposition G E := by
    rw [show E = insert (P ⊔ Q) R from congrArg (fun L ↦ insert L R) hKe]
    apply hD.merge hP hQ
    exact ⟨a,b,p.append q,hpq,hKe.symm⟩
  have hKne : K.edgeSet.Nonempty := by
    obtain ⟨e,he⟩ := hne _ hP
    exact ⟨e,by rw [hKe,Subgraph.edgeSet_sup]; exact Or.inl he⟩
  have hab : a ≠ b := path_endpoints_ne hpq hKne
  have hpqn : ¬(p.append q).Nil := Walk.not_nil_of_ne hab
  have hEne : ∀ H ∈ E, H.edgeSet.Nonempty := by
    intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · exact hKne
    · exact hne H (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hH))
  have hKout : K ∉ R := by
    intro hKR
    have hKD := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hKR)
    have hKP : K ≠ P := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hKR)).1
    obtain ⟨e,he⟩ := hne _ hP
    have heK : e ∈ K.edgeSet := by rw [hKe,Subgraph.edgeSet_sup]; exact Or.inl he
    exact Set.disjoint_left.mp (hD.2.1 hKD hP hKP) heK he
  have hrestore : insert P (insert Q (E.erase K)) = D := by
    rw [show E.erase K = R from Finset.erase_insert hKout]
    dsimp only [R]
    rw [Finset.insert_erase (Finset.mem_erase.mpr ⟨hPQ.symm,hQ⟩),Finset.insert_erase hP]
  obtain ⟨_,hc,_,he⟩ := split_member hE (Finset.mem_insert_self _ _)
    ⟨a,v,p,hp,rfl⟩ ⟨v,b,q,hq,rfl⟩ (hne _ hP) (hne _ hQ) hdis
    (by rw [hKe,Subgraph.edgeSet_sup]) hEne
  change (insert P (insert Q (E.erase K))).card = E.card + 1 at hc
  rw [hrestore] at hc
  have hformula (x : V) : endpointMultiplicity D x = endpointMultiplicity E x +
      2*(if x = v then 1 else 0) := by
    have hh := he x
    change endpointMultiplicity (insert P (insert Q (E.erase K))) x + _ = _ at hh
    rw [hrestore] at hh
    simp only [K,path_neighbor_one_iff hpq hpqn,path_neighbor_one_iff hp hpn,
      path_neighbor_one_iff hq hqn] at hh
    by_cases hxv : x = v
    · subst x
      simp only [hav.symm,hvb,or_self,↓reduceIte,or_true,true_or] at hh
      simpa only [↓reduceIte,mul_one] using hh
    · by_cases hxa : x = a
      · subst x
        simp only [hxv,hab,or_self,↓reduceIte,true_or] at hh
        simp only [hxv,↓reduceIte,mul_zero,add_zero]
        omega
      · by_cases hxb : x = b
        · subst x
          simp only [hxv,hxa,or_self,↓reduceIte,or_true] at hh
          simp only [hxv,↓reduceIte,mul_zero,add_zero]
          omega
        · simp only [hxv,hxa,hxb,or_self,↓reduceIte,add_zero] at hh
          simpa only [hxv,↓reduceIte,mul_zero,add_zero] using hh
  have hEv : endpointMultiplicity E v = 0 := by
    have hh := hformula v
    simp only [↓reduceIte,mul_one,hv] at hh
    omega
  have hEx (x : V) (hx : x ≠ v) : endpointMultiplicity E x = endpointMultiplicity D x := by
    simpa only [hx,↓reduceIte,mul_zero,add_zero] using (hformula x).symm
  refine ⟨E,hE,hEne,hc.symm,hEv,hEx,?_⟩
  ext x
  simp only [inactive,Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hx : x = v
  · simp [hx,hEv]
  · simp [hx,hEx x hx]

/-- Maximality forces a genuine intersection obstruction at every attempted
endpoint merge. This is a necessary condition, not the missing global count. -/
lemma max_inactive_pair_intersects {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ x, endpointMultiplicity D x ≤ 2)
    (hmax : ∀ E : Finset G.Subgraph, GoodDecomposition G E →
      (∀ H ∈ E, H.edgeSet.Nonempty) → (∀ x, endpointMultiplicity E x ≤ 2) →
      (inactive E).card ≤ (inactive D).card)
    {a v b : V} (p : G.Walk a v) (q : G.Walk v b)
    (hp : p.IsPath) (hq : q.IsPath) (hP : p.toSubgraph ∈ D) (hQ : q.toSubgraph ∈ D)
    (hv : endpointMultiplicity D v = 2) :
    ∃ x, x ≠ v ∧ x ∈ p.support ∧ x ∈ q.support := by
  classical
  by_contra hn
  have hpq : (p.append q).IsPath := by
    apply path_append_of_support_intersection hp hq
    intro x hxp hxq
    by_contra hxv
    exact hn ⟨x,hxv,hxp,hxq⟩
  obtain ⟨E,hE,hEne,_,hEv,hEx,hEi⟩ := deactivate_by_append hD hne p q hp hq hpq hP hQ hv
  have hbE (x : V) : endpointMultiplicity E x ≤ 2 := by
    by_cases hx : x = v
    · simp [hx,hEv]
    · rw [hEx x hx]; exact hb x
  have hcap := hmax E hE hEne hbE
  have hvout : v ∉ inactive D := by
    simp [inactive,hv]
  rw [hEi,Finset.card_insert_of_notMem hvout] at hcap
  omega

lemma walk_hits_boundary {V : Type*} {G : SimpleGraph V} (S : Set V) (c : V)
    (hbd : ∀ u ∈ S, ∀ w, w ∉ S → G.Adj u w → w = c)
    {a b : V} (p : G.Walk a b) (ha : a ∈ S) (hb : b ∉ S) : c ∈ p.support := by
  classical
  revert ha hb
  induction p with
  | nil => intro ha hb; exact (hb ha).elim
  | @cons a w b h p ih =>
    intro ha hb
    by_cases hw : w ∈ S
    · exact List.mem_cons_of_mem _ (ih hw hb)
    · have hwc := hbd a ha w hw h
      exact List.mem_cons_of_mem _ (hwc ▸ p.start_mem_support)

lemma path_endpoint_in_pendant_region {V : Type*} {G : SimpleGraph V}
    (S : Set V) (c : V) (hc : c ∉ S)
    (hbd : ∀ u ∈ S, ∀ w, w ∉ S → G.Adj u w → w = c)
    {a b x : V} (p : G.Walk a b) (hp : p.IsPath) (hx : x ∈ S) (hxp : x ∈ p.support) :
    a ∈ S ∨ b ∈ S := by
  classical
  by_contra hn
  obtain ⟨ha,hb⟩ := not_or.mp hn
  let q := p.takeUntil x hxp
  let r := p.dropUntil x hxp
  have hcq : c ∈ q.support := by
    simpa using walk_hits_boundary S c hbd q.reverse hx ha
  have hcr : c ∈ r.support := walk_hits_boundary S c hbd r hx hb
  have hqr : (q.append r).IsPath := by simpa only [q,r,Walk.take_spec] using hp
  have hcx : c ≠ x := fun he ↦ hc (he.symm ▸ hx)
  exact hqr.ne_of_mem_support_of_append hcx hcq hcr rfl

/-- A supported region attached to the rest only through one outside vertex
cannot consist entirely of inactive vertices. This justifies the articulation
obstruction used in exact feasibility diagnostics. -/
lemma no_inactive_pendant_region {V : Type*} {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (S : Set V) (c : V) (hc : c ∉ S)
    (hbd : ∀ u ∈ S, ∀ w, w ∉ S → G.Adj u w → w = c)
    (hz : ∀ x ∈ S, endpointMultiplicity D x = 0)
    {x : V} (hx : x ∈ S) (hsupp : x ∈ G.support) : False := by
  classical
  obtain ⟨a,b,p,hp,hpn,hxp,hmem⟩ := hD.path_through_support hsupp
  have hends := path_endpoint_in_pendant_region S c hc hbd p hp hx hxp
  have hpos (v : V) (hv : v = a ∨ v = b) : 0 < endpointMultiplicity D v := by
    apply Finset.card_pos.mpr
    exact ⟨p.toSubgraph,Finset.mem_filter.mpr ⟨hmem,(path_neighbor_one_iff hp hpn v).mpr hv⟩⟩
  rcases hends with ha | hb
  · have h1 := hpos a (Or.inl rfl)
    have h2 := hz a ha
    omega
  · have h1 := hpos b (Or.inr rfl)
    have h2 := hz b hb
    omega

open scoped Classical in
/-- The one-vertex forcing result already gives the Gallai bound whenever
there are at most three even-degree vertices; connectivity is unnecessary. -/
lemma gallai_of_at_most_three_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hfew : (Finset.univ.filter fun v ↦ Even (G.degree v)).card ≤ 3) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  by_cases hsmall : (Finset.univ.filter fun v ↦ Even (G.degree v)).card ≤ 1
  · obtain ⟨D,hD,hne,hb⟩ := exists_normal_decomposition G
    exact ⟨D,hD,(normal_gallai_iff hD hne (fun v ↦ (hb v).1)).mpr (by omega)⟩
  · obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter fun v ↦ Even (G.degree v)).card by omega)
    have hv' : Even (Nat.card (G.neighborSet v)) := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using (Finset.mem_filter.mp hv).2
    obtain ⟨D,hD,hne,hb,hzero⟩ := exists_normal_inactive_at G v hv'
    have hin : v ∈ inactive D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero⟩
    have hpos := Finset.card_pos.mpr ⟨v,hin⟩
    exact ⟨D,hD,(normal_gallai_iff hD hne hb).mpr (by omega)⟩

end Erdos583ActivationDevelopment
