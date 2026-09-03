import Submission.StarCopyIntegrated

/-! A quota-tracked edge-restoration criterion. This is an auxiliary result. -/
namespace Erdos583EvenEdgeRestorationDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.QuotaRooted
open Erdos583Work.EndpointSelection Erdos583Work.PendantCompletion
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma decomposition_path_family_tracked {V : Type*} {G : SimpleGraph V}
    (D : Finset G.Subgraph) (hD : GoodDecomposition G D)
    (hne : ∀ K ∈ D, K.edgeSet.Nonempty) :
    ∃ T : TrailFamily G D.card, (∀ i, (T.walk i).IsPath) ∧
      ∀ x, T.quota x = endpointMultiplicity D x := by
  classical
  choose a b p hp he using fun K : D ↦ hD.1 K.val K.property
  let e : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (by simp)).symm
  let T : TrailFamily G D.card :=
    { start := a ∘ e, finish := b ∘ e, walk := fun i ↦ p (e i),
      isTrail := fun i ↦ (hp (e i)).isTrail,
      disjoint := by
        intro i j hij
        rw [←he,←he]
        exact hD.2.1 (e i).property (e j).property
          (fun h ↦ hij (e.injective (Subtype.ext h)))
      cover := by
        intro d
        rw [←hD.2.2]
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨K,hK,hd⟩
          refine ⟨e.symm ⟨K,hK⟩,?_⟩
          rw [←he]
          simpa only [e.apply_symm_apply] using hd
        · rintro ⟨i,hi⟩
          exact ⟨(e i).val,(e i).property,by rwa [←he] at hi⟩ }
  refine ⟨T,fun i ↦ hp (e i),?_⟩
  intro x
  rw [quota_eq_sum_endpoints]
  change (∑ i, ((if a (e i)=x then 1 else 0)+(if b (e i)=x then 1 else 0))) = _
  rw [e.sum_comp (fun K ↦ ((if a K=x then 1 else 0)+(if b K=x then 1 else 0) : ℕ))]
  have hterm (K : D) : ((if a K=x then 1 else 0)+(if b K=x then 1 else 0) : ℕ) =
      if (K.val.neighborSet x).ncard=1 then 1 else 0 := by
    have hpn : ¬(p K).Nil := Walk.not_nil_of_ne (path_endpoints_ne (hp K) (he K ▸ hne _ K.property))
    have hab : a K ≠ b K := path_endpoints_ne (hp K) (he K ▸ hne _ K.property)
    simp only [he K,path_neighbor_one_iff (hp K) hpn]
    split_ifs <;> aesop
  simp_rw [hterm]
  simpa only [endpointMultiplicity,Finset.card_filter] using
    (Finset.sum_coe_sort D (fun K ↦ if (K.neighborSet x).ncard=1 then 1 else 0))

/-- Restoration only requires acyclicity of the actual zero-baseline set,
not of the whole graph on even vertices. -/
lemma restore_of_zero_forest {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath)
    (hu : T.quota u=1) (hv : T.quota v=1)
    (hf : (G.induce {x | T.quota x=0 ∨ x=u ∨ x=v}).IsAcyclic) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k := by
  classical
  by_contra hfail
  obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T (v := u) (by omega)
  have hc : G.edgeSet=insert s(v,u) (G.deleteEdges {s(v,u)}).edgeSet := by
    rw [edgeSet_deleteEdges,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(v,u) ∈ G.edgeSet from h)).symm
  obtain ⟨U,hs,hq,_,hr⟩ := DeletionEndpoint.append_new_edge_tracked
    (G.deleteEdges_le _) T hp i hi h (by simp) hc
  have hnp : ¬∀ i, (U.walk i).IsPath := by
    intro hpath
    exact hfail (MatchingAppend.path_family_partition U hpath)
  have hscore : U.score+1=G.edgeSet.ncard+k := by
    have hupper := U.score_le_edges_add
    have hne := U.score_eq_edges_add_iff.not.mpr hnp
    omega
  let b (x : V) : ℕ := if x=u ∨ x=v then 0 else T.quota x
  have hquota (x : V) : U.quota x=b x+2*(if v=x then 1 else 0) := by
    have hh := hq x
    dsimp only [b]
    by_cases hxu : x=u
    · subst x
      simp only [hu, h.ne, h.ne.symm, ↓reduceIte, true_or, mul_zero, add_zero] at hh ⊢
      omega
    by_cases hxv : x=v
    · subst x
      simp only [hv, h.ne, h.ne.symm, ↓reduceIte, or_true, mul_one, zero_add, add_zero] at hh ⊢
      omega
    · simp only [hxu,hxv,Ne.symm hxu,Ne.symm hxv,or_self,↓reduceIte,mul_zero,add_zero] at hh ⊢
      exact hh
  have hzero : {x | b x=0}={x | T.quota x=0 ∨ x=u ∨ x=v} := by
    ext x
    simp only [Set.mem_setOf_eq,b]
    split_ifs <;> aesop
  obtain ⟨r,P,_,hP⟩ := ForestZeroNormalization.normalize_one_defect_forest U b v
    hscore hquota (hr hnp) (by rwa [hzero])
  exact hfail (MatchingAppend.path_family_partition P hP)

lemma acyclic_of_edges_incident {V : Type*} {G : SimpleGraph V} (r : V)
    (h : ∀ ⦃x y⦄, G.Adj x y → x=r ∨ y=r) : G.IsAcyclic := by
  intro v p hp
  have hn : ¬p.Nil := hp.not_nil
  obtain ⟨x,hxp,hxr⟩ : ∃ x ∈ p.support, x ≠ r := by
    by_cases hv : v=r
    · refine ⟨p.snd,p.getVert_mem_support 1,?_⟩
      have ha := p.adj_snd hn
      exact fun hh ↦ ha.ne (hv.trans hh.symm)
    · exact ⟨v,p.start_mem_support,hv⟩
  have hs : p.toSubgraph.neighborSet x ⊆ {r} := by
    intro y hy
    exact (h (p.toSubgraph.adj_sub hy)).resolve_left hxr
  have hc := Set.ncard_le_ncard hs
  rw [hp.ncard_neighborSet_toSubgraph_eq_two hxp,Set.ncard_singleton] at hc
  omega

lemma even_count_delete_edge {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : G.Adj v u)
    (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) :
    (Finset.univ.filter fun x ↦ Even (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet x))).card+2 =
      (Finset.univ.filter fun x ↦ Even (Nat.card (G.neighborSet x))).card := by
  classical
  let A := Finset.univ.filter fun x ↦ Even (Nat.card (G.neighborSet x))
  have he : (Finset.univ.filter fun x ↦ Even (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet x))) =
      (A.erase u).erase v := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,A]
    by_cases hxu : x=u
    · subst x
      have ho := EdgeDefect.even_degree_delete_edge_odd h hu
      simp only [ne_eq,not_true_eq_false,and_false,false_and]
      exact iff_false_intro (Nat.not_even_iff_odd.mpr ho)
    by_cases hxv : x=v
    · subst x
      have ho := EdgeDefect.even_degree_delete_edge_odd h.symm hv
      rw [Sym2.eq_swap] at ho
      simp only [ne_eq,not_true_eq_false,false_and]
      exact iff_false_intro (Nat.not_even_iff_odd.mpr ho)
    · have hd : Nat.card ((G.deleteEdges {s(v,u)}).neighborSet x)=Nat.card (G.neighborSet x) := by
        simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
        exact degree_delete_edge_other G hxv hxu
      simp only [hd,ne_eq,hxu,hxv,not_false_eq_true,true_and]
  rw [he]
  have huA : u ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩
  have hvA : v ∈ A.erase u := Finset.mem_erase.mpr ⟨h.ne,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩
  have h1 := Finset.card_erase_add_one huA
  have h2 := Finset.card_erase_add_one hvA
  change _=A.card
  omega

/-- With at most five even-degree vertices, an even-even edge and a distinct
even vertex nonadjacent to one of its ends suffice for the Gallai budget.
No connectivity assumption is required. -/
lemma gallai_of_few_even_and_nonedge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfew : (Finset.univ.filter fun x ↦ Even (Nat.card (G.neighborSet x))).card ≤ 5)
    (a u v : V) (hau : a ≠ u) (hav : a ≠ v) (h : G.Adj v u)
    (ha : Even (Nat.card (G.neighborSet a)))
    (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) (hnot : ¬G.Adj a u) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  let J := G.deleteEdges {s(v,u)}
  have hJa : Even (Nat.card (J.neighborSet a)) := by
    have hd : Nat.card (J.neighborSet a)=Nat.card (G.neighborSet a) := by
      simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,J]
      exact degree_delete_edge_other G hav hau
    rwa [hd]
  have hJfew : (Finset.univ.filter fun x ↦ Even (J.degree x)).card ≤ 3 := by
    have hh := even_count_delete_edge h hu hv
    change (Finset.univ.filter fun x ↦ Even (Nat.card (J.neighborSet x))).card+2=_ at hh
    simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hh hfew
    omega
  obtain ⟨D,hD,hne,hb,hDa⟩ := exists_normal_inactive_at J a hJa
  have haI : a ∈ inactive D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hDa⟩
  have hIpos := Finset.card_pos.mpr ⟨a,haI⟩
  have hbound : D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ :=
    (normal_gallai_iff hD hne hb).mpr (by omega)
  by_contra hfail
  have hcard : D.card=⌈(Fintype.card V : ℚ)/2⌉₊ := by
    by_contra hh
    have hpath : IsPathSubgraph (G.subgraphOfAdj h) :=
      ⟨v,u,Walk.cons h Walk.nil,by simp [h.ne],by simp⟩
    have hrestore := @restore_path_subgraph V G (G.subgraphOfAdj h) hpath
    rw [G.edgeSet_subgraphOfAdj h] at hrestore
    obtain ⟨E,hE,hEc⟩ := hrestore hD
    exact hfail ⟨E,hE,by omega⟩
  have hIc : (inactive D).card ≤ 1 := by
    have hn := normal_count hD hne hb
    rw [hcard,BridgeGlue.ceil_half] at hn
    omega
  have hzero (x : V) : endpointMultiplicity D x=0 ↔ x=a := by
    constructor
    · intro hx
      exact Finset.card_le_one.mp hIc x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩) a haI
    · rintro rfl; exact hDa
  have hJu : Odd (Nat.card (J.neighborSet u)) := EdgeDefect.even_degree_delete_edge_odd h hu
  have hJv : Odd (Nat.card (J.neighborSet v)) := by
    have hh := EdgeDefect.even_degree_delete_edge_odd h.symm hv
    simpa only [Sym2.eq_swap,J] using hh
  have hqu : endpointMultiplicity D u=1 := by
    have hp := (hD.odd_endpointMultiplicity_iff u).mpr (by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hJu)
    have hb' := hb u
    rw [Nat.odd_iff] at hp
    omega
  have hqv : endpointMultiplicity D v=1 := by
    have hp := (hD.odd_endpointMultiplicity_iff v).mpr (by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hJv)
    have hb' := hb v
    rw [Nat.odd_iff] at hp
    omega
  obtain ⟨T,hT,hTq⟩ := decomposition_path_family_tracked D hD hne
  have hz (x : V) : T.quota x=0 ↔ x=a := by rw [hTq,hzero]
  have hf : (G.induce {x | T.quota x=0 ∨ x=u ∨ x=v}).IsAcyclic := by
    apply acyclic_of_edges_incident ⟨v,Or.inr (Or.inr rfl)⟩
    intro x y hxy
    by_cases hxv : x.val=v
    · exact Or.inl (Subtype.ext hxv)
    by_cases hyv : y.val=v
    · exact Or.inr (Subtype.ext hyv)
    have hx : x.val=a ∨ x.val=u := by
      have hh := x.property
      simp only [Set.mem_setOf_eq,hz] at hh
      exact hh.imp_right (fun h ↦ h.resolve_right hxv)
    have hy : y.val=a ∨ y.val=u := by
      have hh := y.property
      simp only [Set.mem_setOf_eq,hz] at hh
      exact hh.imp_right (fun h ↦ h.resolve_right hyv)
    change G.Adj x.val y.val at hxy
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · rw [hx,hy] at hxy; exact (G.irrefl hxy).elim
    · rw [hx,hy] at hxy; exact (hnot hxy).elim
    · rw [hx,hy] at hxy; exact (hnot hxy.symm).elim
    · rw [hx,hy] at hxy; exact (G.irrefl hxy).elim
  obtain ⟨E,hE,hEc⟩ := restore_of_zero_forest h T hT
    (by rw [hTq,hqu]) (by rw [hTq,hqv]) hf
  exact hfail ⟨E,hE,hEc.trans hbound⟩

end Erdos583EvenEdgeRestorationDevelopment
