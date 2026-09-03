import Submission.LocalZeroNormalization

/-! Matching restoration with protected positive quotas.  We retain indexed
path families during restoration, so intermediate nil slots and isolated
vertices do not require an additional hypothesis. -/
namespace Erdos583GuardedMatchingRestorationDevelopment
open SimpleGraph Erdos583Work Erdos583EvenEdgeRestorationDevelopment
open Erdos583NormalForestRestorationDevelopment
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.EvenMatchingRestore
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma restore_one_edge_zero_forest_tracked {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath)
    (hu : T.quota u=1) (hv : T.quota v=1) (hbound : ∀ x, T.quota x ≤ 2)
    (hf : (G.induce {x | T.quota x=0 ∨ x=u ∨ x=v}).IsAcyclic) :
    ∃ P : TrailFamily G k, (∀ i, (P.walk i).IsPath) ∧ (∀ x, P.quota x ≤ 2) ∧
      ∀ x, 0 < T.quota x → x ≠ u → x ≠ v → P.quota x=T.quota x := by
  classical
  obtain ⟨i,hi⟩ := DeletionEndpoint.endpoint_of_positive_quota T (v := u) (by omega)
  have hc : G.edgeSet=insert s(v,u) (G.deleteEdges {s(v,u)}).edgeSet := by
    rw [edgeSet_deleteEdges,Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem (show s(v,u) ∈ G.edgeSet from h)).symm
  obtain ⟨U,hs,hq,_,hr⟩ := DeletionEndpoint.append_new_edge_tracked
    (G.deleteEdges_le _) T hp i hi h (by simp) hc
  let b (x : V) : ℕ := if x=u ∨ x=v then 0 else T.quota x
  have hquota (x : V) : U.quota x=b x+2*(if v=x then 1 else 0) := by
    have hh := hq x
    dsimp only [b]
    by_cases hxu : x=u
    · subst x
      simp only [hu,h.ne,h.ne.symm,↓reduceIte,true_or,mul_zero,add_zero] at hh ⊢
      omega
    by_cases hxv : x=v
    · subst x
      simp only [hv,h.ne,h.ne.symm,↓reduceIte,or_true,mul_one,zero_add,add_zero] at hh ⊢
      omega
    · simp only [hxu,hxv,Ne.symm hxu,Ne.symm hxv,or_self,↓reduceIte,mul_zero,add_zero] at hh ⊢
      exact hh
  have hbb (x : V) : b x ≤ 2 := by dsimp [b]; split_ifs; omega; exact hbound x
  have hzero : {x | b x=0}={x | T.quota x=0 ∨ x=u ∨ x=v} := by
    ext x
    simp only [Set.mem_setOf_eq,b]
    split_ifs <;> aesop
  have hrootzero : b v=0 := by simp [b]
  have hex : ∃ r : V, b r=0 ∧ ∃ P : TrailFamily G k,
      (∀ x, P.quota x=b x+2*(if r=x then 1 else 0)) ∧ ∀ i, (P.walk i).IsPath := by
    by_cases hpaths : ∀ i, (U.walk i).IsPath
    · exact ⟨v,hrootzero,U,hquota,hpaths⟩
    · have hscore : U.score+1=G.edgeSet.ncard+k := by
        have hupper := U.score_le_edges_add
        have hne := U.score_eq_edges_add_iff.not.mpr hpaths
        omega
      exact normalize_zero_root_forest U b v hscore hquota
        (hr hpaths) hrootzero (by rwa [hzero])
  obtain ⟨r,hr0,P,hPq,hP⟩ := hex
  refine ⟨P,hP,?_,?_⟩
  · intro x
    rw [hPq]
    by_cases hrx : r=x
    · subst x; simp [hr0]
    · simpa [hrx] using hbb x
  · intro x hx hxu hxv
    have hbx : b x=T.quota x := by simp [b,hxu,hxv]
    have hrx : r ≠ x := by rintro rfl; rw [hbx] at hr0; omega
    simp [hPq,hbx,hrx]

lemma even_vertices_delete_edge_subset {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) :
    {x | Even (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet x))} ⊆
      {x | Even (Nat.card (G.neighborSet x))} := by
  intro x hx
  by_cases hxu : x=u
  · subst x; exact hu
  by_cases hxv : x=v
  · subst x; exact hv
  · have hd : Nat.card ((G.deleteEdges {s(v,u)}).neighborSet x)=Nat.card (G.neighborSet x) := by
      simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
      exact degree_delete_edge_other G hxv hxu
    rwa [Set.mem_setOf_eq,hd] at hx

lemma even_forest_off_delete_edge {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (hu : Even (Nat.card (G.neighborSet u)))
    (hv : Even (Nat.card (G.neighborSet v))) (A : Set V)
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x)) ∧ x ∉ A}).IsAcyclic) :
    ((G.deleteEdges {s(v,u)}).induce
      {x | Even (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet x)) ∧ x ∉ A}).IsAcyclic := by
  let f : ((G.deleteEdges {s(v,u)}).induce
      {x | Even (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet x)) ∧ x ∉ A}) →g
      (G.induce {x | Even (Nat.card (G.neighborSet x)) ∧ x ∉ A}) :=
    { toFun := fun x ↦ ⟨x.val,even_vertices_delete_edge_subset hu hv x.property.1,x.property.2⟩
      map_rel' := fun hxy ↦ G.deleteEdges_le _ hxy }
  apply hf.comap f
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : {x | Even (Nat.card (G.neighborSet x)) ∧ x ∉ A} ↦ z.val) hxy

lemma restore_even_edge_guarded {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u)
    (hu : Even (Nat.card (G.neighborSet u))) (hv : Even (Nat.card (G.neighborSet v)))
    (A : Set V) (huA : u ∉ A) (hvA : v ∉ A)
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x)) ∧ x ∉ A}).IsAcyclic)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath)
    (hb : ∀ x, T.quota x ≤ 2) (hA : ∀ x ∈ A, 0 < T.quota x) :
    ∃ P : TrailFamily G k, (∀ i, (P.walk i).IsPath) ∧ (∀ x, P.quota x ≤ 2) ∧
      ∀ x ∈ A, P.quota x=T.quota x := by
  have hqu : T.quota u=1 := by
    have ho := (QuotaParity.quota_odd_iff T u).mpr (EdgeDefect.even_degree_delete_edge_odd h hu)
    have hh := hb u
    rw [Nat.odd_iff] at ho
    omega
  have hqv : T.quota v=1 := by
    have hj : Odd (Nat.card ((G.deleteEdges {s(v,u)}).neighborSet v)) := by
      simpa only [Sym2.eq_swap] using EdgeDefect.even_degree_delete_edge_odd h.symm hv
    have ho := (QuotaParity.quota_odd_iff T v).mpr hj
    have hh := hb v
    rw [Nat.odd_iff] at ho
    omega
  have hsub : {x | T.quota x=0 ∨ x=u ∨ x=v} ⊆
      {x | Even (Nat.card (G.neighborSet x)) ∧ x ∉ A} := by
    intro x hx
    rcases hx with hz|rfl|rfl
    · exact ⟨even_vertices_delete_edge_subset hu hv (QuotaParity.zero_quota_even T hz),
        fun hxA ↦ by have hh := hA x hxA; omega⟩
    · exact ⟨hu,huA⟩
    · exact ⟨hv,hvA⟩
  have hf' := hf.comap (G.induceHomOfLE hsub).toHom (G.induceHomOfLE hsub).injective
  obtain ⟨P,hP,hPb,hPq⟩ := restore_one_edge_zero_forest_tracked h T hp hqu hqv hb hf'
  refine ⟨P,hP,hPb,?_⟩
  intro x hx
  exact hPq x (hA x hx) (fun hxu ↦ huA (hxu ▸ hx)) (fun hxv ↦ hvA (hxv ▸ hx))

lemma restore_matching_guarded {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (A : Set V) (hFA : ∀ ⦃x y⦄, F.Adj x y → x ∉ A)
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x)) ∧ x ∉ A}).IsAcyclic)
    {k : ℕ} (T : TrailFamily (G \ F) k) (hp : ∀ i, (T.walk i).IsPath)
    (hb : ∀ x, T.quota x ≤ 2) (hA : ∀ x ∈ A, 0 < T.quota x) :
    ∃ P : TrailFamily G k, (∀ i, (P.walk i).IsPath) ∧ (∀ x, P.quota x ≤ 2) ∧
      ∀ x ∈ A, P.quota x=T.quota x := by
  classical
  induction hn : F.edgeSet.ncard using Nat.strong_induction_on generalizing G F with
  | h n ih =>
    by_cases hbot : F=⊥
    · have hEq : G \ F=G := by
        ext a b
        simp only [hbot,sdiff_adj,bot_adj,not_false_eq_true,and_true]
      revert T
      rw [hEq]
      intro T hp hb hA
      exact ⟨T,hp,hb,fun _ _ ↦ rfl⟩
    obtain ⟨v,u,h⟩ := ne_bot_iff_exists_adj.mp hbot
    let J := G.deleteEdges {s(v,u)}
    let K := F.deleteEdges {s(v,u)}
    have hKJ : K ≤ J := deleteEdges_mono hFG
    have hKm : ∀ x, (K.neighborSet x).Subsingleton := by
      intro x a ha b hb
      exact hm x (F.deleteEdges_le _ ha) (F.deleteEdges_le _ hb)
    have hKe : ∀ ⦃x y⦄, K.Adj x y → Even (Nat.card (J.neighborSet x)) := by
      intro x y hxy
      obtain ⟨hxv,hxu⟩ := matching_delete_endpoints hm h hxy
      have heq : Nat.card (J.neighborSet x)=Nat.card (G.neighborSet x) := by
        simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
        exact degree_delete_edge_other G hxv hxu
      rw [heq]
      exact he (F.deleteEdges_le _ hxy)
    have hKA : ∀ ⦃x y⦄, K.Adj x y → x ∉ A := by
      intro x y hxy
      exact hFA (F.deleteEdges_le _ hxy)
    have hJf := even_forest_off_delete_edge (he h.symm) (he h) A hf
    have hdiff : J \ K=G \ F := by
      ext a b
      simp only [J,K,sdiff_adj,deleteEdges_adj,Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨hab,hne⟩,hn⟩
        exact ⟨hab,fun hF ↦ hn ⟨hF,hne⟩⟩
      · rintro ⟨hab,hn⟩
        refine ⟨⟨hab,?_⟩,fun hh ↦ hn hh.1⟩
        intro heq
        exact hn ((F.adj_congr_of_sym2 heq).mpr h)
    have hlt : K.edgeSet.ncard<n := by
      rw [←hn]
      change (F.deleteEdges {s(v,u)}).edgeSet.ncard < F.edgeSet.ncard
      rw [edgeSet_deleteEdges]
      exact Set.ncard_diff_singleton_lt_of_mem (show s(v,u) ∈ F.edgeSet from h)
    have hex : ∃ P : TrailFamily J k, (∀ i, (P.walk i).IsPath) ∧
        (∀ x, P.quota x ≤ 2) ∧ ∀ x ∈ A, P.quota x=T.quota x := by
      generalize hB : G \ F=B at T hp hb hA ⊢
      have hEq : J \ K=B := hdiff.trans hB
      cases hEq
      exact ih K.edgeSet.ncard hlt J K hKJ hKm hKe hKA hJf T hp hb hA rfl
    obtain ⟨U,hU,hUb,hUq⟩ := hex
    have hUA : ∀ x ∈ A, 0 < U.quota x := by
      intro x hx; rw [hUq x hx]; exact hA x hx
    obtain ⟨P,hP,hPb,hPq⟩ := restore_even_edge_guarded (hFG h) (he h.symm) (he h)
      A (hFA h.symm) (hFA h) hf U hU hUb hUA
    exact ⟨P,hP,hPb,fun x hx ↦ (hPq x hx).trans (hUq x hx)⟩

lemma partition_of_guarded_matching {V : Type*} [Fintype V] (G F : SimpleGraph V)
    (hFG : F ≤ G) (hm : ∀ x, (F.neighborSet x).Subsingleton)
    (he : ∀ ⦃x y⦄, F.Adj x y → Even (Nat.card (G.neighborSet x)))
    (A : Set V) (hFA : ∀ ⦃x y⦄, F.Adj x y → x ∉ A)
    (hf : (G.induce {x | Even (Nat.card (G.neighborSet x)) ∧ x ∉ A}).IsAcyclic)
    (D : Finset (G \ F).Subgraph) (hD : GoodDecomposition (G \ F) D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) (hb : ∀ x, endpointMultiplicity D x ≤ 2)
    (hA : ∀ x ∈ A, 0 < endpointMultiplicity D x) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity E x ≤ 2 := by
  obtain ⟨T,hT,hTq⟩ := decomposition_path_family_tracked D hD hne
  obtain ⟨P,hP,hPb,_⟩ := restore_matching_guarded G F hFG hm he A hFA hf T hT
    (fun x ↦ (hTq x) ▸ hb x) (fun x hx ↦ (hTq x) ▸ hA x hx)
  obtain ⟨E,hE,hEc,hEne,hEq⟩ := path_family_partition_quota_le P hP
  exact ⟨E,hE,hEc,hEne,fun x ↦ (hEq x).trans (hPb x)⟩

end Erdos583GuardedMatchingRestorationDevelopment
