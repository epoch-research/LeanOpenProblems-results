import Submission.EvenEdgeRestoration

/-! Normality-preserving restoration using zero-baseline forest normalization.
These auxiliary lemmas do not assert an unrestricted path bound. -/
namespace Erdos583NormalForestRestorationDevelopment
open SimpleGraph Erdos583Work Erdos583EvenEdgeRestorationDevelopment
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.DistinctTails Erdos583Work.EndpointSelection Erdos583Work.PendantCompletion
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma normalize_zero_root_forest {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (c : V → ℕ) (r : V)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hquota : ∀ v, T.quota v=c v+2*(if r=v then 1 else 0))
    (hroot : HasRoot T r) (hr0 : c r=0) (hforest : (G.induce {v | c v=0}).IsAcyclic) :
    ∃ r' : V, c r'=0 ∧ ∃ P : TrailFamily G k,
      (∀ v, P.quota v=c v+2*(if r'=v then 1 else 0)) ∧ ∀ i, (P.walk i).IsPath := by
  classical
  by_contra hn
  let W (a : V) : Prop := c a=0 ∧ ∃ U : TrailFamily G k, U.score=T.score ∧
    (∀ v, U.quota v=c v+2*(if a=v then 1 else 0)) ∧ HasRoot U a
  have hw : ∃ a, W a := ⟨r,hr0,T,rfl,hquota,hroot⟩
  have hnext (a : V) (ha : W a) : ∃ x y, x ≠ y ∧ G.Adj a x ∧ G.Adj a y ∧
      x ∈ ({v | c v=0} : Set V) ∧ y ∈ ({v | c v=0} : Set V) ∧ W x ∧ W y := by
    obtain ⟨ha0,U,hUs,hUq,A,R,ρ,hρ,hRn⟩ := ha
    have hscoreU : U.score+1=G.edgeSet.ncard+k := by omega
    obtain ⟨B,_,x,y,hxy,hax,hay,hxB,hyB,hEx,hEy⟩ := R.two_root_exposures ρ hρ hRn
    have hreach (z : V) (hzB : z ∉ B) (hE : ExposedRoot U a A B z) : c z=0 ∧ W z := by
      have hz0 : c z=0 := by
        by_contra hzne
        have hpos : 0 < U.quota z := by rw [hUq]; omega
        obtain ⟨P,hPq,hP⟩ := exposedRoot_repair_of_positive hE hscoreU hzB hpos
        exact hn ⟨a,ha0,P,fun v ↦ (hPq v).trans (hUq v),hP⟩
      have hpos : 2 ≤ U.quota a := by rw [hUq]; simp
      obtain ⟨P,hPq,hP⟩ := exposedRoot_move_pair_or_repair hE hscoreU hpos
      have hnewq (v : V) : P.quota v=c v+2*(if z=v then 1 else 0) := by
        have hh := hPq v
        rw [hUq] at hh
        omega
      rcases hP with hP | ⟨hPs,hPr⟩
      · exact (hn ⟨z,hz0,P,hnewq,hP⟩).elim
      · exact ⟨hz0,hz0,P,hPs.trans hUs,hnewq,hPr⟩
    obtain ⟨hx0,hWx⟩ := hreach x hxB hEx
    obtain ⟨hy0,hWy⟩ := hreach y hyB hEy
    exact ⟨x,y,hxy,hax,hay,hx0,hy0,hWx,hWy⟩
  exact cycle_of_two_zero_successors G {v | c v=0} W hw hnext hforest


lemma path_family_partition_quota_le {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (hp : ∀ i, (T.walk i).IsPath) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity D x ≤ T.quota x := by
  classical
  let f (i : Fin k) := (T.walk i).toSubgraph
  let I := Finset.univ.filter fun i ↦ (f i).edgeSet.Nonempty
  let D := I.image f
  have hmem (K) : K ∈ D ↔ ∃ i, (f i).edgeSet.Nonempty ∧ f i=K := by
    simp [D,I]
  have hgood : GoodDecomposition G D := by
    refine ⟨?_,?_,?_⟩
    · intro K hK
      obtain ⟨i,_,rfl⟩ := (hmem K).mp hK
      exact ⟨_,_,_,hp i,rfl⟩
    · intro K hK L hL hKL
      obtain ⟨i,_,rfl⟩ := (hmem K).mp hK
      obtain ⟨j,_,rfl⟩ := (hmem L).mp hL
      exact T.disjoint (fun he ↦ hKL (he ▸ rfl))
    · ext e
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨K,_,he⟩; exact K.edgeSet_subset he
      · intro he
        obtain ⟨i,hi⟩ := (T.cover e).mp he
        exact ⟨f i,(hmem _).mpr ⟨i,⟨e,hi⟩,rfl⟩,hi⟩
  refine ⟨D,hgood,Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (by simp)),?_,?_⟩
  · intro K hK
    obtain ⟨i,hi,rfl⟩ := (hmem K).mp hK
    exact hi
  · intro x
    let J := Finset.univ.filter fun i ↦ ((f i).neighborSet x).ncard=1
    have hsub : (D.filter fun K ↦ (K.neighborSet x).ncard=1) ⊆ J.image f := by
      intro K hK
      obtain ⟨hKD,hd⟩ := Finset.mem_filter.mp hK
      obtain ⟨i,_,rfl⟩ := (hmem K).mp hKD
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩,rfl⟩
    have hc : J.card ≤ T.quota x := by
      rw [quota_eq_sum_endpoints]
      simp only [J,Finset.card_filter]
      apply Finset.sum_le_sum
      intro i _
      by_cases hd : ((f i).neighborSet x).ncard=1
      · have hh : x=T.start i ∨ x=T.finish i :=
          ((trail_neighbor_ncard_odd_iff (T.isTrail i) x).mp (by rw [show
            ((T.walk i).toSubgraph.neighborSet x).ncard=1 from hd]; exact odd_one)).2
        simp only [hd,↓reduceIte]
        rcases hh with hh|hh <;> simp [hh]
      · simp [hd]
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hc)

lemma restore_normal_of_zero_forest {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {u v : V} (h : G.Adj v u)
    (T : TrailFamily (G.deleteEdges {s(v,u)}) k) (hp : ∀ i, (T.walk i).IsPath)
    (hu : T.quota u=1) (hv : T.quota v=1) (hbound : ∀ x, T.quota x ≤ 2)
    (hf : (G.induce {x | T.quota x=0 ∨ x=u ∨ x=v}).IsAcyclic) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ k ∧
      (∀ H ∈ D, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity D x ≤ 2 := by
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
  have hex : ∃ P : TrailFamily G k, (∀ x, P.quota x ≤ 2) ∧ ∀ i, (P.walk i).IsPath := by
    by_cases hpaths : ∀ i, (U.walk i).IsPath
    · refine ⟨U,?_,hpaths⟩
      intro x
      rw [hquota]
      by_cases hvx : v=x
      · subst x; simp [hrootzero]
      · simpa [hvx] using hbb x
    · have hscore : U.score+1=G.edgeSet.ncard+k := by
        have hupper := U.score_le_edges_add
        have hne := U.score_eq_edges_add_iff.not.mpr hpaths
        omega
      obtain ⟨r,hr0,P,hPq,hP⟩ := normalize_zero_root_forest U b v hscore hquota
        (hr hpaths) hrootzero (by rwa [hzero])
      refine ⟨P,?_,hP⟩
      intro x
      rw [hPq]
      by_cases hrx : r=x
      · subst x; simp [hr0]
      · simpa [hrx] using hbb x
  obtain ⟨P,hPq,hP⟩ := hex
  obtain ⟨D,hD,hDc,hDne,hDq⟩ := path_family_partition_quota_le P hP
  exact ⟨D,hD,hDc,hDne,fun x ↦ (hDq x).trans (hPq x)⟩

lemma restore_path_subgraph_tracked {V : Type*} {G : SimpleGraph V} (K : G.Subgraph)
    (hK : IsPathSubgraph K) (hKne : K.edgeSet.Nonempty)
    (D : Finset (G.deleteEdges K.edgeSet).Subgraph) (hD : GoodDecomposition (G.deleteEdges K.edgeSet) D)
    (hne : ∀ H ∈ D, H.edgeSet.Nonempty) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card+1 ∧
      (∀ H ∈ E, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity E x ≤
        endpointMultiplicity D x+(if (K.neighborSet x).ncard=1 then 1 else 0) := by
  classical
  let f := Subgraph.map (Hom.ofLE (G.deleteEdges_le K.edgeSet))
  let E := insert K (D.image f)
  have hgood : GoodDecomposition G E := by
    refine ⟨?_,restore_subgraph_partition K hD.2⟩
    intro H hH
    rcases Finset.mem_insert.mp hH with rfl|hH
    · exact hK
    · obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hH
      exact lift_path_subgraph _ (hD.1 L hL)
  refine ⟨E,hgood,(Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1),?_,?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl|hH
    · exact hKne
    · obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hH
      rw [edgeSet_lift]; exact hne L hL
  · intro x
    have hKe : K ∉ D.image f := by
      rintro hmem
      obtain ⟨L,_,he⟩ := Finset.mem_image.mp hmem
      obtain ⟨e,heK⟩ := hKne
      have heL : e ∈ L.edgeSet := by
        rw [←edgeSet_lift (G.deleteEdges_le K.edgeSet)]
        change e ∈ (f L).edgeSet
        rwa [he]
      exact (show e ∈ G.edgeSet ∧ e ∉ K.edgeSet by
        simpa only [edgeSet_deleteEdges,Set.mem_diff] using L.edgeSet_subset heL).2 heK
    have heq : endpointMultiplicity E x=endpointMultiplicity (D.image f) x+
        (if (K.neighborSet x).ncard=1 then 1 else 0) := by
      simp only [endpointMultiplicity,E,Finset.card_filter,Finset.sum_insert hKe]
      omega
    rw [heq,endpointMultiplicity_lift]

noncomputable def evenCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  {x | Even (Nat.card (G.neighborSet x))}.ncard

def SmallEvenForests {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, S ⊆ {x | Even (Nat.card (G.neighborSet x))} →
    2*S.ncard ≤ evenCount G+2 → (G.induce S).IsAcyclic

def NormalBound {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ ∧
    (∀ H ∈ D, H.edgeSet.Nonempty) ∧ ∀ x, endpointMultiplicity D x ≤ 2

lemma evenCount_eq_filter {V : Type*} [Fintype V] (G : SimpleGraph V) :
    evenCount G=(Finset.univ.filter fun x ↦ Even (Nat.card (G.neighborSet x))).card := by
  classical
  simp only [evenCount,Set.ncard_eq_toFinset_card',Set.toFinset_setOf]

lemma normal_bound_of_three_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hfew : evenCount G ≤ 3) : NormalBound G := by
  classical
  rw [evenCount_eq_filter] at hfew
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hfew
  by_cases hsmall : (Finset.univ.filter fun v ↦ Even (G.degree v)).card ≤ 1
  · obtain ⟨D,hD,hne,hb⟩ := exists_normal_decomposition G
    exact ⟨D,hD,(normal_gallai_iff hD hne (fun v ↦ (hb v).1)).mpr (by omega),hne,fun v ↦ (hb v).1⟩
  · obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter fun v ↦ Even (G.degree v)).card by omega)
    have hv' : Even (Nat.card (G.neighborSet v)) := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using (Finset.mem_filter.mp hv).2
    obtain ⟨D,hD,hne,hb,hzero⟩ := exists_normal_inactive_at G v hv'
    have hin : v ∈ inactive D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hzero⟩
    have hpos := Finset.card_pos.mpr ⟨v,hin⟩
    exact ⟨D,hD,(normal_gallai_iff hD hne hb).mpr (by omega),hne,hb⟩

lemma restore_normal_small_even_forests {V : Type*} [Fintype V] {G : SimpleGraph V}
    {u v : V} (h : G.Adj v u)
    (hu : Even (Nat.card (G.neighborSet u))) (hv : Even (Nat.card (G.neighborSet v)))
    (hf : SmallEvenForests G) (hbase : NormalBound (G.deleteEdges {s(v,u)})) : NormalBound G := by
  classical
  let J := G.deleteEdges {s(v,u)}
  obtain ⟨D,hD,hDc,hne,hb⟩ := hbase
  have hJu : Odd (Nat.card (J.neighborSet u)) := EdgeDefect.even_degree_delete_edge_odd h hu
  have hJv : Odd (Nat.card (J.neighborSet v)) := by
    simpa only [Sym2.eq_swap,J] using EdgeDefect.even_degree_delete_edge_odd h.symm hv
  have hqu : endpointMultiplicity D u=1 := MarkedBudgets.normal_odd_endpoint_eq_one hD hb hJu
  have hqv : endpointMultiplicity D v=1 := MarkedBudgets.normal_odd_endpoint_eq_one hD hb hJv
  by_cases hstrict : D.card < ⌈(Fintype.card V : ℚ)/2⌉₊
  · let K := G.subgraphOfAdj h
    have hK : IsPathSubgraph K := ⟨v,u,Walk.cons h Walk.nil,by simp [h.ne],by simp [K]⟩
    have hKne : K.edgeSet.Nonempty := by rw [G.edgeSet_subgraphOfAdj h]; exact Set.singleton_nonempty _
    have hrestore := restore_path_subgraph_tracked K hK hKne
    rw [G.edgeSet_subgraphOfAdj h] at hrestore
    obtain ⟨E,hE,hEc,hEne,hEq⟩ := hrestore D hD hne
    refine ⟨E,hE,by omega,hEne,?_⟩
    intro x
    have hh := hEq x
    have hdeg : (K.neighborSet x).ncard=1 ↔ x=v ∨ x=u := by
      have hp : (Walk.cons h Walk.nil).IsPath := by simp [h.ne]
      simpa only [Walk.toSubgraph_cons_nil_eq_subgraphOfAdj] using
        path_neighbor_one_iff hp (by simp) x
    simp only [hdeg] at hh
    by_cases hx : x=v ∨ x=u
    · rcases hx with rfl|rfl <;> simp only [true_or,or_true,↓reduceIte,hqu,hqv] at hh <;> omega
    · simpa only [hx,↓reduceIte,add_zero] using hh.trans (by simpa [hx] using hb x)
  · have hcard : D.card=⌈(Fintype.card V : ℚ)/2⌉₊ := by omega
    have hcount := normal_count hD hne hb
    have he := even_count_delete_edge h hu hv
    have heG : (Finset.univ.filter fun x ↦ Even (Nat.card (G.neighborSet x))).card=evenCount G :=
      (evenCount_eq_filter G).symm
    rw [heG] at he
    simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at he
    rw [hcard,BridgeGlue.ceil_half] at hcount
    let S : Set V := insert u (insert v (↑(inactive D) : Set V))
    have hSc : S.ncard ≤ (inactive D).card+2 := by
      have h1 := Set.ncard_insert_le u (insert v (↑(inactive D) : Set V))
      have h2 := Set.ncard_insert_le v (↑(inactive D) : Set V)
      rw [Set.ncard_coe_finset] at h2
      change S.ncard ≤ _ at h1
      omega
    have hsub : S ⊆ {x | Even (Nat.card (G.neighborSet x))} := by
      intro x hx
      rcases hx with rfl|rfl|hx
      · exact hu
      · exact hv
      · have hj : Even (J.degree x) := inactive_even hD hx
        by_cases hxu : x=u
        · subst x; exact hu
        by_cases hxv : x=v
        · subst x; exact hv
        · simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,Set.mem_setOf_eq]
          rwa [degree_delete_edge_other G hxv hxu] at hj
    have hforest : (G.induce S).IsAcyclic := hf S hsub (by omega)
    obtain ⟨T,hT,hTq⟩ := decomposition_path_family_tracked D hD hne
    have hS : {x | T.quota x=0 ∨ x=u ∨ x=v}=S := by
      ext x
      simp only [Set.mem_setOf_eq,S,Set.mem_insert_iff,Finset.mem_coe,inactive,Finset.mem_filter,
        Finset.mem_univ,true_and,hTq]
      tauto
    obtain ⟨E,hE,hEc,hEne,hEb⟩ := restore_normal_of_zero_forest h T hT
      (by rw [hTq,hqu]) (by rw [hTq,hqv]) (fun x ↦ (hTq x) ▸ hb x) (by rwa [hS])
    exact ⟨E,hE,hEc.trans hDc,hEne,hEb⟩

end Erdos583NormalForestRestorationDevelopment
