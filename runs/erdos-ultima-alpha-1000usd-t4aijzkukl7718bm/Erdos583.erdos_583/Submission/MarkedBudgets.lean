import Submission.Work

/-! Sharp one-even-vertex partitions and justified marked endpoint budgets.
These are special cases, not an assertion of endpoint flexibility for every
connected graph. -/
open SimpleGraph Erdos583Work
open Erdos583Work.PendantCompletion Erdos583Work.EndpointSelection
open Erdos583Work.BridgeGlue Erdos583Work.VertexCritical
namespace Erdos583MarkedBudgetsDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

lemma normal_odd_endpoint_eq_one {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D)
    (hb : ∀ x, endpointMultiplicity D x ≤ 2) {v : V}
    (hv : Odd (Nat.card (G.neighborSet v))) : endpointMultiplicity D v=1 := by
  have hv' : Odd (G.degree v) := by
    simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hv
  have he := (hD.odd_endpointMultiplicity_iff v).mpr hv'
  rw [Nat.odd_iff] at he
  have := hb v
  omega

lemma one_even_path_partition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (v : V) (hv : Even (Nat.card (G.neighborSet v)))
    (hodd : ∀ x, x ≠ v → Odd (Nat.card (G.neighborSet x))) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      (∀ K ∈ D, K.edgeSet.Nonempty) ∧
      (∀ x, endpointMultiplicity D x=if x=v then 0 else 1) ∧
      2*D.card+1=Fintype.card V := by
  classical
  obtain ⟨D,hD,hne,hb,hvD⟩ := exists_normal_inactive_at G v hv
  have hmult (x : V) : endpointMultiplicity D x=if x=v then 0 else 1 := by
    by_cases hx : x=v
    · simpa only [hx,if_pos rfl] using hvD
    · simpa only [if_neg hx] using normal_odd_endpoint_eq_one hD hb (hodd x hx)
  have hI : inactive D={v} := by
    ext x
    simp only [inactive,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,hmult]
    split_ifs <;> simp_all
  have hE : (Finset.univ.filter fun x ↦ Even (G.degree x))={v} := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    by_cases hx : x=v
    · subst x
      have hv' : Even (G.degree v) := by simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hv
      simp [hv']
    · have hnot : ¬Even (G.degree x) := by
        simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using Nat.not_even_iff_odd.mpr (hodd x hx)
      simp [hx,hnot]
  have hc := normal_count hD hne hb
  rw [hI,hE,Finset.card_singleton] at hc
  exact ⟨D,hD,hne,hmult,by omega⟩

lemma marked_of_positive_endpoint {V : Type*} [Fintype V] {G : SimpleGraph V}
    {D : Finset G.Subgraph} (hD : GoodDecomposition G D) {u : V}
    (hu : 0 < endpointMultiplicity D u) :
    ∃ a, ∃ p : G.Walk u a, p.IsPath ∧ p.toSubgraph ∈ D := by
  obtain ⟨K,hK⟩ := Finset.card_pos.mp hu
  obtain ⟨hKD,hdeg⟩ := Finset.mem_filter.mp hK
  obtain ⟨a,p,hp,hKp⟩ := path_endpoint_of_neighbor_ncard_one (hD.1 K hKD) hdeg
  exact ⟨a,p,hp,hKp ▸ hKD⟩

lemma few_even_marked {V : Type*} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.Connected) (u : V)
    (hfew : (Finset.univ.filter fun v ↦ Even (G.degree v)).card ≤ 3) :
    ∃ D : Finset G.Subgraph, ∃ a, ∃ p : G.Walk u a,
      GoodDecomposition G D ∧ p.IsPath ∧ p.toSubgraph ∈ D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  by_cases hu : Odd (G.degree u)
  · obtain ⟨D,hD,hDc⟩ := gallai_of_at_most_three_even G hfew
    have hp : 0 < endpointMultiplicity D u := ((hD.odd_endpointMultiplicity_iff u).mpr hu).pos
    obtain ⟨a,p,hp,hpD⟩ := marked_of_positive_endpoint hD hp
    exact ⟨D,a,p,hD,hp,hpD,hDc⟩
  · have hue : Even (Nat.card (G.neighborSet u)) := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using Nat.not_odd_iff_even.mp hu
    by_cases hex : ∃ v, v ≠ u ∧ Even (Nat.card (G.neighborSet v))
    · obtain ⟨v,hvu,hv⟩ := hex
      obtain ⟨D,hD,hne,hb,hI⟩ := feasible_singleton hG v hv
      have hpos : 0 < endpointMultiplicity D u := by
        by_contra hn
        have hz : endpointMultiplicity D u=0 := by omega
        have hm : u ∈ inactive D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
        rw [hI,Finset.mem_singleton] at hm
        exact hvu hm.symm
      obtain ⟨a,p,hp,hpD⟩ := marked_of_positive_endpoint hD hpos
      have hc := normal_count hD hne hb
      rw [hI,Finset.card_singleton] at hc
      exact ⟨D,a,p,hD,hp,hpD,by rw [ceil_half]; omega⟩
    · obtain ⟨D,hD,hne,hb,_⟩ := exists_normal_inactive_at G u hue
      obtain ⟨E,hE,hEne,hEb,hEI,_⟩ := realize_subset
        (fun x ↦ hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ x)
        hD hne hb ∅ (Finset.empty_subset _)
      have hpos : 0 < endpointMultiplicity E u := by
        by_contra hn
        have hz : endpointMultiplicity E u=0 := by omega
        have hm : u ∈ inactive E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
        simp [hEI] at hm
      obtain ⟨a,p,hp,hpE⟩ := marked_of_positive_endpoint hE hpos
      have hcard : (Finset.univ.filter fun v ↦ Even (G.degree v)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro x hx y hy
        have heq (z : V) (hz : Even (G.degree z)) : z=u := by
          by_contra hzu
          exact hex ⟨z,hzu,by simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hz⟩
        exact (heq x (Finset.mem_filter.mp hx).2).trans (heq y (Finset.mem_filter.mp hy).2).symm
      have hc := normal_count hE hEne hEb
      rw [hEI,Finset.card_empty] at hc
      exact ⟨E,a,p,hE,hp,hpE,by rw [ceil_half]; omega⟩


lemma forest_marked {V : Type*} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) (hG : G.Connected) (hf : G.IsAcyclic) (u : V) :
    ∃ D : Finset G.Subgraph, ∃ a, ∃ p : G.Walk u a,
      GoodDecomposition G D ∧ p.IsPath ∧ p.toSubgraph ∈ D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  classical
  obtain ⟨D,hD,hne,hmult,hDc⟩ := forest_normal_decomposition G hf
  by_cases hu : Odd (G.degree u)
  · obtain ⟨a,p,hp,hpD⟩ := marked_of_positive_endpoint hD (by rw [hmult,if_pos hu]; decide)
    have hc := Fintype.card_subtype_le (fun x ↦ Odd (G.degree x))
    exact ⟨D,a,p,hD,hp,hpD,by rw [ceil_half]; omega⟩
  · have hlt : Fintype.card {x : V // Odd (G.degree x)} < Fintype.card V :=
      Fintype.card_subtype_lt (p := fun x : V ↦ Odd (G.degree x)) hu
    obtain ⟨E,hE,_,hEc,huE,_,_⟩ := activate_vertex hD hne
      (show u ∈ G.support from hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ u)
      (by rw [hmult,if_neg hu])
    obtain ⟨a,p,hp,hpE⟩ := marked_of_positive_endpoint hE (by rw [huE]; decide)
    exact ⟨E,a,p,hE,hp,hpE,by rw [ceil_half]; omega⟩

lemma map_decomposition_tracked {V W : Type*} {H : SimpleGraph V}
    {G : SimpleGraph W} (f : H →g G) (hf : Function.Injective f)
    (hc : G.edgeSet=Sym2.map f '' H.edgeSet)
    {D : Finset H.Subgraph} (hD : GoodDecomposition H D) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧ E.card ≤ D.card ∧
      ∀ K ∈ D, K.map f ∈ E := by
  classical
  let E := D.image (Subgraph.map f)
  refine ⟨E,⟨?_,?_,?_⟩,Finset.card_image_le,fun K hK ↦ Finset.mem_image.mpr ⟨K,hK,rfl⟩⟩
  · intro L hL
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨a,b,p,hp,rfl⟩ := hD.1 K hK
    exact ⟨f a,f b,p.map f,Walk.map_isPath_of_injective hf hp,by simp⟩
  · intro L hL M hM hLM
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hM
    change Disjoint (K.map f).edgeSet (J.map f).edgeSet
    rw [Subgraph.edgeSet_map,Subgraph.edgeSet_map,Set.disjoint_image_iff (Sym2.map.injective hf)]
    exact hD.2.1 hK hJ (fun h ↦ hLM (congrArg (Subgraph.map f) h))
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨K,_,he⟩
      exact K.edgeSet_subset he
    · intro he
      rw [hc] at he
      obtain ⟨e,he,rfl⟩ := he
      rw [←hD.2.2] at he
      simp only [Set.mem_iUnion] at he
      obtain ⟨K,hK,heK⟩ := he
      refine ⟨K.map f,Finset.mem_image.mpr ⟨K,hK,rfl⟩,?_⟩
      rw [Subgraph.edgeSet_map]
      exact ⟨e,heK,rfl⟩

lemma lift_induce_marked {V : Type*} {G : SimpleGraph V} (S : Set V)
    {D : Finset (G.induce S).Subgraph} (hD : GoodDecomposition (G.induce S) D)
    {u a : S} (p : (G.induce S).Walk u a) (hp : p.IsPath) (hpD : p.toSubgraph ∈ D) :
    ∃ E : Finset (within G S).Subgraph, ∃ q : (within G S).Walk u.val a.val,
      GoodDecomposition (within G S) E ∧ q.IsPath ∧ q.toSubgraph ∈ E ∧ E.card ≤ D.card := by
  let f : G.induce S →g within G S :=
    { toFun := Subtype.val, map_rel' := fun {x y} h ↦ ⟨h,x.property,y.property⟩ }
  have hc : (within G S).edgeSet=Sym2.map f '' (G.induce S).edgeSet := by
    apply Set.Subset.antisymm
    · intro e he
      induction e using Sym2.ind with
      | h x y => exact ⟨s(⟨x,he.2.1⟩,⟨y,he.2.2⟩),he.1,rfl⟩
    · rintro e ⟨a,ha,rfl⟩
      exact f.map_mem_edgeSet ha
  obtain ⟨E,hE,hEc,hparts⟩ := map_decomposition_tracked f Subtype.val_injective hc hD
  exact ⟨E,p.map f,hE,Walk.map_isPath_of_injective Subtype.val_injective hp,
    by simpa using hparts p.toSubgraph hpD,hEc⟩

lemma endpoint_of_path_rep {V : Type*} [Fintype V] {G : SimpleGraph V} {a b u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (q : G.Walk a b) (hq : q.IsTrail)
    (he : q.toSubgraph=p.toSubgraph) : u=a ∨ u=b := by
  by_cases hn : p.Nil
  · cases hn
    have ha := q.start_mem_support
    rw [←Walk.mem_verts_toSubgraph,he,Walk.mem_verts_toSubgraph] at ha
    exact Or.inl (show a=u from by simpa using ha).symm
  · have hodd : Odd (q.toSubgraph.neighborSet u).ncard := by
      rw [he,hp.neighborSet_toSubgraph_startpoint hn,Set.ncard_singleton]
      exact odd_one
    exact ((trail_neighbor_ncard_odd_iff hq u).mp hodd).2

lemma append_marked_to_isolated {V : Type*} [Fintype V] {A B : SimpleGraph V}
    {u v a : V} (hAB : A ≤ B) (h : B.Adj u v) (hiso : ∀ x, ¬A.Adj u x)
    (hcover : B.edgeSet=insert s(u,v) A.edgeSet)
    (D : Finset A.Subgraph) (hD : GoodDecomposition A D)
    (p : A.Walk v a) (hp : p.IsPath) (hpD : p.toSubgraph ∈ D) :
    ∃ E : Finset B.Subgraph, GoodDecomposition B E ∧ E.card ≤ D.card := by
  obtain ⟨T,hT,hparts⟩ := EdgeDefect.decomposition_path_family D hD
  obtain ⟨i,hi⟩ := hparts p.toSubgraph hpD
  have hvi := endpoint_of_path_rep p hp (T.walk i) (T.isTrail i) hi
  have hu : u ∉ (T.walk i).support := by
    intro hm
    obtain ⟨ha,hb⟩ := DegreeThreeReduction.isolated_mem_support hiso (T.walk i) hm
    rcases hvi with he|he
    · exact h.ne (he.trans ha).symm
    · exact h.ne (he.trans hb).symm
  obtain ⟨U,_,_,hU,_⟩ := DeletionEndpoint.append_new_edge_tracked hAB T hT i hvi h
    (fun hh ↦ hiso v hh) hcover
  exact MatchingAppend.path_family_partition U (hU hu)

lemma extend_marked_bridge_side {V : Type*} [Fintype V] {G : SimpleGraph V}
    (S : Set V) {u v : V} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v)
    {D : Finset (G.induce S).Subgraph} (hD : GoodDecomposition (G.induce S) D)
    {a : S} (p : (G.induce S).Walk ⟨u,hu⟩ a) (hp : p.IsPath) (hpD : p.toSubgraph ∈ D) :
    ∃ E : Finset (within G (insert v S)).Subgraph,
      GoodDecomposition (within G (insert v S)) E ∧ E.card ≤ D.card := by
  obtain ⟨D',q,hD',hq,hqD,hDc⟩ := lift_induce_marked S hD p hp hpD
  obtain ⟨E,hE,hEc⟩ := append_marked_to_isolated
    (show within G S ≤ within G (insert v S) from fun _ _ hx ↦
      ⟨hx.1,Or.inr hx.2.1,Or.inr hx.2.2⟩)
    (show (within G (insert v S)).Adj v u from ⟨h.symm,Or.inl rfl,Or.inr hu⟩)
    (fun _ hx ↦ hv hx.2.1) (BridgeParityReduction.augment_bridge_side_cover S h hu hv hcross) D' hD' q hq hqD
  exact ⟨E,hE,hEc.trans hDc⟩


lemma gallai_of_marked_bridge_side {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) (S : Set (Fin n))
    {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) (hS : 2 ≤ S.ncard)
    {D : Finset (G.induce S).Subgraph} (hD : GoodDecomposition (G.induce S) D)
    {a : S} (p : (G.induce S).Walk ⟨u,hu⟩ a) (hp : p.IsPath) (hpD : p.toSubgraph ∈ D)
    (hDc : D.card ≤ ⌈(S.ncard : ℚ)/2⌉₊) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  have hsum : S.ncard+Sᶜ.ncard=n := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using S.ncard_add_ncard_compl
  have hcross' : ∀ x ∈ Sᶜ, ∀ y ∉ Sᶜ, G.Adj x y → x=v ∧ y=u := by
    intro x hx y hy hxy
    have hyS : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
    exact (hcross y hyS x hx hxy.symm).symm
  obtain ⟨D',hD',hD'c⟩ := extend_marked_bridge_side S h hu hv hcross hD p hp hpD
  have hconnT := cut_side_connected hG Sᶜ h.symm hv (not_not.mpr hu) hcross'
  have hsizeT : (insert u Sᶜ).ncard=Sᶜ.ncard+1 := Set.ncard_insert_of_notMem (not_not.mpr hu)
  obtain ⟨E,hE,hEc⟩ := hsmall.on_induce G (insert u Sᶜ) (by rw [hsizeT]; omega) hconnT
  obtain ⟨E',hE',hE'c⟩ := lift_induce_within (insert u Sᶜ) E hE
  obtain ⟨F,hF,hFc⟩ := BridgeParityReduction.glue_spanning_cut_sides S h hu hv hcross D' E' hD' hE'
  rw [ceil_half] at hDc
  rw [hsizeT,ceil_half] at hEc
  exact ⟨F,hF,by simp only [Fintype.card_fin,ceil_half]; omega⟩

lemma failure_cut_side_many_even {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) (hS : 2 ≤ S.ncard) :
    4 ≤ (Finset.univ.filter fun x : S ↦ Even ((G.induce S).degree x)).card := by
  classical
  by_contra hn
  have hcard : Fintype.card S=S.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  letI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hconn := CutVertexReduction.single_boundary_connected hG S u hu
    (fun x hx y hy hxy ↦ (hcross x hx y hy hxy).1)
  obtain ⟨D,a,p,hD,hp,hpD,hDc⟩ := few_even_marked (G.induce S) hconn ⟨u,hu⟩ (by omega)
  exact hfail (gallai_of_marked_bridge_side hsmall hG S h hu hv hcross hS hD p hp hpD
    (by simpa only [hcard] using hDc))

lemma failure_cut_side_not_acyclic {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (S : Set (Fin n)) {u v : Fin n} (h : G.Adj u v) (hu : u ∈ S) (hv : v ∉ S)
    (hcross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) (hS : 2 ≤ S.ncard) :
    ¬(G.induce S).IsAcyclic := by
  classical
  intro hf
  have hcard : Fintype.card S=S.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  letI : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hconn := CutVertexReduction.single_boundary_connected hG S u hu
    (fun x hx y hy hxy ↦ (hcross x hx y hy hxy).1)
  obtain ⟨D,a,p,hD,hp,hpD,hDc⟩ := forest_marked (G.induce S) hconn hf ⟨u,hu⟩
  exact hfail (gallai_of_marked_bridge_side hsmall hG S h hu hv hcross hS hD p hp hpD
    (by simpa only [hcard] using hDc))

lemma failure_bridge_side_structure {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    {u v : Fin n} (hb : G.IsBridge s(u,v)) :
    ∃ S : Set (Fin n), u ∈ S ∧ v ∉ S ∧
      (∀ x ∈ S, ∀ y ∉ S, G.Adj x y → x=u ∧ y=v) ∧
      (∀ T, (T=S ∨ T=Sᶜ) → 2 ≤ T.ncard →
        4 ≤ (Finset.univ.filter fun x : T ↦ Even ((G.induce T).degree x)).card ∧
          ¬(G.induce T).IsAcyclic) := by
  classical
  have h := (isBridge_iff.mp hb).1
  obtain ⟨S,hu,hv,hcross⟩ := bridge_cut hb
  refine ⟨S,hu,hv,hcross,?_⟩
  intro T hT hsize
  rcases hT with hT|hT
  · subst T
    exact ⟨failure_cut_side_many_even hsmall hG hfail S h hu hv hcross hsize,
      failure_cut_side_not_acyclic hsmall hG hfail S h hu hv hcross hsize⟩
  · subst T
    have hcross' : ∀ x ∈ Sᶜ, ∀ y ∉ Sᶜ, G.Adj x y → x=v ∧ y=u := by
      intro x hx y hy hxy
      have hyS : y ∈ S := by simpa only [Set.mem_compl_iff,not_not] using hy
      exact (hcross y hyS x hx hxy.symm).symm
    exact ⟨failure_cut_side_many_even hsmall hG hfail Sᶜ h.symm hv (not_not.mpr hu) hcross' hsize,
      failure_cut_side_not_acyclic hsmall hG hfail Sᶜ h.symm hv (not_not.mpr hu) hcross' hsize⟩

end Erdos583MarkedBudgetsDevelopment
