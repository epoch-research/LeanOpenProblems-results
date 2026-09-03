import Submission.MatchingSmoothing

/-!
A legitimate one-vertex reduction for an independent neighborhood.
The smaller-graph bound is an explicit hypothesis, not a consequence of
edge-minimality among spanning subgraphs.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace VertexSmoothing
open MatchingSmoothing

variable {V : Type*}

/-- Pair any finite even set, without making a claim about its ambient edges. -/
lemma exists_matching_support [Fintype V] (S : Set V) (he : Even S.ncard) :
    ∃ M : SimpleGraph V, IsMatching M ∧ M.support = S := by
  obtain ⟨r,hr⟩ := he
  let U := S.toFinset
  have hu : U.card = r + r := by simpa only [U,Set.ncard_eq_toFinset_card'] using hr
  obtain ⟨T,hTU,hT⟩ := Finset.exists_subset_card_eq (s := U) (n := r) (by omega)
  have hdiff : (U \ T).card = r := by rw [Finset.card_sdiff_of_subset hTU,hT,hu]; omega
  let f : (T : Set V) ≃ ((U \ T : Finset V) : Set V) :=
    Fintype.equivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Set.ncard_coe_finset]
        using hT.trans hdiff.symm)
  have hdis : Disjoint (T : Set V) ((U \ T : Finset V) : Set V) := by
    rw [Finset.coe_sdiff]
    exact Set.disjoint_sdiff_right
  have hadj : ∀ v : (T : Set V), (⊤ : SimpleGraph V).Adj v (f v) := by
    intro v
    exact hdis.ne_of_mem v.property (f v).property
  obtain ⟨M,hverts,hm⟩ :=
    Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hdis f hadj
  refine ⟨M.spanningCoe,?_,?_⟩
  · intro u v w huv huw
    exact hm.eq_of_adj_left huv huw
  · change M.support = S
    rw [hm.support_eq_verts,hverts]
    rw [← Finset.coe_union,Finset.union_sdiff_of_subset hTU]
    exact Set.coe_toFinset S

/-- The numerical bound using the full ambient vertex count. -/
def HasCardBound [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ D.card ≤ C * Fintype.card V

lemma transport_iso {W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {K : SimpleGraph W} (f : G ≃g K)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    ∃ E : Finset K.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition K E ∧ E.card ≤ D.card := by
  have hi : Set.InjOn (Sym2.map f) G.edgeSet := (Sym2.map.injective f.injective).injOn
  have hs : Set.SurjOn (Sym2.map f) G.edgeSet K.edgeSet := by
    intro e he
    obtain ⟨d,hd⟩ := f.mapEdgeSet.surjective ⟨e,he⟩
    exact ⟨d.val,d.property,congrArg Subtype.val hd⟩
  obtain ⟨E,hcE,hdE,hbE⟩ := project_decomposition_degree_two f.toHom hi hs ∅
    (f.injective.injOn) (by simp) D hc hd
  exact ⟨E,hcE,hdE,by simpa using hbE⟩

lemma HasCardBound.of_iso {W : Type*} [Fintype V] [Fintype W]
    {C : ℕ} {G : SimpleGraph V} {K : SimpleGraph W} (f : G ≃g K)
    (hb : HasCardBound C G) : HasCardBound C K := by
  obtain ⟨D,hc,hd,hbD⟩ := hb
  obtain ⟨E,hcE,hdE,hbE⟩ := transport_iso f D hc hd
  exact ⟨E,hcE,hdE,hbE.trans (by simpa only [f.card_eq] using hbD)⟩

abbrev Without (v : V) := {w : V // w ≠ v}

def neighborsWithout (G : SimpleGraph V) (v : V) : Set (Without v) :=
  {w | G.Adj v w.val}

lemma neighborsWithout_card [Fintype V] (G : SimpleGraph V) (v : V) :
    (neighborsWithout G v).ncard = G.degree v := by
  let e : (neighborsWithout G v) ≃ G.neighborSet v := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    invFun := fun x => ⟨⟨x.val,x.property.ne.symm⟩,x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have h := Nat.card_congr e
  simpa only [Nat.card_coe_set_eq,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using h

noncomputable def apexIso (G : SimpleGraph V) (v : V)
    (M : SimpleGraph (Without v)) (hM : M.support = neighborsWithout G v) :
    apex (G.induce {w | w ≠ v}) M ≃g G where
  toEquiv := Equiv.optionSubtypeNe v
  map_rel_iff' := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none => simp [apex]
      | some y => change G.Adj v y.val ↔ y ∈ M.support; rw [hM]; rfl
    | some x =>
      cases y with
      | none =>
        change G.Adj x.val v ↔ x ∈ M.support
        rw [hM]
        exact G.adj_comm _ _
      | some y => rfl

set_option maxHeartbeats 800000 in
/-- A vertex of positive even degree at most 2(C+1), whose neighbors are
independent, is reducible for a C-times-order bound. The induction hypothesis
ranges over all even graphs on the smaller vertex type. -/
lemma independent_neighborhood_reduction [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ u, Even (G.degree u)) (v : V) (hv : 0 < G.degree v)
    (hdeg : G.degree v ≤ 2 * (C+1))
    (hind : ∀ u w, G.Adj v u → G.Adj v w → ¬G.Adj u w)
    (hsmall : ∀ H : SimpleGraph (Without v),
      (∀ u, Even (H.degree u)) → HasCardBound C H) : HasCardBound C G := by
  let A := G.induce {w | w ≠ v}
  obtain ⟨M,hm,hM⟩ := exists_matching_support (neighborsWithout G v)
    (by rw [neighborsWithout_card]; exact he v)
  have ham : Disjoint A.edgeSet M.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heA heM
    induction e using Sym2.ind with
    | h u w =>
      have hu : u ∈ neighborsWithout G v := hM ▸ (show u ∈ M.support from ⟨w,heM⟩)
      have hw : w ∈ neighborsWithout G v := hM ▸ (show w ∈ M.support from ⟨u,heM.symm⟩)
      exact hind u.val w.val hu hw heA
  let f : apex A M ≃g G := apexIso G v M hM
  have hap : ∀ x, Even ((apex A M).degree x) := by
    intro x
    have hd := f.degree_eq x
    have hx := he (f x)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hx ⊢
    rwa [← hd]
  have heAM := (even_apex_iff A M hm ham).mp (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hap x)
  obtain ⟨D,hcD,hdD,hbD⟩ := hsmall (A ⊔ M) (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heAM x)
  have hr : 2 * M.edgeSet.ncard = G.degree v := by
    rw [← hm.support_card,hM,neighborsWithout_card]
  have hne : M ≠ ⊥ := by
    intro h
    simp only [h,edgeSet_bot,Set.ncard_empty,Nat.mul_zero] at hr
    omega
  have hrbound : M.edgeSet.ncard ≤ C + 1 := by
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hr hdeg
    omega
  obtain ⟨E,hcE,hdE,hbE⟩ := bound_apex_of_small_matching C A M hm ham hne
    hrbound D (by
      intro H hH
      refine ⟨(hcD H hH).1,?_⟩
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hcD H hH).2 x) hdD hbD
  apply HasCardBound.of_iso f
  refine ⟨E,?_,hdE,hbE⟩
  intro H hH
  refine ⟨(hcE H hH).1,?_⟩
  intro x
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 x

end VertexSmoothing
end Erdos184
