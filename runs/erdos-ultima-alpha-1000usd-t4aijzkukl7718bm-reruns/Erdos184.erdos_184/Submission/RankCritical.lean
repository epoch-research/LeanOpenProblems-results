import Submission.CriticalSmoothingBudget

/-!
Criticality for a spanning-forest-rank charge. A small cycle packing in a
critical graph cannot disconnect any pair of previously connected vertices.
This is a necessary condition only, not a settlement of Erdos 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace RankCritical

variable {V : Type*} [Fintype V]

noncomputable def graphRank (G : SimpleGraph V) : ℕ :=
  Fintype.card V - Nat.card G.ConnectedComponent

omit [Fintype V] in
lemma component_mk_surjective (G : SimpleGraph V) : Function.Surjective G.connectedComponentMk := by
  intro c
  induction c using ConnectedComponent.ind with
  | _ v => exact ⟨v,rfl⟩

lemma component_card_le (G : SimpleGraph V) : Nat.card G.ConnectedComponent ≤ Fintype.card V := by
  simpa only [Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_surjective G.connectedComponentMk (component_mk_surjective G)

lemma rank_mono {A G : SimpleGraph V} (h : A ≤ G) : graphRank A ≤ graphRank G := by
  have hc := ConnectedComponent.card_le_card_of_le h
  unfold graphRank
  omega

lemma rank_le_card (G : SimpleGraph V) : graphRank G ≤ Fintype.card V := Nat.sub_le _ _

lemma rank_bot : graphRank (⊥ : SimpleGraph V) = 0 := by
  have hi : Function.Injective (⊥ : SimpleGraph V).connectedComponentMk := by
    intro u v h
    exact SimpleGraph.reachable_bot.mp (ConnectedComponent.exact h)
  have hc := Fintype.card_congr (Equiv.ofBijective (⊥ : SimpleGraph V).connectedComponentMk
    ⟨hi,component_mk_surjective _⟩)
  simp only [graphRank,Nat.card_eq_fintype_card,← hc,Nat.sub_self]

lemma reachable_iff_of_rank_eq {A G : SimpleGraph V} (h : A ≤ G)
    (hr : graphRank A = graphRank G) (u v : V) : A.Reachable u v ↔ G.Reachable u v := by
  have ha := component_card_le A
  have hg := component_card_le G
  have hcard : Nat.card A.ConnectedComponent = Nat.card G.ConnectedComponent := by
    unfold graphRank at hr
    omega
  let f := ConnectedComponent.map (SimpleGraph.Hom.ofLE h)
  have hi : Function.Injective f :=
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨ConnectedComponent.surjective_map_ofLE h,
      by simpa only [Nat.card_eq_fintype_card] using hcard⟩).1
  refine ⟨fun h => h.mono ‹A ≤ G›,?_⟩
  intro huv
  apply ConnectedComponent.exact
  apply hi
  simpa only [f,ConnectedComponent.map_mk,Hom.ofLE_apply] using ConnectedComponent.sound huv

/-- The order-minus-components charge is the rank of any spanning forest. -/
def HasBound (C : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ D.card ≤ C * graphRank G

lemma hasBound_bot (C : ℕ) : HasBound C (⊥ : SimpleGraph V) :=
  ⟨∅,by simp,by simp [IsDecomposition],by simp⟩

def IsCritical (C : ℕ) (G : SimpleGraph V) : Prop :=
  (∀ v, Even (G.degree v)) ∧ ¬HasBound C G ∧
  ∀ H : SimpleGraph V, H ≤ G → H.edgeSet.ncard < G.edgeSet.ncard →
    (∀ v, Even (H.degree v)) → HasBound C H

lemma exists_critical_subgraph (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasBound C G) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsCritical C H := by
  let P (n : ℕ) := ∃ H : SimpleGraph V, H ≤ G ∧
    (∀ v, Even (H.degree v)) ∧ ¬HasBound C H ∧ H.edgeSet.ncard = n
  have hex : ∃ n, P n := ⟨_,G,le_rfl,he,hb,rfl⟩
  obtain ⟨H,hHG,heH,hbH,hnH⟩ := Nat.find_spec hex
  refine ⟨H,hHG,heH,hbH,?_⟩
  intro K hKH hlt heK
  by_contra hbK
  have hmin := Nat.find_min' hex
    (show P K.edgeSet.ncard from ⟨K,hKH.trans hHG,heK,hbK,rfl⟩)
  omega

lemma IsCritical.ne_bot {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G) : G ≠ ⊥ := by
  intro h
  exact hG.2.1 (h ▸ hasBound_bot C)

lemma IsCritical.packing_cost {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (P : Finset G.Subgraph) (hp : P.Nonempty)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet)) :
    C * graphRank G < P.card + C * graphRank (G \ unionPieces G P) := by
  have heR := even_residual_of_cycle_packing G hG.1 P hc hd
  obtain ⟨F,hcF,hdF,hbF⟩ := hG.2.2 (G \ unionPieces G P) sdiff_le
    (MinimalCounterexample.residual_edge_card_lt G P hp hc) (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heR v)
  obtain ⟨D,hcD,hdD,hbD⟩ := complete_cycle_packing G P hc hd F (by
    intro H hH
    refine ⟨(hcF H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcF H hH).2 v) hdF
  have hbad : C * graphRank G < D.card := by
    by_contra! h
    exact hG.2.1 ⟨D,hcD,hdD,h⟩
  omega

lemma IsCritical.small_packing_rank_eq {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hb : P.card ≤ C) : graphRank (G \ unionPieces G P) = graphRank G := by
  by_cases hp : P.Nonempty
  · have hh := hG.packing_cost P hp hc hd
    have hle := rank_mono (show G \ unionPieces G P ≤ G from sdiff_le)
    apply Nat.le_antisymm hle
    by_contra hn
    have hmul := Nat.mul_le_mul_left C
      (show graphRank (G \ unionPieces G P) + 1 ≤ graphRank G by omega)
    rw [Nat.mul_add,Nat.mul_one] at hmul
    omega
  · have hp0 := Finset.not_nonempty_iff_eq_empty.mp hp
    simp [hp0,unionPieces]

lemma IsCritical.small_packing_reachable {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hb : P.card ≤ C) (u v : V) :
    (G \ unionPieces G P).Reachable u v ↔ G.Reachable u v :=
  reachable_iff_of_rank_eq sdiff_le (hG.small_packing_rank_eq P hc hd hb) u v

lemma IsCritical.delete_cycle_reachable {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) (hC : 0 < C)
    (H : G.Subgraph) (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (u v : V) :
    (G \ H.spanningCoe).Reachable u v ↔ G.Reachable u v := by
  have hh := hG.small_packing_reachable {H}
    (by intro K hK; obtain rfl := Finset.mem_singleton.mp hK; exact hcH)
    (by simp) (by simpa using hC) u v
  simpa only [unionPieces,Finset.sup_singleton] using hh

lemma IsCritical.extend_cycle {C : ℕ} {G : SimpleGraph V} (hG : IsCritical C G)
    (H : G.Subgraph) (hcH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ D : Finset G.Subgraph,
      (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ D.card = C * graphRank G + 1 := by
  let P : Finset G.Subgraph := {H}
  have hc : ∀ K ∈ P, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by
    intro K hK
    have : K = H := Finset.mem_singleton.mp hK
    subst K
    exact hcH
  have hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) := by
    simp [P]
  have heR := even_residual_of_cycle_packing G hG.1 P hc hd
  obtain ⟨F, hcF, hdF, hbF⟩ := hG.2.2 (G \ unionPieces G P) sdiff_le
    (MinimalCounterexample.residual_edge_card_lt G P (Finset.singleton_nonempty _) hc) (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
        using heR w)
  obtain ⟨D, hcD, hdD, hPD, hbD⟩ := complete_cycle_packing_extension G P hc hd F (by
    intro H hH
    refine ⟨(hcF H hH).1, ?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcF H hH).2 w) hdF
  have hbad : C * graphRank G < D.card := by
    by_contra! h
    exact hG.2.1 ⟨D, hcD, hdD, h⟩
  have hsupport := Nat.mul_le_mul_left C
    (rank_mono (show G \ unionPieces G P ≤ G from sdiff_le))
  have hP : P.card = 1 := Finset.card_singleton _
  exact ⟨D, hcD, hdD, hPD (Finset.mem_singleton_self H), by omega⟩


lemma IsCritical.allCyclesOptimal {C : ℕ} {G : SimpleGraph V}
    (hG : IsCritical C G) : MinimalCounterexample.AllCyclesOptimal G := by
  intro H hcH
  obtain ⟨D,hcD,hdD,hHD,hcard⟩ := hG.extend_cycle H hcH
  refine ⟨D,hcD,hdD,hHD,?_⟩
  intro E hcE hdE
  have hbad : C * graphRank G < E.card := by
    by_contra! h
    exact hG.2.1 ⟨E,hcE,hdE,h⟩
  omega

universe u
/-- This is a conditional reduction, not a proof that rank-critical graphs
are absent. The rank is at most the number of vertices. -/
lemma conjecture_of_no_critical (C : ℕ)
    (hno : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), ¬IsCritical C G) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨C,?_⟩
  intro V _ _ G he
  have hb : HasBound C G := by
    by_contra h
    obtain ⟨H,_,hH⟩ := exists_critical_subgraph C G he h
    exact hno H hH
  obtain ⟨D,hc,hd,hbD⟩ := hb
  refine ⟨D,hc,hd,?_⟩
  exact_mod_cast hbD.trans (Nat.mul_le_mul_left C (rank_le_card G))

/-- A uniformly small separating cycle packing in every all-optimal graph
would suffice. This hypothesis is not established here. -/
lemma conjecture_of_small_separating_packing (C : ℕ)
    (hsep : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), G ≠ ⊥ →
      (∀ v, Even (G.degree v)) → MinimalCounterexample.AllCyclesOptimal G →
      ∃ P : Finset G.Subgraph,
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
        P.card ≤ C ∧ ∃ u v, G.Reachable u v ∧ ¬(G \ unionPieces G P).Reachable u v) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_of_no_critical C
  intro V _ G hG
  obtain ⟨P,hc,hd,hb,u,v,huv,hn⟩ := hsep G hG.ne_bot hG.1 hG.allCyclesOptimal
  exact hn ((hG.small_packing_reachable P hc hd hb u v).mpr huv)

end RankCritical
end Erdos184
