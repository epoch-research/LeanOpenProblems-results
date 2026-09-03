import Submission.RankGlobalMinimal

/-!
The original conjecture is equivalent to a uniform pure-cycle bound by
spanning-forest rank. No uniform constant or counterexample is established.
-/
open SimpleGraph Filter
open scoped Classical
namespace Erdos184
namespace RankReduction
open RankCritical RankComponents RankCriticalPartitions RankGlobalMinimal

universe u

theorem conjecture_iff_rank_bound :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℕ, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) → HasBound C G) := by
  rw [conjecture_iff_even_cycle_bound]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨N,hN⟩ := exists_nat_ge c
    refine ⟨2*N,?_⟩
    intro V _ G he
    apply bound_of_component_bounds
    intro k
    by_cases hn : 2 ≤ Fintype.card k
    · have hek : ∀ x, Even (k.toSimpleGraph.degree x) := by
        intro x
        have hx := he x.val
        have hd := component_degree G k x
        simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx hd ⊢
        rwa [hd]
      obtain ⟨D,hcy,hd,hb⟩ := hc k.toSimpleGraph hek
      have hr := connected_rank k.connected_toSimpleGraph
      have horder : Fintype.card k ≤ 2 * graphRank k.toSimpleGraph := by omega
      have hcard : (D.card : ℝ) ≤ ((2*N) * graphRank k.toSimpleGraph : ℕ) := by
        calc
          (D.card : ℝ) ≤ c * Fintype.card k := hb
          _ ≤ (N : ℝ) * Fintype.card k := mul_le_mul_of_nonneg_right hN (by positivity)
          _ ≤ (N : ℝ) * (2 * graphRank k.toSimpleGraph) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact_mod_cast horder
          _ = _ := by push_cast; ring
      exact ⟨D,hcy,hd,by exact_mod_cast hcard⟩
    · haveI : Subsingleton k := ⟨Fintype.card_le_one_iff.mp
        (show Fintype.card k ≤ 1 by omega)⟩
      have hbot : k.toSimpleGraph = ⊥ := by
        apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
        intro x y h
        exact h.ne (Subsingleton.elim _ _)
      rw [hbot]
      exact hasBound_bot _
  · rintro ⟨C,hC⟩
    refine ⟨C,?_⟩
    intro V _ _ G he
    obtain ⟨D,hc,hd,hb⟩ := hC G he
    exact ⟨D,hc,hd,by exact_mod_cast hb.trans (Nat.mul_le_mul_left C (rank_le_card G))⟩

/-- The exclusion premise remains the missing theorem. Connectedness and
both forms of minimality in it are supplied by the verified extraction. -/
lemma conjecture_of_no_connected_critical (C : ℕ)
    (hno : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      ¬(RankGlobalMinimal.IsLexMinimal C G ∧ RankCritical.IsCritical C G ∧ G.Connected)) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_rank_bound.mpr
  refine ⟨C,?_⟩
  intro V _ G he
  by_contra hb
  obtain ⟨W,instW,H,hH⟩ := exists_connected_critical C G he hb
  letI := instW
  exact hno H hH

/-- A weaker structural target than bounded positive degree: a bounded
packing may separate a nontrivial cut without isolating any vertex. The
separating-packing hypothesis remains unproved. -/
lemma conjecture_of_connected_small_separating_packing (C : ℕ)
    (hsep : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), G.Connected → G ≠ ⊥ →
      (∀ v, Even (G.degree v)) → MinimalCounterexample.AllCyclesOptimal G →
      ∃ P : Finset G.Subgraph,
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
        P.card ≤ C ∧ ¬(G \ unionPieces G P).Preconnected) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_of_no_connected_critical C
  intro V _ G ⟨_,hcrit,hconn⟩
  obtain ⟨P,hc,hd,hb,hn⟩ := hsep G hconn hcrit.ne_bot hcrit.1 hcrit.allCyclesOptimal
  apply hn
  intro u v
  exact (hcrit.small_packing_reachable P hc hd hb u v).mpr (hconn.preconnected u v)

end RankReduction
end Erdos184
