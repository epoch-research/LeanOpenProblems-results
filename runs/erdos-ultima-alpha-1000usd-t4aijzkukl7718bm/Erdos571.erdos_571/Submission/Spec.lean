import FormalConjecturesUtil

/-!
# Erdős Problem 571

*References:*
- [erdosproblems.com/571](https://www.erdosproblems.com/571)
-/

open Filter SimpleGraph Finset

universe u v

namespace Erdos571

private theorem star_free_iff {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ) :
    (completeBipartiteGraph (Fin 1) (Fin k)).Free H ↔ ∀ v, H.degree v < k := by
  classical
  constructor
  · intro hf v
    by_contra hv
    have hk : k ≤ (H.neighborFinset v).card := by simpa only [card_neighborFinset_eq_degree] using (Nat.le_of_not_gt hv)
    obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq hk
    apply hf
    apply completeBipartiteGraph_isContained_iff.mpr
    refine ⟨{v}, s, by simp, by simpa using hsc, ?_⟩
    intro x hx y hy
    have hxv : x = v := by simpa using hx
    subst x
    exact (H.mem_neighborFinset _ _).mp (hs hy)
  · intro hd hc
    obtain ⟨l, r, hl, hr, h⟩ := completeBipartiteGraph_isContained_iff.mp hc
    have hl' : l.card = 1 := by simpa using hl
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hl'
    have hsub : r ⊆ H.neighborFinset v := by
      intro w hw
      apply (H.mem_neighborFinset _ _).mpr
      apply h
      · simp [hv]
      · exact hw
    have hcard := Finset.card_le_card hsub
    have hr' : r.card = k := by simpa using hr
    have := hd v
    simp only [hr', card_neighborFinset_eq_degree] at hcard
    omega

private theorem extremal_star_three (n : ℕ) (hn : 3 ≤ n) :
    extremalNumber n (completeBipartiteGraph (Fin 1) (Fin 3)) = n := by
  classical
  apply Nat.le_antisymm
  · rw [← Fintype.card_fin n, extremalNumber_le_iff]
    intro H _ hH
    have hd := (star_free_iff H 3).mp hH
    have hsum : ∑ v, H.degree v ≤ ∑ _v : Fin n, 2 := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.le_of_lt_succ (hd v)
    rw [H.sum_degrees_eq_twice_card_edges] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    simp only [Fintype.card_fin]
    omega
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hd : ∀ v, (cycleGraph (m + 3)).degree v = 2 := by
      intro v
      exact cycleGraph_degree_three_le
    have hf : (completeBipartiteGraph (Fin 1) (Fin 3)).Free (cycleGraph (m + 3)) := by
      apply (star_free_iff _ _).mpr
      intro v
      rw [hd]
      omega
    have hc : (cycleGraph (m + 3)).edgeFinset.card = m + 3 := by
      have hsum := (cycleGraph (m + 3)).sum_degrees_eq_twice_card_edges
      simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
      omega
    simpa only [Fintype.card_fin, hc] using card_edgeFinset_le_extremalNumber hf


/-- The endpoint of the rational-exponent assertion, witnessed by the claw. -/
theorem endpoint_one :
    ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
      Asymptotics.IsTheta atTop
        (fun n : ℕ => (extremalNumber n G : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ((1 : ℚ) : ℝ)) := by
  let S := completeBipartiteGraph (Fin 1) (Fin 3)
  let e : (Fin 1 ⊕ Fin 3) ≃ Fin 4 := finSumFinEquiv
  refine ⟨4, S.map e.toEmbedding, ?_, ?_⟩
  · have hS : S.IsBipartite := by
      have h := (CompleteBipartiteGraph.bicoloring (Fin 1) (Fin 3)).colorable
      simpa only [Fintype.card_bool] using h
    exact hS.map e.toEmbedding
  · apply Filter.EventuallyEq.isTheta
    filter_upwards [eventually_ge_atTop 3] with n hn
    rw [← extremalNumber_congr_right (SimpleGraph.Iso.map e S)]
    simp only [S, extremal_star_three n hn, Rat.cast_one, Real.rpow_one]

/--
Show that for any rational $\alpha \in [1,2)$ there exists a bipartite graph $G$ such that\[\mathrm{ex}(n;G)\asymp n^{\alpha}.\]
-/
theorem erdos_571 :
    ∀ α : ℚ, 1 ≤ α → α < 2 →
      ∃ q : ℕ, ∃ G : SimpleGraph (Fin q), G.IsBipartite ∧
        Asymptotics.IsTheta atTop
          (fun n : ℕ => (extremalNumber n G : ℝ))
          (fun n : ℕ => (n : ℝ) ^ (α : ℝ)) := by
  intro α hα hα2
  by_cases h₁ : α = 1
  · subst α
    exact endpoint_one
  -- A matching upper-bound construction for every rational exponent is missing.
  sorry

end Erdos571
