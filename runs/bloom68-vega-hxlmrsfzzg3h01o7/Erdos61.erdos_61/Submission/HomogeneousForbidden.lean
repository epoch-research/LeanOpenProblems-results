import Submission.CriticalBlocker

/-!
# Erdős–Hajnal for homogeneous forbidden graphs

These special cases use the verified cardinal Ramsey bound. They do not use
`Submission.Spec` and do not assert the general Erdős–Hajnal conjecture.
-/

open SimpleGraph

namespace Auxiliary.HomogeneousForbidden

/-- Excluding the complete graph bounds the clique number. -/
theorem cliqueNum_lt_of_top_free {α V : Type*} [Fintype α] [Fintype V]
    (G : SimpleGraph V)
    (hfree : ¬ ∃ g : α ↪ V, (⊤ : SimpleGraph α) = G.comap g) :
    G.cliqueNum < Fintype.card α := by
  classical
  have hf : G.CliqueFree (Fintype.card α) := by
    by_contra hn
    let e : (⊤ : SimpleGraph α) ↪g G :=
      (SimpleGraph.Iso.completeGraph (Fintype.equivFin α)).toEmbedding.trans
        (G.topEmbeddingOfNotCliqueFree hn)
    apply hfree
    refine ⟨e.toEmbedding, ?_⟩
    ext x y
    exact e.map_adj_iff.symm
  by_contra! hn
  obtain ⟨S, hS⟩ := G.exists_isNClique_cliqueNum
  exact (hf.mono hn) S hS

/-- A coefficient-one integral product bound for complete forbidden graphs. -/
theorem top_free_product_bound {α V : Type*} [Fintype α] [Fintype V]
    (G : SimpleGraph V)
    (hfree : ¬ ∃ g : α ↪ V, (⊤ : SimpleGraph α) = G.comap g) :
    Fintype.card V ≤ (G.indepNum * G.cliqueNum) ^ (Fintype.card α + 1) := by
  classical
  have hW := cliqueNum_lt_of_top_free G hfree
  by_contra! hn
  have h := CriticalBlocker.exponent_lt_parameters_of_counterexample G hn
  omega

/-- The precise lower-bound predicate for every finite complete forbidden graph. -/
theorem erdosHajnal_top {α : Type*} [Fintype α] [DecidableEq α] :
    ∃ c > (0 : ℝ), Auxiliary.IsErdosHajnalLowerBound (⊤ : SimpleGraph α)
      (fun n : ℕ => (n : ℝ) ^ c) := by
  apply IntegerReduction.erdosHajnal_of_exists_all_orders_nat_product_bound
  refine ⟨Fintype.card α + 1, Nat.succ_pos _, ?_⟩
  intro n G hfree
  simpa only [Fintype.card_fin] using top_free_product_bound G hfree

/-- Edgeless exclusion becomes complete-graph exclusion in the complement. -/
theorem top_free_compl_of_bot_free {α V : Type*} (G : SimpleGraph V)
    (hfree : ¬ ∃ g : α ↪ V, (⊥ : SimpleGraph α) = G.comap g) :
    ¬ ∃ g : α ↪ V, (⊤ : SimpleGraph α) = Gᶜ.comap g := by
  rintro ⟨g, hg⟩
  apply hfree
  refine ⟨g, ?_⟩
  ext x y
  by_cases heq : x = y
  · subst y
    simp
  · have ht : Gᶜ.Adj (g x) (g y) := by
      change (Gᶜ.comap g).Adj x y
      rw [← hg]
      exact heq
    simp only [bot_adj, comap_adj, false_iff]
    exact (SimpleGraph.compl_adj.mp ht).2

/-- The complementary coefficient-one product bound. -/
theorem bot_free_product_bound {α V : Type*} [Fintype α] [Fintype V]
    (G : SimpleGraph V)
    (hfree : ¬ ∃ g : α ↪ V, (⊥ : SimpleGraph α) = G.comap g) :
    Fintype.card V ≤ (G.indepNum * G.cliqueNum) ^ (Fintype.card α + 1) := by
  simpa only [indepNum_compl, cliqueNum_compl, Nat.mul_comm] using
    top_free_product_bound Gᶜ (top_free_compl_of_bot_free G hfree)

/-- The precise lower-bound predicate for every finite edgeless forbidden graph. -/
theorem erdosHajnal_bot {α : Type*} [Fintype α] [DecidableEq α] :
    ∃ c > (0 : ℝ), Auxiliary.IsErdosHajnalLowerBound (⊥ : SimpleGraph α)
      (fun n : ℕ => (n : ℝ) ^ c) := by
  apply IntegerReduction.erdosHajnal_of_exists_all_orders_nat_product_bound
  refine ⟨Fintype.card α + 1, Nat.succ_pos _, ?_⟩
  intro n G hfree
  simpa only [Fintype.card_fin] using bot_free_product_bound G hfree

end Auxiliary.HomogeneousForbidden

#print axioms Auxiliary.HomogeneousForbidden.cliqueNum_lt_of_top_free
#print axioms Auxiliary.HomogeneousForbidden.top_free_product_bound
#print axioms Auxiliary.HomogeneousForbidden.erdosHajnal_top
#print axioms Auxiliary.HomogeneousForbidden.top_free_compl_of_bot_free
#print axioms Auxiliary.HomogeneousForbidden.bot_free_product_bound
#print axioms Auxiliary.HomogeneousForbidden.erdosHajnal_bot
