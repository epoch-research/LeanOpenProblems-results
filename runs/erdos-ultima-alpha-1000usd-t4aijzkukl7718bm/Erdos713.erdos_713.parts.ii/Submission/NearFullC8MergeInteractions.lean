import FormalConjecturesUtil
import Submission.NearFullMergeWitnesses
import Submission.C8TwoMergers

/-! Simultaneous degree control, few safe mergers, and sparse genuine
interactions on near-full C8-free hosts. No cheap common blocker is asserted. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713NearFullC8MergeInteractions
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713CloneResistance
open Erdos713MergeDegreePenalty Erdos713NearFullMergeWitnesses Erdos713C8TwoMergers
set_option maxHeartbeats 1000000

lemma eventual_interactions_real_cap {β D σ : ℝ} (hβ : β < 1/4) (hσ : 0 < σ) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (∀ v, degreeR G v ≤ D*(n : ℝ)^β) →
      ((genuineRoots G).card : ℝ) ≤ σ*(n : ℝ)^4 := by
  filter_upwards [eventually_genuine_sparse (C := D) hβ hσ,eventually_gt_atTop (0 : ℕ)]
    with n hn hnp
  intro G hD
  letI : Nonempty (Fin n) := ⟨⟨0,hnp⟩⟩
  obtain ⟨v,hv⟩ := G.exists_maximal_degree_vertex
  have hc : (G.maxDegree : ℝ) ≤ D*(n : ℝ)^β := by
    rw [hv]
    have hh := hD v
    simpa only [degreeR,Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hh
  exact hn G G.maxDegree G.degree_le_maxDegree hc

lemma cycle_eight_bipartite : (cycleGraph 8).IsBipartite := by
  refine ⟨Coloring.mk (fun z => (⟨z.val % 2,Nat.mod_lt _ (by decide)⟩ : Fin 2)) ?_⟩
  intro u v
  simp only [cycleGraph_adj]
  fin_cases u <;> fin_cases v <;> decide

/-- The degree cap and global potential comparisons now refer to the same
host. Sparse interaction applies only to pairs of INDIVIDUALLY SAFE mergers;
most pairs are instead obstructed, and no blocker is constructed here. -/
theorem joint {α c : ℝ} (ha : 1 < α) (ha2 : α < 5/4) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ ∀ ε ρ : ℝ, 0 < ε → 0 < ρ →
      ∃ D : ℝ, 0 < D ∧ ∀ σ : ℝ, 0 < σ → ∀ L : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
        L ≤ n ∧ (cycleGraph 8).Free G ∧ (c-ε)*(n : ℝ)^α ≤ edgesR G ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ degreeR G v ∧ degreeR G v ≤ D*(n : ℝ)^(α-1)) ∧
        ((safePairs (cycleGraph 8) G).card : ℝ) ≤ ρ*(n : ℝ)^2 ∧
        ((genuineRoots G).card : ℝ) ≤ σ*(n : ℝ)^4 ∧
        ∃ lam mu : ℝ, 0 < lam ∧ 0 < mu ∧ GlobalOptimal (cycleGraph 8) G lam mu ∧
          κ*(n : ℝ)^α ≤ netBudget G lam mu := by
  have hEdge : ∃ v w, (cycleGraph 8).Adj v w := ⟨0,1,by decide⟩
  obtain ⟨a,κ,ha',hκ,hs⟩ := near_full_few_safe_mergers (cycleGraph 8)
    cycle_eight_bipartite hEdge ha (by linarith : α < 2) hc h
  refine ⟨a,κ,ha',hκ,?_⟩
  intro ε ρ hε hρ
  obtain ⟨D,hD,hD'⟩ := hs ε ρ hε hρ
  refine ⟨D,hD,?_⟩
  intro σ hσ L
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (eventual_interactions_real_cap (D := D) (by linarith : α-1 < 1/4) hσ)
  obtain ⟨n,G,hn,hFree,hDense,hDeg,hSafe,hGlob⟩ := hD' (max L K)
  have hnL : L ≤ n := (le_max_left _ _).trans hn
  have hnK : K ≤ n := (le_max_right _ _).trans hn
  exact ⟨n,G,hnL,hFree,hDense,hDeg,hSafe,hK n hnK G (fun v => (hDeg v).2),hGlob⟩

#print axioms eventual_interactions_real_cap
#print axioms joint
end Erdos713NearFullC8MergeInteractions
