import Submission.FiniteRepBernoulliExplore
import Submission.VariableBernoulliBoundsExplore
import Submission.SummableTailBudgetExplore
import Submission.SummableCostCompactnessExplore

/-! A generic finite-Bernoulli/compactness selection theorem for countably
many nonnegative continuous representation costs with summable means. -/
namespace Erdos66BernoulliCostSelection
open Filter AdditiveCombinatorics Erdos66FiniteRepBernoulli Erdos66FiniteBernoulli
  Erdos66VariableBernoulliBounds Erdos66SummableTailBudget Erdos66SummableCostCompactness
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma row_budget (L : ℕ) : (∑ j∈Finset.range (L+1), (1/2:ℝ)^j/4) ≤ 1/2 := by
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).div_const 4
  have hh := Summable.sum_le_tsum (Finset.range (L+1)) (fun j _ ↦ by positivity) hs
  rw [tsum_div_const,tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)] at hh
  norm_num at hh ⊢
  exact hh

/-- Each expected cost is bounded uniformly in the final cutoff. Summable
bounds yield one set with all countably many cost sequences summable. -/
theorem exists_summable_rep_costs (p : ℕ → ℝ) (hp : ∀ n, 0≤p n ∧ p n≤1)
    (cost : ℕ → ℕ → ℝ → ℝ) (g : ℕ → ℕ → ℝ)
    (hcont : ∀ j n, Continuous (cost j n)) (hpos : ∀ j n x, 0≤cost j n x)
    (hg : ∀ j, Summable (g j))
    (hbound : ∀ j, ∀ᶠ n : ℕ in atTop, ∀ L, n≤L →
      expect (fun i : Fin (L+1) ↦ p i.val)
        (fun ω ↦ cost j n (sumRep (selected L ω) n)) ≤ g j n) :
    ∃ A : Set ℕ, ∀ j, Summable (fun n ↦ cost j n (sumRep A n)) := by
  have hN (j : ℕ) : ∃ N : ℕ,
      (∀ n≥N, ∀ L, n≤L → expect (fun i : Fin (L+1) ↦ p i.val)
        (fun ω ↦ cost j n (sumRep (selected L ω) n)) ≤ g j n) ∧
      (∀ S : Finset ℕ, (∀ n∈S, N≤n) → (∑ n∈S, g j n)<(1/2:ℝ)^j/4) := by
    obtain ⟨N₁,h₁⟩ := eventually_atTop.mp (hbound j)
    obtain ⟨N₂,h₂⟩ := exists_tail_budget _ (hg j) ((1/2:ℝ)^j/4) (by positivity)
    refine ⟨max N₁ N₂,fun n hn L hL ↦ h₁ n ((le_max_left _ _).trans hn) L hL,
      fun S hS ↦ h₂ S (fun n hn ↦ (le_max_right _ _).trans (hS n hn))⟩
  choose N hNb hNs using hN
  let trim : ℕ → ℕ → ℝ → ℝ := fun j n x ↦ if N j≤n then cost j n x else 0
  have htpos (j n : ℕ) (x : ℝ) : 0≤trim j n x := by
    dsimp [trim]
    split_ifs
    · exact hpos j n x
    · exact le_rfl
  have htcont (j n : ℕ) : Continuous (trim j n) := by
    by_cases hn : N j≤n
    · simpa only [trim,if_pos hn] using hcont j n
    · simp only [trim,if_neg hn]
      exact continuous_const
  have hfinite (L : ℕ) : ∃ A : Set ℕ, ∀ j≤L, ∀ K≤L,
      (∑ n∈Finset.range K, trim j n (sumRep A n)) ≤ 1 := by
    let pL : Fin (L+1) → ℝ := fun i ↦ p i.val
    let P : (Fin (L+1) → Bool) → ℝ := fun ω ↦
      ∑ j∈Finset.range (L+1), ∑ n∈Finset.range (L+1), trim j n (sumRep (selected L ω) n)
    have hrow (j : ℕ) : expect pL (fun ω ↦ ∑ n∈Finset.range (L+1),
        trim j n (sumRep (selected L ω) n)) ≤ (1/2:ℝ)^j/4 := by
      rw [expect_sum]
      calc
        _ ≤ ∑ n∈Finset.range (L+1), if N j≤n then g j n else 0 := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases hnj : N j≤n
          · simp only [trim,if_pos hnj]
            exact hNb j n hnj L (by have := Finset.mem_range.mp hn; omega)
          · simp only [trim,if_neg hnj,expect_const]
            exact le_rfl
        _ = ∑ n∈(Finset.range (L+1)).filter (fun n ↦ N j≤n), g j n :=
          (Finset.sum_filter _ _).symm
        _ ≤ (1/2:ℝ)^j/4 := (hNs j _ (fun n hn ↦ (Finset.mem_filter.mp hn).2)).le
    have hP : expect pL P < 1 := by
      change expect pL (fun ω ↦ ∑ j∈Finset.range (L+1), _) < 1
      rw [expect_sum]
      exact ((Finset.sum_le_sum (fun j _ ↦ hrow j)).trans (row_budget L)).trans_lt (by norm_num)
    obtain ⟨ω,hw,hω⟩ := exists_positive_weight_lt pL (fun i ↦ hp i.val) P 1 hP
    refine ⟨selected L ω,fun j hj K hK ↦ ?_⟩
    have h₁ : (∑ n∈Finset.range K, trim j n (sumRep (selected L ω) n)) ≤
        ∑ n∈Finset.range (L+1), trim j n (sumRep (selected L ω) n) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun n _ _ ↦ htpos j n _)
    have h₂ : (∑ n∈Finset.range (L+1), trim j n (sumRep (selected L ω) n)) ≤ P ω :=
      Finset.single_le_sum (s := Finset.range (L+1)) (a := j)
        (f := fun k ↦ ∑ n∈Finset.range (L+1), trim k n (sumRep (selected L ω) n))
        (fun k _ ↦ Finset.sum_nonneg (fun n _ ↦ htpos k n _))
        (Finset.mem_range.mpr (by omega))
    exact (h₁.trans h₂).trans hω.le
  obtain ⟨A,hA⟩ := exists_summable_costs trim htcont htpos hfinite
  refine ⟨A,fun j ↦ (hA j).congr_cofinite ?_⟩
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (N j)] with n hn
  simp only [trim,if_pos hn]

end Erdos66BernoulliCostSelection
