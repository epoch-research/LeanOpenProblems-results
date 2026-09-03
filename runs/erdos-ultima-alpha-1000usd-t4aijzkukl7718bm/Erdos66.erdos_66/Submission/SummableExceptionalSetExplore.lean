import Submission.SummableTailBudgetExplore

/-! Diagonalizing countably many summable exceptional sets into one
summable exceptional set outside which a sequence converges. -/
namespace Erdos66SummableExceptionalSet
open Filter Erdos66SummableTailBudget
open scoped Classical Topology
set_option maxHeartbeats 1500000

lemma small_geometric_sum (S : Finset ℕ) : (∑ j∈S, (1/2:ℝ)^j/4) ≤ 1/2 := by
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).div_const 4
  have hh := Summable.sum_le_tsum S (fun j _ ↦ by positivity) hs
  rw [tsum_div_const,tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)] at hh
  norm_num at hh ⊢
  exact hh

/-- Summability of the bad set at every fixed tolerance gives a single
summable exceptional set. This theorem does not assert that the exception
set is finite. -/
theorem exists_exceptional_set (f : ℕ → ℝ) (c : ℝ) (w : ℕ → ℝ)
    (hw : ∀ n, 0≤w n)
    (h : ∀ ε : ℝ, 0<ε → Summable (fun n ↦ if ε≤|f n-c| then w n else 0)) :
    ∃ E : Set ℕ, Summable (fun n ↦ if n∈E then w n else 0) ∧
      Tendsto (fun n ↦ if n∈E then c else f n) atTop (𝓝 c) := by
  let δ : ℕ → ℝ := fun j ↦ 1/((j:ℝ)+1)
  let bad : ℕ → ℕ → ℝ := fun j n ↦ if δ j≤|f n-c| then w n else 0
  have hbpos (j n : ℕ) : 0≤bad j n := by dsimp [bad]; split_ifs; exact hw n; exact le_rfl
  have hN (j : ℕ) : ∃ N : ℕ, j≤N ∧ ∀ S : Finset ℕ,
      (∀ n∈S, N≤n) → (∑ n∈S, bad j n) < (1/2:ℝ)^j/4 := by
    obtain ⟨N,hN⟩ := exists_tail_budget (bad j) (h (δ j) (by dsimp [δ]; positivity))
      ((1/2:ℝ)^j/4) (by positivity)
    refine ⟨max j N,le_max_left _ _,fun S hS ↦ hN S (fun n hn ↦ ?_)⟩
    exact (le_max_right _ _).trans (hS n hn)
  choose N hNj hNsum using hN
  let E : Set ℕ := {n | ∃ j, N j≤n ∧ δ j≤|f n-c|}
  have hEsum : Summable (fun n ↦ if n∈E then w n else 0) := by
    apply summable_of_sum_le (c := (1/2:ℝ)) (fun n ↦ by dsimp only; split_ifs; exact hw n; exact le_rfl)
    intro S
    let J := Finset.range (S.sup id+1)
    have hp (n : ℕ) (hn : n∈S) : (if n∈E then w n else 0) ≤
        ∑ j∈J, if N j≤n then bad j n else 0 := by
      by_cases he : n∈E
      · rw [if_pos he]
        obtain ⟨j,hj,hbad⟩ := he
        have hjJ : j∈J := by
          have hh := Finset.le_sup (f := id) hn
          change n≤S.sup id at hh
          exact Finset.mem_range.mpr (by have := hNj j; omega)
        have hh := Finset.single_le_sum (s := J) (a := j)
          (f := fun k ↦ if N k≤n then bad k n else 0)
          (fun k _ ↦ by dsimp only; split_ifs; exact hbpos k n; exact le_rfl) hjJ
        simpa only [if_pos hj,bad,if_pos hbad] using hh
      · rw [if_neg he]
        exact Finset.sum_nonneg (fun j _ ↦ by split_ifs; exact hbpos j n; exact le_rfl)
    calc
      _ ≤ ∑ n∈S, ∑ j∈J, if N j≤n then bad j n else 0 := Finset.sum_le_sum hp
      _ = ∑ j∈J, ∑ n∈S, if N j≤n then bad j n else 0 := Finset.sum_comm
      _ ≤ ∑ j∈J, (1/2:ℝ)^j/4 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [←Finset.sum_filter]
        exact (hNsum j _ (fun n hn ↦ (Finset.mem_filter.mp hn).2)).le
      _ ≤ 1/2 := small_geometric_sum J
  refine ⟨E,hEsum,Metric.tendsto_atTop.mpr (fun ε hε ↦ ?_)⟩
  obtain ⟨j,hj⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hε).exists
  refine ⟨N j,fun n hn ↦ ?_⟩
  by_cases he : n∈E
  · simp only [if_pos he,dist_self]
    exact hε
  · rw [if_neg he,Real.dist_eq]
    have hh : |f n-c|<δ j := by
      by_contra hh
      exact he ⟨j,hn,le_of_not_gt hh⟩
    exact hh.trans hj

end Erdos66SummableExceptionalSet
