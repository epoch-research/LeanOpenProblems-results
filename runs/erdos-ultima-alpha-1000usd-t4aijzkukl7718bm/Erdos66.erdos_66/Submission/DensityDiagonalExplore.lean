import Submission.ParityDensityExplore

/-! Statistical convergence can be realized as convergence outside one
natural-density-zero set. This does not make the exceptional set summable. -/
namespace Erdos66DensityDiagonal
open Erdos66Counting Erdos66SquarePrefixDensity
open scoped Classical Topology
open Filter
set_option maxHeartbeats 2400000

lemma count_mono (E F : Set ℕ) (hEF : E⊆F) (N : ℕ) : count E N ≤ count F N := by
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnN,hnE⟩ := mem_cutoff.mp hn
  exact mem_cutoff.mpr ⟨hnN,hEF hnE⟩

lemma count_truncated_zero (E : Set ℕ) (M N : ℕ) (hN : N≤M) :
    count {n | M≤n ∧ n∈E} N=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hnN,hnM,hnE⟩ := mem_cutoff.mp hn
  omega

lemma density_union_of_summable_bounds (E : ℕ → Set ℕ) (b : ℕ → ℝ)
    (hb : Summable b)
    (hbound : ∀ j N, (count (E j) N : ℝ)/N ≤ b j)
    (hlim : ∀ j, Tendsto (fun N : ℕ ↦ (count (E j) N : ℝ)/N) atTop (𝓝 0))
    (hindex : ∀ j n, n∈E j → j≤n) :
    Tendsto (fun N : ℕ ↦ (count (⋃ j, E j) N : ℝ)/N) atTop (𝓝 0) := by
  have hs (N : ℕ) : Summable (fun j ↦ (count (E j) N : ℝ)/N) := by
    apply hb.of_norm_bounded
    intro j
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (count (E j) N : ℝ)/N)]
      using hbound j N
  have ht : Tendsto (fun N : ℕ ↦ ∑' j, (count (E j) N : ℝ)/N) atTop (𝓝 0) := by
    have hh := tendsto_tsum_of_dominated_convergence hb hlim
      (Eventually.of_forall (fun N j ↦ show ‖(count (E j) N : ℝ)/N‖ ≤ b j from by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (count (E j) N : ℝ)/N)]
          using hbound j N))
    simpa only [tsum_zero] using hh
  apply squeeze_zero' _ _ ht
  · exact Eventually.of_forall (fun N ↦ by positivity)
  · apply Eventually.of_forall
    intro N
    have hsub : cutoff (⋃ j, E j) N ⊆ (Finset.range N).biUnion (fun j ↦ cutoff (E j) N) := by
      intro n hn
      obtain ⟨hnN,hnE⟩ := mem_cutoff.mp hn
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hnE
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (lt_of_le_of_lt (hindex j n hj) hnN),
        mem_cutoff.mpr ⟨hnN,hj⟩⟩
    have hcount := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hcR : (count (⋃ j, E j) N : ℝ) ≤ ∑ j∈Finset.range N, (count (E j) N : ℝ) := by
      exact_mod_cast hcount
    calc
      _ ≤ (∑ j∈Finset.range N, (count (E j) N : ℝ))/N :=
        div_le_div_of_nonneg_right hcR (Nat.cast_nonneg N)
      _ = ∑ j∈Finset.range N, (count (E j) N : ℝ)/N := Finset.sum_div ..
      _ ≤ _ := (hs N).sum_le_tsum _ (fun j _ ↦ by positivity)

/-- A single density-zero exceptional set for a statistically convergent
sequence in any pseudometric space. No rate or weighted summability is asserted. -/
theorem exists_density_zero_exception {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X) (c : X)
    (h : ∀ ε : ℝ, 0<ε → Tendsto
      (fun N : ℕ ↦ (count {n | ε ≤ dist (f n) c} N : ℝ)/N) atTop (𝓝 0)) :
    ∃ E : Set ℕ, Tendsto (fun N : ℕ ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then c else f n) atTop (𝓝 c) := by
  let B : ℕ → Set ℕ := fun j ↦ {n | 1/((j : ℝ)+1) ≤ dist (f n) c}
  let b : ℕ → ℝ := fun j ↦ (1/2 : ℝ)^j
  have hb0 (j : ℕ) : 0<b j := pow_pos (by norm_num) _
  have hB (j : ℕ) : Tendsto (fun N : ℕ ↦ (count (B j) N : ℝ)/N) atTop (𝓝 0) := h _ (by positivity)
  have hM (j : ℕ) : ∃ M : ℕ, ∀ N≥M, (count (B j) N : ℝ)/N < b j :=
    eventually_atTop.mp ((hB j).eventually_lt_const (hb0 j))
  choose M hM using hM
  let L : ℕ → ℕ := fun j ↦ max (j+1) (M j)
  let T : ℕ → Set ℕ := fun j ↦ {n | L j≤n ∧ n∈B j}
  have hsub (j : ℕ) : T j⊆B j := fun n hn ↦ hn.2
  have hTbound (j N : ℕ) : (count (T j) N : ℝ)/N ≤ b j := by
    by_cases hN : N≤L j
    · rw [show count (T j) N=0 from count_truncated_zero (B j) (L j) N hN,Nat.cast_zero,zero_div]
      exact (hb0 j).le
    · have hNM : M j≤N := (le_max_right _ _).trans (le_of_lt (lt_of_not_ge hN))
      have hm := hM j N hNM
      have hcR : (count (T j) N : ℝ) ≤ (count (B j) N : ℝ) := by exact_mod_cast count_mono _ _ (hsub j) N
      exact (div_le_div_of_nonneg_right hcR (Nat.cast_nonneg N)).trans hm.le
  have hTlim (j : ℕ) : Tendsto (fun N : ℕ ↦ (count (T j) N : ℝ)/N) atTop (𝓝 0) :=
    density_zero_of_eventual_subset (B j) (T j) (hB j) (Eventually.of_forall (fun n hn ↦ hsub j hn))
  let E : Set ℕ := ⋃ j, T j
  have hE : Tendsto (fun N : ℕ ↦ (count E N : ℝ)/N) atTop (𝓝 0) := by
    apply density_union_of_summable_bounds T b (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      hTbound hTlim
    intro j n hn
    exact (Nat.le_succ j).trans ((le_max_left _ _).trans hn.1)
  refine ⟨E,hE,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨j,hj⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (L j)] with n hn
  by_cases he : n∈E
  · simp only [if_pos he,dist_self]
    exact hε
  · rw [if_neg he]
    have hbad : n∉B j := by
      intro hb
      exact he (Set.mem_iUnion.mpr ⟨j,hn,hb⟩)
    exact (lt_of_not_ge hbad).trans hj

end Erdos66DensityDiagonal
