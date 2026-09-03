import FormalConjecturesUtil

/-!
# Counting-function constraints for Erdős Problem 66

These necessary conditions do not prove or disprove the conjecture.
-/

namespace Erdos66Counting
open Filter AdditiveCombinatorics
open scoped Topology

noncomputable def cutoff (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun a ↦ a ∈ A)

noncomputable def count (A : Set ℕ) (N : ℕ) : ℕ := (cutoff A N).card

lemma mem_cutoff {A : Set ℕ} {N a : ℕ} : a ∈ cutoff A N ↔ a < N ∧ a ∈ A := by
  classical
  simp [cutoff]

lemma sumRep_le_succ (A : Set ℕ) (n : ℕ) : sumRep A n ≤ n + 1 := by
  classical
  rw [sumRep_def, ← Finset.Nat.card_antidiagonal n]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma sumRep_eq_fiber_card (A : Set ℕ) (N n : ℕ) (hn : n < N) :
    sumRep A n = (((cutoff A N).product (cutoff A N)).filter
      (fun p : ℕ × ℕ ↦ p.1 + p.2 = n)).card := by
  classical
  rw [sumRep_def]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.product_eq_sprod, Finset.mem_product, mem_cutoff]
  constructor
  · rintro ⟨hs, hA, hB⟩
    exact ⟨⟨⟨by omega, hA⟩, ⟨by omega, hB⟩⟩, hs⟩
  · rintro ⟨⟨⟨ha, hA⟩, ⟨hb, hB⟩⟩, hs⟩
    exact ⟨hs, hA, hB⟩

lemma cumulative_le_count_sq (A : Set ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range N, sumRep A n ≤ count A N ^ 2 := by
  classical
  calc
    ∑ n ∈ Finset.range N, sumRep A n =
        ∑ n ∈ Finset.range N, (((cutoff A N).product (cutoff A N)).filter
          (fun p : ℕ × ℕ ↦ p.1 + p.2 = n)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      exact sumRep_eq_fiber_card A N n (Finset.mem_range.mp hn)
    _ = (((cutoff A N).product (cutoff A N)).filter
        (fun p : ℕ × ℕ ↦ p.1 + p.2 ∈ Finset.range N)).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ ((cutoff A N).product (cutoff A N)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = count A N ^ 2 := by simp [count, pow_two]

lemma count_sq_le_cumulative (A : Set ℕ) (N : ℕ) :
    count A N ^ 2 ≤ ∑ n ∈ Finset.range (2 * N), sumRep A n := by
  classical
  have hm : Set.MapsTo (fun p : ℕ × ℕ ↦ p.1 + p.2)
      (↑((cutoff A N).product (cutoff A N)) : Set (ℕ × ℕ))
      (↑(Finset.range (2 * N)) : Set ℕ) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.product_eq_sprod, Finset.mem_product, mem_cutoff] at hp
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  calc
    count A N ^ 2 = ((cutoff A N).product (cutoff A N)).card := by
      simp [count, pow_two]
    _ = ∑ n ∈ Finset.range (2 * N), (((cutoff A N).product (cutoff A N)).filter
        (fun p : ℕ × ℕ ↦ p.1 + p.2 = n)).card := Finset.card_eq_sum_card_fiberwise hm
    _ ≤ ∑ n ∈ Finset.range (2 * N), sumRep A n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [sumRep_def]
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, mem_cutoff] at hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal]
      exact ⟨hp.2, hp.1.1.2, hp.1.2.2⟩

lemma global_log_upper_bound {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 < C ∧ ∀ n : ℕ,
      (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2) := by
  have hC : c < |c| + 1 := by linarith [le_abs_self c]
  obtain ⟨M, hM⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds hC))
  let C : ℝ := |c| + 1
  let K : ℝ := max M 2 + 1
  have hCp : 0 < C := by dsimp [C]; positivity
  have hKp : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, C, hKp, hCp, fun n ↦ ?_⟩
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  by_cases hn : max M 2 ≤ n
  · have hn2 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hlp : 0 < Real.log (n : ℝ) := Real.log_pos hn2
    have hb : (sumRep A n : ℝ) ≤ C * Real.log n :=
      (div_le_iff₀ hlp).mp (hM n (by omega)).le
    have hl : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith [mul_le_mul_of_nonneg_left hl hCp.le]
  · have hb : (sumRep A n : ℝ) ≤ K := by
      have ht := sumRep_le_succ A n
      dsimp [K]
      exact_mod_cast (show sumRep A n ≤ max M 2 + 1 by omega)
    linarith [mul_nonneg hCp.le hlog]

lemma count_sq_log_upper {A : Set ℕ} {K C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, (sumRep A n : ℝ) ≤ K + C * Real.log ((n : ℝ) + 2)) (N : ℕ) :
    (count A N : ℝ) ^ 2 ≤ 2 * (N : ℝ) * (K + C * Real.log (2 * (N : ℝ) + 2)) := by
  have hcount : (count A N : ℝ) ^ 2 ≤ ∑ n ∈ Finset.range (2 * N), (sumRep A n : ℝ) := by
    exact_mod_cast count_sq_le_cumulative A N
  calc
    (count A N : ℝ) ^ 2 ≤ ∑ n ∈ Finset.range (2 * N), (sumRep A n : ℝ) := hcount
    _ ≤ ∑ n ∈ Finset.range (2 * N), (K + C * Real.log (2 * (N : ℝ) + 2)) := by
      apply Finset.sum_le_sum
      intro n hn
      apply (h n).trans
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.log_le_log (by positivity)
      have hn' : n < 2 * N := Finset.mem_range.mp hn
      exact_mod_cast (show n + 2 ≤ 2 * N + 2 by omega)
    _ = _ := by simp [Nat.cast_mul, mul_assoc]; ring

lemma count_sq_log_lower {A : Set ℕ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∃ M : ℕ, ∀ N ≥ M,
      (N : ℝ) * (c / 2) * Real.log N ≤ (count A (2 * N) : ℝ) ^ 2 := by
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    (h.eventually (lt_mem_nhds (show c / 2 < c by linarith)))
  refine ⟨max L 2, fun N hN ↦ ?_⟩
  have hNl : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hb (n : ℕ) (hn : n ∈ Finset.Ico N (2 * N)) :
      (c / 2) * Real.log N ≤ (sumRep A n : ℝ) := by
    obtain ⟨hnl, hnu⟩ := Finset.mem_Ico.mp hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hnl
    have hlogp : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hh := (le_div_iff₀ hlogp).mp (hL n (by omega)).le
    exact (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) hn') (by positivity)).trans hh
  have hs : ∑ n ∈ Finset.Ico N (2 * N), sumRep A n ≤ count A (2 * N) ^ 2 := by
    apply le_trans (Finset.sum_le_sum_of_subset ?_) (cumulative_le_count_sq A (2 * N))
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  calc
    (N : ℝ) * (c / 2) * Real.log N =
        ∑ _n ∈ Finset.Ico N (2 * N), (c / 2) * Real.log N := by
      simp [show 2 * N - N = N by omega, mul_assoc]
    _ ≤ ∑ n ∈ Finset.Ico N (2 * N), (sumRep A n : ℝ) := Finset.sum_le_sum hb
    _ ≤ (count A (2 * N) : ℝ) ^ 2 := by exact_mod_cast hs

lemma log_two_mul_add_two_div_nat_limit :
    Tendsto (fun n : ℕ ↦ Real.log (2 * (n : ℝ) + 2) / n) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      tendsto_natCast_atTop_atTop
  have hh := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-1) 1
    (by norm_num)).comp hg
  apply hh.congr'
  filter_upwards [] with n
  dsimp
  congr 1 <;> ring

lemma count_div_nat_limit_zero {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count A N : ℝ) / N) atTop (𝓝 0) := by
  obtain ⟨K, C, hK, hC, hbound⟩ := global_log_upper_bound h
  have hupper := count_sq_log_upper hC.le hbound
  have hboundlim : Tendsto (fun N : ℕ ↦
      2 * (K / N + C * (Real.log (2 * (N : ℝ) + 2) / N))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_const_div_atTop_nhds_zero_nat K).add
        (log_two_mul_add_two_div_nat_limit.const_mul C)).const_mul 2
  have hsq : Tendsto (fun N : ℕ ↦ ((count A N : ℝ) / N) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ sq_nonneg _)) ?_ hboundlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    calc
      ((count A N : ℝ) / N) ^ 2 = (count A N : ℝ) ^ 2 / (N : ℝ) ^ 2 := div_pow _ _ _
      _ ≤ (2 * (N : ℝ) * (K + C * Real.log (2 * (N : ℝ) + 2))) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (hupper N) (sq_nonneg _)
      _ = 2 * (K / N + C * (Real.log (2 * (N : ℝ) + 2) / N)) := by
        field_simp
  have hh := hsq.sqrt
  rw [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [] with N
  exact Real.sqrt_sq (by positivity)

lemma hasDensity_zero_of_finite_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    A.HasDensity 0 := by
  have he (N : ℕ) : (↑(cutoff A N) : Set ℕ) = A ∩ Set.Iio N := by
    ext i
    simp [mem_cutoff, and_comm]
  have hf : (fun N ↦ A.partialDensity Set.univ N) = fun N ↦ (count A N : ℝ) / N := by
    funext N
    simp only [Set.partialDensity, Set.inter_univ]
    rw [← he, Set.ncard_coe_finset]
    simp [count]
  change Tendsto (fun N ↦ A.partialDensity Set.univ N) atTop (𝓝 0)
  rw [hf]
  exact count_div_nat_limit_zero h

end Erdos66Counting
