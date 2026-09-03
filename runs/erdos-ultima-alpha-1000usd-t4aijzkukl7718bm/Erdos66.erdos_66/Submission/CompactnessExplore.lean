import FormalConjecturesUtil

/-!
# A finite-approximation formulation of Erdős Problem 66

This file isolates the uniform finite construction that would suffice to prove
Erdős Problem 66. It does not provide that construction.
-/

namespace Erdos66Compactness
open Filter AdditiveCombinatorics
open scoped Topology

noncomputable def encodedRep (f : ℕ → Bool) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal n,
    (if f p.1 then (1 : ℝ) else 0) * (if f p.2 then (1 : ℝ) else 0)

lemma continuous_encodedRep (n : ℕ) : Continuous (fun f : ℕ → Bool ↦ encodedRep f n) := by
  have he (i : ℕ) : Continuous (fun f : ℕ → Bool ↦ if f i then (1 : ℝ) else 0) :=
    (continuous_of_discreteTopology (f := fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp
      (continuous_apply i)
  exact continuous_finset_sum _ (fun p _ ↦ (he p.1).mul (he p.2))

lemma encodedRep_eq_sumRep (f : ℕ → Bool) (n : ℕ) :
    encodedRep f n = (sumRep {i | f i = true} n : ℝ) := by
  classical
  simp [encodedRep, sumRep, sumConv, Set.indicatorOne, Set.indicator]

lemma encodedRep_decide (A : Set ℕ) (n : ℕ) :
    encodedRep (fun i ↦ @decide (i ∈ A) (Classical.propDecidable _)) n =
      (sumRep A n : ℝ) := by
  rw [encodedRep_eq_sumRep]
  simp

/-- Uniform feasibility of all finite collections of tail estimates yields a single set
satisfying all those estimates. The thresholds `N k` must be independent of the cutoff `L`. -/
lemma exists_of_finite_approximations (c : ℝ) (N : ℕ → ℕ)
    (h : ∀ L : ℕ, ∃ A : Set ℕ, ∀ k ≤ L, ∀ n ≤ L, N k ≤ n →
      |(sumRep A n : ℝ) / Real.log n - c| ≤ 1 / ((k : ℝ) + 1)) :
    ∃ A : Set ℕ, ∀ k n : ℕ, N k ≤ n →
      |(sumRep A n : ℝ) / Real.log n - c| ≤ 1 / ((k : ℝ) + 1) := by
  classical
  let C : ℕ → Set (ℕ → Bool) := fun L ↦ {f | ∀ k ≤ L, ∀ n ≤ L, N k ≤ n →
    |encodedRep f n / Real.log n - c| ≤ 1 / ((k : ℝ) + 1)}
  have hclosed (L : ℕ) : IsClosed (C L) := by
    dsimp only [C]
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro k
    apply isClosed_iInter
    intro hk
    apply isClosed_iInter
    intro n
    apply isClosed_iInter
    intro hn
    apply isClosed_iInter
    intro hkn
    exact isClosed_le (((continuous_encodedRep n).div_const _).sub continuous_const).abs
      continuous_const
  have hne (L : ℕ) : (C L).Nonempty := by
    obtain ⟨A, hA⟩ := h L
    refine ⟨fun i ↦ decide (i ∈ A), ?_⟩
    intro k hk n hn hkn
    rw [encodedRep_decide]
    exact hA k hk n hn hkn
  have hmono (L : ℕ) : C (L + 1) ⊆ C L := by
    intro f hf k hk n hn hkn
    exact hf k (by omega) n (by omega) hkn
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    hmono hne (hclosed 0).isCompact hclosed
  refine ⟨{i | f i = true}, fun k n hkn ↦ ?_⟩
  have hh := Set.mem_iInter.mp hf (max k n) k (le_max_left _ _) n (le_max_right _ _) hkn
  rwa [encodedRep_eq_sumRep] at hh

lemma tendsto_of_tail_estimates (A : Set ℕ) (c : ℝ) (N : ℕ → ℕ)
    (h : ∀ k n : ℕ, N k ≤ n →
      |(sumRep A n : ℝ) / Real.log n - c| ≤ 1 / ((k : ℝ) + 1)) :
    Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨N k, fun n hn ↦ ?_⟩
  rw [Real.dist_eq]
  exact (h k n hn).trans_lt hk

lemma finite_approximations_suffice (c : ℝ) (N : ℕ → ℕ)
    (h : ∀ L : ℕ, ∃ A : Set ℕ, ∀ k ≤ L, ∀ n ≤ L, N k ≤ n →
      |(sumRep A n : ℝ) / Real.log n - c| ≤ 1 / ((k : ℝ) + 1)) :
    ∃ A : Set ℕ, Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c) := by
  obtain ⟨A, hA⟩ := exists_of_finite_approximations c N h
  exact ⟨A, tendsto_of_tail_estimates A c N hA⟩

lemma sumRep_congr_below {A B : Set ℕ} {n : ℕ}
    (h : ∀ i ≤ n, i ∈ A ↔ i ∈ B) : sumRep A n = sumRep B n := by
  classical
  rw [sumRep_def, sumRep_def]
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hs := Finset.mem_antidiagonal.mp hp
  exact and_congr (h p.1 (by omega)) (h p.2 (by omega))

open scoped Classical in
lemma sumRep_truncate (A : Set ℕ) (L n : ℕ) (hn : n ≤ L) :
    sumRep (↑((Finset.range (L + 1)).filter (fun i ↦ i ∈ A)) : Set ℕ) n = sumRep A n := by
  apply sumRep_congr_below
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
  exact and_iff_right (by omega)

/-- This is an equivalent finite-construction problem, not an existence proof.
In particular, both `c` and the whole threshold function `N` must be chosen before `L`. -/
theorem conjecture_iff_finite_prefixes :
    (∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
    ∃ c : ℝ, c ≠ 0 ∧ ∃ N : ℕ → ℕ,
      ∀ L : ℕ, ∃ B : Finset ℕ, B ⊆ Finset.range (L + 1) ∧
        ∀ k ≤ L, ∀ n ≤ L, N k ≤ n →
          |(sumRep (B : Set ℕ) n : ℝ) / Real.log n - c| ≤ 1 / ((k : ℝ) + 1) := by
  classical
  constructor
  · rintro ⟨A, c, hc, hlim⟩
    have htail (k : ℕ) : ∃ M : ℕ, ∀ n ≥ M,
        |(sumRep A n : ℝ) / Real.log n - c| ≤ 1 / ((k : ℝ) + 1) := by
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hlim
        (1 / ((k : ℝ) + 1)) (by positivity)
      refine ⟨M, fun n hn ↦ ?_⟩
      simpa only [Real.dist_eq] using (hM n hn).le
    choose N hN using htail
    refine ⟨c, hc, N, fun L ↦ ?_⟩
    refine ⟨(Finset.range (L + 1)).filter (fun i ↦ i ∈ A), Finset.filter_subset _ _, ?_⟩
    intro k hk n hn hkn
    rw [sumRep_truncate A L n hn]
    exact hN k n hkn
  · rintro ⟨c, hc, N, h⟩
    have h' : ∀ L : ℕ, ∃ A : Set ℕ, ∀ k ≤ L, ∀ n ≤ L, N k ≤ n →
        |(sumRep A n : ℝ) / Real.log n - c| ≤ 1 / ((k : ℝ) + 1) := by
      intro L
      obtain ⟨B, hB, hgood⟩ := h L
      exact ⟨(B : Set ℕ), hgood⟩
    obtain ⟨A, hA⟩ := finite_approximations_suffice c N h'
    exact ⟨A, c, hc, hA⟩

end Erdos66Compactness
