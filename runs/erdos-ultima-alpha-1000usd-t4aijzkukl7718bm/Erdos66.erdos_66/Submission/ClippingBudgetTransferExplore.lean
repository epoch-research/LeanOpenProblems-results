import Submission.MonotoneClippingExplore

/-! The exact quantity that the monotone clipping budget controls: prefix
counts. A prefix-count limit is not a pointwise representation limit. -/
namespace Erdos66ClippingBudgetTransfer
open Filter AdditiveCombinatorics Erdos66Counting Erdos66MonotoneClipping
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma count_diff_add (A C : Set ℕ) (hCA : C ⊆ A) (N : ℕ) :
    count (A\C) N+count C N=count A N := by
  have he : cutoff (A\C) N=cutoff A N\cutoff C N := by
    ext a
    simp only [mem_cutoff,Finset.mem_sdiff,Set.mem_diff]
    tauto
  have hc : cutoff C N ⊆ cutoff A N := by
    intro a ha
    obtain ⟨haN,haC⟩ := mem_cutoff.mp ha
    exact mem_cutoff.mpr ⟨haN,hCA haC⟩
  change (cutoff (A\C) N).card+(cutoff C N).card=(cutoff A N).card
  rw [he]
  exact Finset.card_sdiff_add_card_eq_card hc

lemma count_limit_of_small_deletion_budget (A C : Set ℕ) (hCA : C ⊆ A)
    (R F : ℕ → ℝ) (hR : ∀ᶠ N : ℕ in atTop, 0<R N)
    (hbudget : ∀ N, (count (A\C) N:ℝ) ≤ F N)
    (hsmall : Tendsto (fun N ↦ F N/R N) atTop (𝓝 0))
    (c : ℝ) (hA : Tendsto (fun N ↦ (count A N:ℝ)/R N) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count C N:ℝ)/R N) atTop (𝓝 c) := by
  have hdel : Tendsto (fun N ↦ (count (A\C) N:ℝ)/R N) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hsmall
    · filter_upwards [hR] with N hN
      positivity
    · filter_upwards [hR] with N hN
      exact div_le_div_of_nonneg_right (hbudget N) hN.le
  have hh := hA.sub hdel
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [] with N
  have he : (count (A\C) N:ℝ)+(count C N:ℝ)=(count A N:ℝ) := by
    exact_mod_cast count_diff_add A C hCA N
  rw [←sub_div]
  congr 1
  linarith

 theorem clipping_preserves_count_limit_under_budget (A : Set ℕ) (q : ℕ → ℕ)
    (hq : ∀ n, 1 ≤ q n) (R : ℕ → ℝ) (hR : ∀ᶠ N : ℕ in atTop, 0<R N)
    (hsmall : Tendsto (fun N ↦
      (∑ n∈Finset.range (2*N), (excess (sumRep A n) (q n):ℝ))/R N) atTop (𝓝 0))
    (c : ℝ) (hA : Tendsto (fun N ↦ (count A N:ℝ)/R N) atTop (𝓝 c)) :
    ∃ C : Set ℕ, C ⊆ A ∧ (∀ n, sumRep C n ≤ q n) ∧
      Tendsto (fun N ↦ (count C N:ℝ)/R N) atTop (𝓝 c) := by
  obtain ⟨C,hCA,hupper,hbudget⟩ := exists_simultaneous_upper_clipping A q hq
  refine ⟨C,hCA,hupper,?_⟩
  apply count_limit_of_small_deletion_budget A C hCA R
    (fun N ↦ ∑ n∈Finset.range (2*N), (excess (sumRep A n) (q n):ℝ)) hR _ hsmall c hA
  intro N
  change (count (A\C) N:ℝ) ≤ ∑ n∈Finset.range (2*N), (excess (sumRep A n) (q n):ℝ)
  exact_mod_cast hbudget N

lemma excess_sum_bound (A : Set ℕ) (q : ℕ → ℕ) (N : ℕ) (V : ℝ)
    (hrep : ∀ n<N, (sumRep A n:ℝ) ≤ V) :
    (∑ n∈Finset.range N, (excess (sumRep A n) (q n):ℝ)) ≤
      (count {n | q n<sumRep A n} N:ℝ)*V := by
  have he : (∑ n∈Finset.range N, (excess (sumRep A n) (q n):ℝ)) =
      ∑ n∈cutoff {n | q n<sumRep A n} N, (excess (sumRep A n) (q n):ℝ) := by
    symm
    rw [cutoff,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hh : q n<sumRep A n
    · simp only [Set.mem_setOf_eq,hh,ite_true]
    · simp only [Set.mem_setOf_eq,hh,ite_false,excess,Nat.cast_zero]
  rw [he]
  calc
    _ ≤ ∑ _n∈cutoff {n | q n<sumRep A n} N, V := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnN,hnq⟩ := mem_cutoff.mp hn
      have hle : excess (sumRep A n) (q n) ≤ sumRep A n := by unfold excess; split_ifs <;> omega
      exact (by exact_mod_cast hle : (excess (sumRep A n) (q n):ℝ) ≤ sumRep A n).trans (hrep n hnN)
    _ = _ := by simp [count]

end Erdos66ClippingBudgetTransfer
