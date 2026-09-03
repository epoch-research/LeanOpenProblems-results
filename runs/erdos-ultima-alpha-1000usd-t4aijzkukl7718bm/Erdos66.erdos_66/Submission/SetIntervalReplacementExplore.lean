import Submission.FlatProfileWindowsExplore

/-! Exact prefix bookkeeping for cardinality-preserving interval replacements. -/
namespace Erdos66SetIntervalReplacement
open AdditiveCombinatorics Erdos66ReflectionRoundingPatch Erdos66Counting
  Erdos66Generating Erdos66Rounding
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def replace (A : Set ℕ) (a b : ℕ) (G : Finset ℕ) : Set ℕ :=
  (A \ Set.Ico a b) ∪ (G : Set ℕ)

lemma mem_replace_outside (A : Set ℕ) (a b : ℕ) (G : Finset ℕ)
    (hG : G ⊆ Finset.Ico a b) (i : ℕ) (hi : i ∉ Set.Ico a b) :
    i ∈ replace A a b G ↔ i ∈ A := by
  have hiG : i ∉ G := fun h ↦ hi (Finset.mem_Ico.mp (hG h))
  simp [replace,hi,hiG]

lemma count_sum (A : Set ℕ) (N : ℕ) :
    (count A N : ℝ) = ∑ i ∈ Finset.range N, indicator A i := by
  simp [count,cutoff,indicator,Finset.sum_ite]

lemma card_inter_sum (G : Finset ℕ) (N : ℕ) :
    ((G ∩ Finset.range N).card : ℝ) =
      ∑ i ∈ Finset.range N, indicator (G : Set ℕ) i := by
  rw [Finset.inter_comm]
  simp [indicator,Finset.sum_ite,Finset.filter_mem_eq_inter]

lemma replacement_count_difference (A : Set ℕ) (a b : ℕ) (G : Finset ℕ)
    (hG : G ⊆ Finset.Ico a b) (N : ℕ) :
    (count (replace A a b G) N : ℝ) - count A N =
      ((G ∩ Finset.range N).card : ℝ) -
        ((intervalPart A a b ∩ Finset.range N).card : ℝ) := by
  rw [count_sum,count_sum,card_inter_sum,card_inter_sum,←Finset.sum_sub_distrib,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hiG : i ∈ G → a ≤ i ∧ i < b := fun h ↦ Finset.mem_Ico.mp (hG h)
  simp only [indicator,replace,Set.mem_union,Set.mem_diff,Set.mem_Ico,Finset.mem_coe,
    intervalPart,Finset.mem_filter,Finset.mem_Ico]
  split_ifs <;> norm_num <;> tauto

lemma replacement_count_before (A : Set ℕ) (a b : ℕ) (G : Finset ℕ)
    (hG : G ⊆ Finset.Ico a b) (N : ℕ) (hN : N ≤ a) :
    count (replace A a b G) N = count A N := by
  unfold count
  congr 1
  ext i
  simp only [mem_cutoff]
  apply and_congr_right
  intro hi
  exact mem_replace_outside A a b G hG i (by simp only [Set.mem_Ico]; omega)

lemma replacement_count_after (A : Set ℕ) (a b : ℕ) (G : Finset ℕ)
    (hG : G ⊆ Finset.Ico a b) (hcard : G.card = (intervalPart A a b).card)
    (N : ℕ) (hN : b ≤ N) : count (replace A a b G) N = count A N := by
  have hg : G ⊆ Finset.range N := fun i hi ↦
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp (hG hi)).2 hN)
  have ha : intervalPart A a b ⊆ Finset.range N := fun i hi ↦
    Finset.mem_range.mpr (lt_of_lt_of_le
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).2 hN)
  have hh := replacement_count_difference A a b G hG N
  rw [Finset.inter_eq_left.mpr hg,Finset.inter_eq_left.mpr ha,hcard,sub_self] at hh
  exact_mod_cast sub_eq_zero.mp hh

lemma intervalPart_congr (A B : Set ℕ) (a b : ℕ)
    (h : ∀ i ∈ Set.Ico a b, i ∈ A ↔ i ∈ B) :
    intervalPart A a b = intervalPart B a b := by
  apply Finset.filter_congr
  intro i hi
  exact h i (Finset.mem_Ico.mp hi)

lemma intervalPart_sub_replace (A : Set ℕ) (L W : ℕ) (G : Finset ℕ) :
    ((intervalPart A L (L+W) ∪ G : Finset ℕ) : Set ℕ) ⊆
      replace A (L+W) (L+2*W) G := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · have ha := Finset.mem_filter.mp hi
    have hb := Finset.mem_Ico.mp ha.1
    exact Or.inl ⟨ha.2,by simp only [Set.mem_Ico]; omega⟩
  · exact Or.inr hi

end Erdos66SetIntervalReplacement
