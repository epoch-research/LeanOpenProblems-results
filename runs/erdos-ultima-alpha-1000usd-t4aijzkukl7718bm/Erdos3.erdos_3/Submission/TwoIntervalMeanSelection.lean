import Submission.NaturalProgressionCuts

/-! Positive mean on at most two intervals gives a long positive-mean piece.
Only an upper bound by one is needed for the function. -/
namespace Erdos3TwoIntervalMeanSelection
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

lemma large_sum_piece (f : ℕ → ℝ) (s m L : ℕ) (hL : 0 < L) (hmL : m ≤ L)
    (hf : ∀ j < m, f (s+j) ≤ 1) {γ : ℝ} (hγ : 0 < γ)
    (hsum : γ*(L : ℝ)/2 ≤ ∑ j ∈ range m, f (s+j)) :
    0 < m ∧ γ*(L : ℝ)/2 ≤ (m : ℝ) ∧ γ/2 ≤ 𝔼 j : Fin m, f (s+j.val) := by
  have hupper : (∑ j ∈ range m, f (s+j)) ≤ (m : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ range m, (1 : ℝ) := sum_le_sum (fun j hj ↦ hf j (mem_range.mp hj))
      _ = _ := by simp
  have hsize := hsum.trans hupper
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hm : (0 : ℝ) < m := (by positivity : 0 < γ*(L : ℝ)/2).trans_le hsize
  refine ⟨by exact_mod_cast hm,hsize,?_⟩
  rw [Fintype.expect_eq_sum_div_card,Fintype.card_fin,Fin.sum_univ_eq_sum_range (fun j ↦ f (s+j)) m]
  apply (le_div_iff₀ hm).mpr
  have hmL' : (m : ℝ) ≤ L := by exact_mod_cast hmL
  have hh := mul_le_mul_of_nonneg_left hmL' (by positivity : 0 ≤ γ/2)
  linarith

/-- One of two disjoint index intervals has both a substantial length and a
positive conditional mean. There is no density loss from passing to that piece. -/
theorem positive_two_interval_piece (f : ℕ → ℝ) (b c e L : ℕ)
    (hbc : b ≤ c) (hce : c ≤ e) (heL : e ≤ L) (hL : 0 < L)
    (hf : ∀ j < L, f j ≤ 1)
    (hzero : ∀ j < L, ¬ (j < b ∨ c ≤ j ∧ j < e) → f j = 0)
    {γ : ℝ} (hγ : 0 < γ) (hmean : γ ≤ 𝔼 j : Fin L, f j.val) :
    ∃ s m : ℕ, ((s = 0 ∧ m = b) ∨ (s = c ∧ m = e-c)) ∧
      0 < m ∧ γ*(L : ℝ)/2 ≤ (m : ℝ) ∧ γ/2 ≤ 𝔼 j : Fin m, f (s+j.val) := by
  have hgap : (∑ j ∈ Ico b c, f j) = 0 := by
    apply sum_eq_zero
    intro j hj
    obtain ⟨hjb,hjc⟩ := mem_Ico.mp hj
    exact hzero j (by omega) (by omega)
  have htail : (∑ j ∈ Ico e L, f j) = 0 := by
    apply sum_eq_zero
    intro j hj
    obtain ⟨hje,hjL⟩ := mem_Ico.mp hj
    exact hzero j hjL (by omega)
  have hbc' := sum_range_add_sum_Ico f hbc
  have hce' := sum_range_add_sum_Ico f hce
  have heL' := sum_range_add_sum_Ico f heL
  rw [hgap,add_zero] at hbc'
  rw [htail,add_zero] at heL'
  have hdecomp : (∑ j ∈ range L, f j) = (∑ j ∈ range b, f j)+(∑ j ∈ Ico c e, f j) := by
    rw [← heL',← hce',← hbc']
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [Fintype.expect_eq_sum_div_card,Fintype.card_fin,Fin.sum_univ_eq_sum_range] at hmean
  have hsum := (le_div_iff₀ hL').mp hmean
  rw [hdecomp] at hsum
  by_cases hb : γ*(L : ℝ)/2 ≤ ∑ j ∈ range b, f j
  · obtain ⟨hb0,hsize,hinc⟩ := large_sum_piece f 0 b L hL (by omega)
      (fun j hj ↦ by simpa only [zero_add] using hf j (by omega)) hγ
      (by simpa only [zero_add] using hb)
    exact ⟨0,b,Or.inl ⟨rfl,rfl⟩,hb0,hsize,hinc⟩
  · have hh : γ*(L : ℝ)/2 ≤ ∑ j ∈ Ico c e, f j := by linarith
    rw [sum_Ico_eq_sum_range] at hh
    obtain ⟨hm,hsize,hinc⟩ := large_sum_piece f c (e-c) L hL (by omega)
      (fun j hj ↦ hf (c+j) (by omega)) hγ hh
    exact ⟨c,e-c,Or.inr ⟨rfl,rfl⟩,hm,hsize,hinc⟩

#print axioms positive_two_interval_piece
end Erdos3TwoIntervalMeanSelection
