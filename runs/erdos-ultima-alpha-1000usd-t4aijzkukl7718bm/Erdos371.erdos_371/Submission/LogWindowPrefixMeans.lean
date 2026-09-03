import Submission.GrowingWindowLogEndpoints

/-! Uniform long logarithmic windows also average the ordinary prefix means.
A finite no-crossing lemma will locate ordinary proportions near their center. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma prefixMean_unit_bound (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N : ℕ) :
    |prefixMean N f| ≤ 1 := by
  by_cases hN : N=0
  · subst N; simp [prefixMean]
  · exact abs_prefixMean_le N (Nat.pos_of_ne_zero hN) f 1 (fun n _ => hf n)

lemma mul_prefixMean_eq_sum (f : ℕ → ℝ) (N : ℕ) :
    (N : ℝ)*prefixMean N f = ∑ n ∈ range N, f n := by
  by_cases hN : N=0
  · subst N; simp [prefixMean]
  · unfold prefixMean
    field_simp

lemma prefixMean_step_identity (f : ℕ → ℝ) (n : ℕ) :
    (n+1 : ℝ)*prefixMean (n+1) f = (n : ℝ)*prefixMean n f+f n := by
  rw [← Nat.cast_add_one,mul_prefixMean_eq_sum,mul_prefixMean_eq_sum,sum_range_succ]

lemma shiftedHarmonicMean_prefix_identity (f : ℕ → ℝ) (A M : ℕ) :
    shiftedHarmonicMean A M f =
      shiftedHarmonicMean A M (fun n => prefixMean (n+1) f)+
        (prefixMean (A+M+2) f-prefixMean (A+1) f)/shiftedHarmonicMass A M := by
  have hp (n : ℕ) (hn : 0 < n) : f n/(n : ℝ) =
      (prefixMean (n+1) f-prefixMean n f)+prefixMean (n+1) f/(n : ℝ) := by
    have h := prefixMean_step_identity f n
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    nlinarith
  have hs := sum_range_sub (fun n => prefixMean (A+n+1) f) (M+1)
  simp only [Nat.add_zero] at hs
  have hs' : (∑ n ∈ range (M+1), (prefixMean (A+n+1+1) f-prefixMean (A+n+1) f)) =
      prefixMean (A+M+2) f-prefixMean (A+1) f := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hs
  unfold shiftedHarmonicMean shiftedHarmonicRaw
  have he := sum_congr (s₁ := range (M+1)) rfl (fun n _ => hp (A+n+1) (by omega))
  simp only [Nat.cast_add,Nat.cast_one] at he
  rw [he,sum_add_distrib,hs',add_div]
  ring

lemma shiftedHarmonicMean_prefix_error (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (A M : ℕ) :
    |shiftedHarmonicMean A M f-shiftedHarmonicMean A M (fun n => prefixMean n f)| ≤
      6/shiftedHarmonicMass A M := by
  have hb := shiftedHarmonicMean_shift_bound A M (fun n => prefixMean n f) (prefixMean_unit_bound f hf)
  have hp := shiftedHarmonicMean_prefix_identity f A M
  have ht : |(prefixMean (A+M+2) f-prefixMean (A+1) f)/shiftedHarmonicMass A M| ≤
      2/shiftedHarmonicMass A M := by
    rw [abs_div,abs_of_pos (shiftedHarmonicMass_pos A M)]
    apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos A M).le
    exact (abs_sub _ _).trans (by linarith [prefixMean_unit_bound f hf (A+M+2),prefixMean_unit_bound f hf (A+1)])
  rw [hp,show shiftedHarmonicMean A M (fun n => prefixMean (n+1) f)+
      (prefixMean (A+M+2) f-prefixMean (A+1) f)/shiftedHarmonicMass A M-
      shiftedHarmonicMean A M (fun n => prefixMean n f) =
      (shiftedHarmonicMean A M (fun n => prefixMean (n+1) f)-shiftedHarmonicMean A M (fun n => prefixMean n f))+
        (prefixMean (A+M+2) f-prefixMean (A+1) f)/shiftedHarmonicMass A M by ring]
  exact (abs_add_le _ _).trans ((add_le_add hb ht).trans_eq (by ring))

lemma shiftedHarmonicMean_prefix_zero (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (A M : ℕ → ℕ) (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop)
    (hz : Tendsto (fun j => shiftedHarmonicMean (A j) (M j) f) atTop (𝓝 0)) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) (fun n => prefixMean n f)) atTop (𝓝 0) := by
  have he : Tendsto (fun j => shiftedHarmonicMean (A j) (M j) f-
      shiftedHarmonicMean (A j) (M j) (fun n => prefixMean n f)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (tendsto_const_nhds.div_atTop hH :
      Tendsto (fun j => (6 : ℝ)/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0))
    intro j
    simpa only [Real.norm_eq_abs] using shiftedHarmonicMean_prefix_error f hf (A j) (M j)
  simpa only [sub_sub_cancel,sub_zero] using hz.sub he

lemma shiftedHarmonicMean_local_mono (A M : ℕ) (f g : ℕ → ℝ)
    (h : ∀ k < M+1, f (A+k+1) ≤ g (A+k+1)) :
    shiftedHarmonicMean A M f ≤ shiftedHarmonicMean A M g := by
  apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos A M).le
  apply sum_le_sum
  intro n hn
  exact div_le_div_of_nonneg_right (h n (mem_range.mp hn)) (by positivity)

lemma finite_prefix_gap_side (g : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (L U : ℕ) (hLU : L ≤ U)
    (haway : ∀ n ∈ Icc L U, ε ≤ |g n|)
    (hstep : ∀ n ∈ Ico L U, |g (n+1)-g n| < ε) :
    (∀ n ∈ Icc L U, g n ≤ -ε) ∨ (∀ n ∈ Icc L U, ε ≤ g n) := by
  have hside (n : ℕ) (hn : n ∈ Icc L U) : g n ≤ -ε ∨ ε ≤ g n := by
    rcases le_abs.mp (haway n hn) with hp | hn
    · exact Or.inr hp
    · exact Or.inl (by linarith)
  rcases hside L (mem_Icc.mpr ⟨le_rfl,hLU⟩) with hl | hr
  · left
    have hi (k : ℕ) : L+k ≤ U → g (L+k) ≤ -ε := by
      induction k with
      | zero => simpa using (fun _ : L ≤ U => hl)
      | succ k ih =>
        intro hk
        have hi := ih (by omega)
        rcases hside (L+k+1) (mem_Icc.mpr ⟨by omega,by omega⟩) with h | h
        · simpa only [Nat.add_assoc] using h
        · have hs := (abs_lt.mp (hstep (L+k) (mem_Ico.mpr ⟨by omega,by omega⟩))).2
          linarith
    intro n hn
    obtain ⟨hLn,hnU⟩ := mem_Icc.mp hn
    simpa only [Nat.add_sub_of_le hLn] using hi (n-L) (by omega)
  · right
    have hi (k : ℕ) : L+k ≤ U → ε ≤ g (L+k) := by
      induction k with
      | zero => simpa using (fun _ : L ≤ U => hr)
      | succ k ih =>
        intro hk
        have hi := ih (by omega)
        rcases hside (L+k+1) (mem_Icc.mpr ⟨by omega,by omega⟩) with h | h
        · have hs := (abs_lt.mp (hstep (L+k) (mem_Ico.mpr ⟨by omega,by omega⟩))).1
          linarith
        · simpa only [Nat.add_assoc] using h
    intro n hn
    obtain ⟨hLn,hnU⟩ := mem_Icc.mp hn
    simpa only [Nat.add_sub_of_le hLn] using hi (n-L) (by omega)

#print axioms shiftedHarmonicMean_prefix_error
#print axioms finite_prefix_gap_side
end Erdos371.FiniteInformation
