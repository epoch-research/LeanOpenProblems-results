import Submission.ShiftedHarmonicAverages

/-! Dilation on translated harmonic intervals, with both endpoint losses
retained. The error vanishes when the harmonic mass tends to infinity. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma positiveRawSum_dilation (T p : ℕ) (hp : 0 < p) (F : ℕ → ℝ) :
    p*positiveRawSum T (fun n => if p ∣ n then F n else 0) =
      positiveRawSum (T/p) (fun n => F (p*n)) := by
  unfold positiveRawSum
  simp only [ite_div,zero_div]
  exact harmonic_dilation_sum p T hp F

lemma positiveRawSum_dilation_bound (T p : ℕ) (hp : 0 < p)
    (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |p*positiveRawSum T (fun n => if p ∣ n then F n else 0)-
      positiveRawSum T (fun n => F (p*n))| ≤ p := by
  rw [positiveRawSum_dilation T p hp,abs_sub_comm]
  exact harmonic_div_endpoint_bound p T hp _ (fun n => hF (p*n))

lemma shiftedHarmonic_dilation_bound (A N p : ℕ) (hp : 0 < p)
    (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |p*shiftedHarmonicMean A N (fun n => if p ∣ n then F n else 0)-
      shiftedHarmonicMean A N (fun n => F (p*n))| ≤ 2*p/shiftedHarmonicMass A N := by
  have h₁ := positiveRawSum_dilation_bound (A+N+1) p hp F hF
  have h₂ := positiveRawSum_dilation_bound A p hp F hF
  unfold shiftedHarmonicMean
  rw [← mul_div_assoc,← sub_div,abs_div,abs_of_pos (shiftedHarmonicMass_pos A N)]
  apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos A N).le
  rw [shiftedHarmonicRaw_eq_sub,shiftedHarmonicRaw_eq_sub]
  have he : (p : ℝ)*(positiveRawSum (A+N+1) (fun n => if p ∣ n then F n else 0)-
      positiveRawSum A (fun n => if p ∣ n then F n else 0)) -
      (positiveRawSum (A+N+1) (fun n => F (p*n))-positiveRawSum A (fun n => F (p*n))) =
    ((p : ℝ)*positiveRawSum (A+N+1) (fun n => if p ∣ n then F n else 0)-
      positiveRawSum (A+N+1) (fun n => F (p*n))) -
    ((p : ℝ)*positiveRawSum A (fun n => if p ∣ n then F n else 0)-
      positiveRawSum A (fun n => F (p*n))) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

lemma shiftedHarmonicMean_fin_sum {ι : Type*} [Fintype ι] (A N : ℕ) (F : ι → ℕ → ℝ) :
    shiftedHarmonicMean A N (fun n => ∑ k, F k n) = ∑ k, shiftedHarmonicMean A N (F k) := by
  simp only [shiftedHarmonicMean,shiftedHarmonicRaw,sum_div]
  rw [sum_comm]

noncomputable def shiftedWindowDilationBudget {X : Type*}
    (A N p K : ℕ) (L : ℕ → X) : ℝ :=
  2*p/shiftedHarmonicMass A N + 2*∑ k : Fin K,
    shiftedHarmonicMean A N (fun n => labelDilationDefect p L (n+k))

lemma shifted_harmonic_window_dilation_error {X : Type*} (A N p K : ℕ) (hp : 0 < p)
    (L : ℕ → X) (F : (Fin K → X) → ℝ) (hF : ∀ x, |F x| ≤ 1) :
    |p*shiftedHarmonicMean A N (fun n => if p ∣ n then F (fun k => L (n+p*k)) else 0)-
      shiftedHarmonicMean A N (fun n => F (fun k => L (n+k)))| ≤
        shiftedWindowDilationBudget A N p K L := by
  classical
  let V (n : ℕ) := F (fun k => L (p*(n+k)))
  let W (n : ℕ) := F (fun k => L (n+k))
  let B : ℝ := p*shiftedHarmonicMean A N
    (fun n => if p ∣ n then F (fun k => L (n+p*k)) else 0)
  have htail : |B-shiftedHarmonicMean A N V| ≤ 2*p/shiftedHarmonicMass A N := by
    have h := shiftedHarmonic_dilation_bound A N p hp
      (fun n => F (fun k => L (n+p*k))) (fun _ => hF _)
    simpa only [B,V,mul_add] using h
  have hpoint (n : ℕ) : |V n-W n| ≤ 2*∑ k : Fin K, labelDilationDefect p L (n+k) :=
    bounded_window_observable_change F hF _ _
  have hdiff : |shiftedHarmonicMean A N V-shiftedHarmonicMean A N W| ≤
      2*∑ k : Fin K, shiftedHarmonicMean A N (fun n => labelDilationDefect p L (n+k)) := by
    apply (shiftedHarmonicMean_abs_difference_le A N V W).trans
    have hh := shiftedHarmonicMean_mono A N _ _ hpoint
    simpa only [shiftedHarmonicMean_const_mul,shiftedHarmonicMean_fin_sum] using hh
  exact (abs_sub_le B (shiftedHarmonicMean A N V) (shiftedHarmonicMean A N W)).trans
    (add_le_add htail hdiff)

lemma shiftedWindowDilationBudget_zero {X : Type*} (p K : ℕ) (L : ℕ → X)
    (hL : Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (A M : ℕ → ℕ) (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedWindowDilationBudget (A j) (M j) p K L) atTop (𝓝 0) := by
  have hd (k : Fin K) : Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun n => labelDilationDefect p L (n+k))) atTop (𝓝 0) := by
    apply shiftedHarmonicMean_zero_of_nonnegative_prefix_zero _ _
      (prefixMean_shift_zero _ (labelDilationDefect_abs_le p L) hL k) A M hH
    intro n
    unfold labelDilationDefect
    split_ifs <;> norm_num
  have hs := tendsto_finset_sum univ (fun k _ => hd k)
  have ht : Tendsto (fun j => (2*(p : ℝ))/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hH
  simpa only [shiftedWindowDilationBudget,sum_const_zero,mul_zero,add_zero] using ht.add (hs.const_mul 2)

lemma shifted_harmonic_window_dilation_le {X : Type*} (A N p K : ℕ) (hp : 0 < p)
    (L : ℕ → X) (F : (Fin K → X) → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    shiftedHarmonicMean A N (fun n => F (fun k => L (n+k))) ≤
      p*shiftedHarmonicMean A N (fun n => F (fun k => L (n+p*k)))+
        shiftedWindowDilationBudget A N p K L := by
  classical
  have he := (abs_le.mp (shifted_harmonic_window_dilation_error A N p K hp L F
    (fun x => by rw [abs_of_nonneg (hF x).1]; exact (hF x).2))).1
  have hm := shiftedHarmonicMean_mono A N
    (fun n => if p ∣ n then F (fun k => L (n+p*k)) else 0)
    (fun n => F (fun k => L (n+p*k))) (fun n => by
      dsimp only
      split_ifs
      · exact le_rfl
      · exact (hF _).1)
  linarith [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) p)]

#print axioms shiftedHarmonic_dilation_bound
#print axioms shiftedWindowDilationBudget_zero
#print axioms shifted_harmonic_window_dilation_le
end Erdos371.FiniteInformation
