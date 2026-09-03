import Submission.HarmonicLargestPrimeHalf
import Submission.PrimeWinnerEnergy

/-! Harmonic cancellation with arbitrary fixed colours on the winning prime.
This does not assert natural density. -/
namespace Erdos371
open Finset Filter FiniteInformation DilationSpectrum
open scoped Topology
set_option autoImplicit false

lemma maxPrimeFac_mean_dilation_defect_zero (p : ℕ) (hp : 0 < p) :
    Tendsto (fun N => prefixMean N (labelDilationDefect p Nat.maxPrimeFac))
      atTop (𝓝 0) := by
  classical
  have h := (density_iff_count _ 0).mp (maxPrimeFac_mul_disagreement_hasDensity_zero p hp)
  have he (N : ℕ) : prefixMean N (labelDilationDefect p Nat.maxPrimeFac) =
      (((range N).filter (fun n => Nat.maxPrimeFac (p*n) ≠ Nat.maxPrimeFac n)).card : ℝ)/N := by
    unfold prefixMean labelDilationDefect
    congr 1
    rw [Finset.natCast_card_filter]
    apply sum_congr rfl
    intro n _
    split_ifs <;> rfl
  simpa only [he] using h

lemma labelDilationDefect_prod_le {A B : Type*} (p : ℕ) (L : ℕ → A) (M : ℕ → B) (n : ℕ) :
    labelDilationDefect p (fun n => (L n,M n)) n ≤
      labelDilationDefect p L n+labelDilationDefect p M n := by
  classical
  unfold labelDilationDefect
  by_cases hL : L (p*n)=L n <;> by_cases hM : M (p*n)=M n <;> simp_all

lemma labelDilationDefect_comp_le {A B : Type*} (p : ℕ) (L : ℕ → A) (g : A → B) (n : ℕ) :
    labelDilationDefect p (fun n => g (L n)) n ≤ labelDilationDefect p L n := by
  classical
  unfold labelDilationDefect
  by_cases h : L (p*n)=L n <;> simp_all
  split_ifs <;> norm_num

lemma primeColouredLabel_mean_dilation_defect_zero (Q : ℕ) (g : ℕ → Bool)
    (p : ℕ) (hp : 0 < p) :
    Tendsto (fun N => prefixMean N (labelDilationDefect p
      (fun n => (localPrimeLabel Q n,g (Nat.maxPrimeFac n))))) atTop (𝓝 0) := by
  have ht := (localPrimeLabel_mean_dilation_defect_zero Q p hp).add
    (maxPrimeFac_mean_dilation_defect_zero p hp)
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => by unfold prefixMean labelDilationDefect; positivity) _ ht
  intro N
  unfold prefixMean
  rw [← add_div,← sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply sum_le_sum
  intro n _
  exact (labelDilationDefect_prod_le p (localPrimeLabel Q) _ n).trans
    (add_le_add_right (labelDilationDefect_comp_le p Nat.maxPrimeFac g n) _)

noncomputable def colouredOrderSkew {A : Type*} [LinearOrder A]
    (w : Bool → ℝ) (a b : A × Bool) : ℝ :=
  if a.1 < b.1 then w b.2 else if b.1 < a.1 then -w a.2 else 0

lemma colouredOrderSkew_swap {A : Type*} [LinearOrder A]
    (w : Bool → ℝ) (a b : A × Bool) :
    colouredOrderSkew w b a = -colouredOrderSkew w a b := by
  unfold colouredOrderSkew
  rcases lt_trichotomy a.1 b.1 with h|h|h
  · simp [h,not_lt.mpr (le_of_lt h)]
  · simp [h]
  · simp [h,not_lt.mpr (le_of_lt h)]

lemma colouredOrderSkew_abs_le {A : Type*} [LinearOrder A]
    (w : Bool → ℝ) (hw : ∀ b, |w b| ≤ 1) (a b : A × Bool) :
    |colouredOrderSkew w a b| ≤ 1 := by
  unfold colouredOrderSkew
  split_ifs <;> first | exact hw _ | simpa only [abs_neg] using hw a.2 | norm_num

lemma colouredOrderSkew_approximation (Q : ℕ) (g : ℕ → Bool)
    (w : Bool → ℝ) (hw : ∀ b, |w b| ≤ 1) (n : ℕ) :
    |factorSign n*w (g (primeWinner n))-
      colouredOrderSkew w (localPrimeLabel Q n,g (Nat.maxPrimeFac n))
        (localPrimeLabel Q (n+1),g (Nat.maxPrimeFac (n+1)))| ≤
    |factorSign n-localFactorSign Q n| := by
  have h0 := hw (g (Nat.maxPrimeFac n))
  have h1 := hw (g (Nat.maxPrimeFac (n+1)))
  have ht := abs_sub (w (g (Nat.maxPrimeFac (n+1)))) (-w (g (Nat.maxPrimeFac n)))
  have ht' := abs_sub (-w (g (Nat.maxPrimeFac n))) (w (g (Nat.maxPrimeFac (n+1))))
  unfold factorSign predicateSign primeWinner localFactorSign orderSkew colouredOrderSkew
  by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · rw [if_pos h,max_eq_right h.le]
    split_ifs <;> simp only [one_mul,sub_self,abs_zero,sub_neg_eq_add,sub_zero] at * <;> norm_num at * <;> linarith
  · rw [if_neg h,max_eq_left (not_lt.mp h)]
    split_ifs <;> simp only [neg_one_mul,sub_self,abs_zero,sub_neg_eq_add,sub_zero,abs_neg] at * <;> norm_num at * <;> linarith

/-- Fixed, arbitrarily chosen prime colours may weight the harmonic comparison
by the colour of its larger prime. -/
theorem primeWinner_coloured_harmonic_zero (g : ℕ → Bool)
    (w : Bool → ℝ) (hw : ∀ b, |w b| ≤ 1) :
    Tendsto (fun N => harmonicMean (N+1) (fun n => factorSign n*w (g (primeWinner n))))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Q,hQ,happrox⟩ := localFactorSign_harmonic_approximation (ε/2) (by positivity)
  let L (n : ℕ) := (localPrimeLabel Q n,g (Nat.maxPrimeFac n))
  let F (n : ℕ) := factorSign n*w (g (primeWinner n))
  let G (n : ℕ) := colouredOrderSkew w (L n) (L (n+1))
  have hz : Tendsto (fun N => harmonicMean (N+1) G) atTop (𝓝 0) :=
    stable_finite_labels_harmonic_skew_zero L (primeColouredLabel_mean_dilation_defect_zero Q g)
      (colouredOrderSkew w) (colouredOrderSkew_swap w) (colouredOrderSkew_abs_le w hw)
  filter_upwards [happrox Q le_rfl,hz.abs.eventually_lt_const (show |(0 : ℝ)|<ε/2 by simpa using half_pos hε)]
    with N ha hs
  have herr := (harmonicMean_abs_difference_le N F G).trans
    ((harmonicMean_mono N _ _ (colouredOrderSkew_approximation Q g w hw)).trans ha)
  have htri := abs_sub_le (harmonicMean (N+1) F) (harmonicMean (N+1) G) 0
  rw [Real.dist_eq,sub_zero]
  simp only [sub_zero] at htri
  change |harmonicMean (N+1) F|<ε
  linarith

#print axioms primeWinner_coloured_harmonic_zero
end Erdos371
