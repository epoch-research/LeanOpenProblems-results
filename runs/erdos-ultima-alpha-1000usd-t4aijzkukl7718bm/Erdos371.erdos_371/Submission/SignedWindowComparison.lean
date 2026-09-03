import Submission.PositiveWindowComparison

/-! A strict, non-sharp bound on the actual signed comparison in terminal
windows. This does not prove that signed window sums tend to zero. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

lemma factorSign_weighted_decomposition (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S, w n * factorSign n) =
      (∑ n ∈ S.filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)), w n) -
      (∑ n ∈ S.filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n), w n) ∧
    (∑ n ∈ S, w n) =
      (∑ n ∈ S.filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)), w n) +
      (∑ n ∈ S.filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n), w n) := by
  simp only [sum_filter, ← sum_sub_distrib, ← sum_add_distrib]
  constructor <;> apply sum_congr rfl <;> intro n _
  all_goals
    rcases lt_or_gt_of_ne (consecutive_maxPrimeFac_ne n) with h | h
    · simp [factorSign,predicateSign,h,h.not_gt]
    · simp [factorSign,predicateSign,h,h.not_gt]

lemma factorSign_weighted_abs_le_of_both (S : Finset ℕ) (w : ℕ → ℝ) (η : ℝ)
    (hr : η ≤ ∑ n ∈ S.filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)), w n)
    (hf : η ≤ ∑ n ∈ S.filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n), w n) :
    |∑ n ∈ S, w n * factorSign n| ≤ (∑ n ∈ S, w n) - 2*η := by
  obtain ⟨hs,ht⟩ := factorSign_weighted_decomposition S w
  rw [hs,ht]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma harmonic_filter_ge_card_div_endpoint (P : ℕ → Prop) [DecidablePred P]
    (L M : ℕ) (hL : 0 < L) :
    (((Ico L M).filter P).card : ℝ)/M ≤ ∑ n ∈ (Ico L M).filter P, (1 : ℝ)/n := by
  calc
    _ = ∑ _n ∈ (Ico L M).filter P, (1 : ℝ)/M := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn,_⟩ := mem_filter.mp hn
      obtain ⟨hLn,hnM⟩ := mem_Ico.mp hn
      exact one_div_le_one_div_of_le (by exact_mod_cast hL.trans_le hLn)
        (by exact_mod_cast hnM.le)

/-- The signed harmonic mass in every sufficiently long relative window is
bounded strictly below the unsigned harmonic mass by a uniform positive amount.
The assertion is intentionally weaker than harmonic-window cancellation. -/
theorem signed_harmonic_window_strict_bound (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ M : ℕ in atTop, ∀ L ≤ M, 0 < L →
      (L : ℝ) ≤ (1-θ)*(M : ℝ) →
      |∑ n ∈ Ico L M, factorSign n/(n : ℝ)| ≤ (∑ n ∈ Ico L M, (1 : ℝ)/n) - 2*δ := by
  obtain ⟨δ,hδ,hw⟩ := rising_falling_positive_window_proportions θ hθ hθ1
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hw] with M hM
  intro L hLM hL hθL
  obtain ⟨hr,hf⟩ := hM L hLM hθL
  have hr' := hr.trans (harmonic_filter_ge_card_div_endpoint _ L M hL)
  have hf' := hf.trans (harmonic_filter_ge_card_div_endpoint _ L M hL)
  simpa only [one_div_mul_eq_div] using
    factorSign_weighted_abs_le_of_both (Ico L M) (fun n => (1 : ℝ)/n) δ hr' hf'

/-- Both signs occupy a fixed positive fraction of every fixed relative
window, so its ordinary signed mean is uniformly separated from `±1`. -/
theorem signed_natural_window_strict_bound (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ M : ℕ in atTop, ∀ L ≤ M,
      (L : ℝ) ≤ (1-θ)*(M : ℝ) →
      |∑ n ∈ Ico L M, factorSign n|/(M : ℝ) ≤ (M-L : ℕ)/(M : ℝ)-2*δ := by
  obtain ⟨δ,hδ,hw⟩ := rising_falling_positive_window_proportions θ hθ hθ1
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hw,eventually_gt_atTop (0 : ℕ)] with M hM hMpos
  intro L hLM hθL
  obtain ⟨hr,hf⟩ := hM L hLM hθL
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hr' : δ*(M : ℝ) ≤ ∑ _n ∈ (Ico L M).filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)), (1 : ℝ) := by
    simpa using (le_div_iff₀ hMr).mp hr
  have hf' : δ*(M : ℝ) ≤ ∑ _n ∈ (Ico L M).filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n), (1 : ℝ) := by
    simpa using (le_div_iff₀ hMr).mp hf
  have hs := factorSign_weighted_abs_le_of_both (Ico L M) (fun _ => (1 : ℝ)) (δ*M) hr' hf'
  simp only [one_mul,sum_const,Nat.card_Ico,nsmul_eq_mul,mul_one] at hs
  have hd := div_le_div_of_nonneg_right hs hMr.le
  convert hd using 1
  field_simp

#print axioms signed_harmonic_window_strict_bound
#print axioms signed_natural_window_strict_bound
end Erdos371
