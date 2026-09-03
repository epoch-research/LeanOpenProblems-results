import Submission.LocalPrimeLabelMeanPerturbation
import Submission.LocalGlobalPrimeRatio
import Submission.HarmonicAbelian

/-! The actual adjacent sign is approximable by comparisons of a fixed finite
sequence of local prime labels. Resolution is fixed before each endpoint limit. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma prefixMean_succ_error (N : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |prefixMean N (fun n => F (n+1))-prefixMean N F| ≤ 2/(N : ℝ) := by
  have he := (sum_range_succ' F N).symm.trans (sum_range_succ F N)
  have he' : (∑ n ∈ range N,F (n+1))-(∑ n ∈ range N,F n) = F N-F 0 := by linarith
  rw [prefixMean,prefixMean,← sub_div,he',abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ)≤N)]
  exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by linarith [hF N,hF 0])) (Nat.cast_nonneg N)

lemma prefixMean_succ_zero (F : ℕ → ℕ → ℝ) (hF : ∀ N n, |F N n| ≤ 1)
    (hzero : Tendsto (fun N => prefixMean N (F N)) atTop (𝓝 0)) :
    Tendsto (fun N => prefixMean N (fun n => F N (n+1))) atTop (𝓝 0) := by
  have he : Tendsto (fun N => prefixMean N (fun n => F N (n+1))-prefixMean N (F N)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    simpa only [Real.norm_eq_abs] using prefixMean_succ_error N (F N) (hF N)
  convert he.add hzero using 1 <;> simp

lemma harmonicMean_eventual_upper_of_prefix_upper (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 2)
    (η : ℝ) (hη : 0 ≤ η) (hmean : ∀ᶠ N : ℕ in atTop, prefixMean N F ≤ η)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, harmonicMean (N+1) F ≤ η+ε := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp hmean
  have ht : Tendsto (fun N : ℕ => (2*(harmonic T : ℝ)+4)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  filter_upwards [eventually_ge_atTop T,ht.eventually_lt_const hε] with N hNT ht
  have he (i : Fin (N+1)) : prefixMean (harmonicPrefixLength N i) F ≤
      η+2*(if harmonicPrefixLength N i<T then (1 : ℝ) else 0) := by
    by_cases hi : harmonicPrefixLength N i<T
    · rw [if_pos hi,mul_one]
      exact (le_abs_self _).trans ((abs_prefixMean_le _ (harmonicPrefixLength_pos N i) F 2
        (fun n _ => hF n)).trans (by linarith))
    · rw [if_neg hi,mul_zero,add_zero]
      exact hT _ (not_lt.mp hi)
  have hm := mean_mono (harmonicPrefixLaw N) _ _ he
  rw [harmonicPrefixLaw_representation,mean_add,mean_const,mean_const_mul] at hm
  have hmass := harmonicPrefixLaw_short_length_mass N T (by omega)
  have herr := (abs_le.mp (harmonicMean_range_error_two N F hF)).1
  change harmonicRangeMean (N+1) F ≤ _ at hm
  rw [add_div,mul_div_assoc] at ht
  linarith

end Erdos371.FiniteInformation
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma bounded_pair_observable_change {A : Type*} [DecidableEq A] (C : A → A → ℝ)
    (hC : ∀ a b, |C a b| ≤ 1) (a b a' b' : A) :
    |C a b-C a' b'| ≤ 2*(if a≠a' then (1 : ℝ) else 0)+2*(if b≠b' then 1 else 0) := by
  have hbound : |C a b-C a' b'| ≤ 2 := (abs_sub _ _).trans (by linarith [hC a b,hC a' b'])
  by_cases ha : a=a' <;> by_cases hb : b=b'
  all_goals simp_all only [ne_eq,not_true_eq_false,not_false_eq_true,if_true,if_false,
    mul_zero,mul_one,zero_add,add_zero,sub_self,abs_zero]
  all_goals linarith

/-- Endpoint-dependent global labels and the fixed local labels agree in
natural mean for each fixed resolution Q. This is not a harmonic-mean claim. -/
theorem local_global_prime_label_mean_zero (Q : ℕ) :
    Tendsto (fun N : ℕ => prefixMean N (fun n =>
      if primeQuantLabel Q N n ≠ localPrimeLabel Q n then (1 : ℝ) else 0)) atTop (𝓝 0) :=
  localPrimeLabel_mean_perturbation_zero Q normalizedPrimeLog
    normalizedPrimeLog_unit_on_prefix local_global_prime_ratio_mean_zero

noncomputable def localFactorSign (Q n : ℕ) : ℝ :=
  orderSkew (localPrimeLabel Q n) (localPrimeLabel Q (n+1))

lemma localFactorSign_error_le_two (Q n : ℕ) : |factorSign n-localFactorSign Q n| ≤ 2 := by
  have hF : |factorSign n| = 1 := by unfold factorSign predicateSign; split_ifs <;> norm_num
  have hL := orderSkew_abs_le (localPrimeLabel Q n) (localPrimeLabel Q (n+1))
  exact (abs_sub _ _).trans (by change |localFactorSign Q n| ≤ 1 at hL; linarith)

lemma local_global_factorSign_mean_error_zero (Q : ℕ) :
    Tendsto (fun N : ℕ => prefixMean N (fun n => |quantFactorSign Q N n-localFactorSign Q n|))
      atTop (𝓝 0) := by
  classical
  let D (N n : ℕ) : ℝ := if primeQuantLabel Q N n ≠ localPrimeLabel Q n then 1 else 0
  have hD : Tendsto (fun N => prefixMean N (D N)) atTop (𝓝 0) := local_global_prime_label_mean_zero Q
  have hDs : Tendsto (fun N => prefixMean N (fun n => D N (n+1))) atTop (𝓝 0) :=
    prefixMean_succ_zero D (fun N n => by dsimp [D]; split_ifs <;> norm_num) hD
  have ht := (hD.const_mul 2).add (hDs.const_mul 2)
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero (fun N => by unfold prefixMean; positivity) _ ht
  intro N
  have hs := sum_le_sum (s := range N) (fun n _ => bounded_pair_observable_change orderSkew
    orderSkew_abs_le (primeQuantLabel Q N n) (primeQuantLabel Q N (n+1))
      (localPrimeLabel Q n) (localPrimeLabel Q (n+1)))
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  simpa only [prefixMean,sum_add_distrib,← mul_sum,add_div,mul_div_assoc,quantFactorSign,localFactorSign,D] using hd

/-- Every sufficiently fine fixed resolution approximates the actual sign
in natural mean. The endpoint threshold may depend on that fixed resolution. -/
theorem localFactorSign_natural_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ > 0, ∀ Q ≥ Q₀, ∀ᶠ N : ℕ in atTop,
      prefixMean N (fun n => |factorSign n-localFactorSign Q n|) ≤ ε := by
  obtain ⟨Q₀,hQ₀,happrox⟩ := quantFactorSign_uniform_approximation (ε/2) (by positivity)
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ
  filter_upwards [happrox,(local_global_factorSign_mean_error_zero Q).eventually_lt_const
    (by positivity : (0 : ℝ)<ε/2)] with N ha he
  have hs := sum_le_sum (s := range N) (fun n _ => abs_sub_le (factorSign n)
    (quantFactorSign Q N n) (localFactorSign Q n))
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  rw [sum_add_distrib,add_div] at hd
  change prefixMean N (fun n => |factorSign n-localFactorSign Q n|) ≤
    prefixMean N (fun n => |factorSign n-quantFactorSign Q N n|)+
      prefixMean N (fun n => |quantFactorSign Q N n-localFactorSign Q n|) at hd
  have haQ := ha Q hQ
  change prefixMean N (fun n => |factorSign n-quantFactorSign Q N n|) ≤ ε/2 at haQ
  linarith

/-- Fixed finite labels also approximate the true sign in harmonic mean.
This follows from uniform control of all sufficiently long natural prefixes. -/
theorem localFactorSign_harmonic_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ Q₀ > 0, ∀ Q ≥ Q₀, ∀ᶠ N : ℕ in atTop,
      harmonicMean (N+1) (fun n => |factorSign n-localFactorSign Q n|) ≤ ε := by
  obtain ⟨Q₀,hQ₀,happrox⟩ := localFactorSign_natural_approximation (ε/2) (by positivity)
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ
  simpa only [add_halves] using harmonicMean_eventual_upper_of_prefix_upper
    (fun n => |factorSign n-localFactorSign Q n|)
    (fun n => by simpa only [abs_abs] using localFactorSign_error_le_two Q n)
    (ε/2) (by positivity) (happrox Q hQ) (ε/2) (by positivity)

#print axioms local_global_prime_label_mean_zero
#print axioms local_global_factorSign_mean_error_zero
#print axioms localFactorSign_natural_approximation
#print axioms localFactorSign_harmonic_approximation
end Erdos371
