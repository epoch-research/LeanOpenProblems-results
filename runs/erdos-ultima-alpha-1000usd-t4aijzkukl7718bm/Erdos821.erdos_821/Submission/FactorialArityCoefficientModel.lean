import Submission.PoissonArityCoefficientModel
import Submission.HigherDivisorWeights

/-!
# A factorial-sensitive check on arity coefficient bootstrapping

The earlier Poisson model only gives geometrically small UNNORMALIZED
coefficients; multiplication by k! changes that conclusion. This model
retains the binomial coefficient coming from a large prime-power exponent.
Its leading coefficients remain geometrically small after multiplication
by k!. It is not a model of the distribution of actual shifted primes.
-/

open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821.ArityModel
set_option maxHeartbeats 3000000

noncomputable def binomialArityMoment (r k N : ℕ) : ℝ :=
  (k : ℝ)^r*((N+(k-1)).choose (k-1) : ℝ)

noncomputable def binomialScale (r N : ℕ) : ℝ := (2 : ℝ)^r*((N : ℝ)+1)

noncomputable def binomialLeadingCoefficient (r k : ℕ) : ℝ :=
  leadingCoefficient r k/((k-1).factorial : ℝ)

noncomputable def factorialLeadingCoefficient (r k : ℕ) : ℝ :=
  (k.factorial : ℝ)*binomialLeadingCoefficient r k

lemma binomialArityMoment_nonneg (r k N : ℕ) : 0 ≤ binomialArityMoment r k N := by
  unfold binomialArityMoment
  positivity

lemma binomialScale_pos (r N : ℕ) : 0 < binomialScale r N := by
  unfold binomialScale
  positivity

lemma binomialArityMoment_prime_power (k N : ℕ) (hk : 1 ≤ k) :
    binomialArityMoment 0 k N = (HigherDivisors.tau k (2^N) : ℝ) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [binomialArityMoment,pow_zero,one_mul,Nat.succ_sub_one,
    HigherDivisors.tau_prime_pow j N 2 Nat.prime_two]

/-- The r=1 profile consists of genuine higher-divisor values. It is NOT
asserted that these integers have prime successors at arbitrarily large N. -/
lemma binomialArityMoment_one_profile (k N : ℕ) (hk : 1 ≤ k) :
    binomialArityMoment 1 k N = (HigherDivisors.tau k (2^N*3) : ℝ) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h3 : HigherDivisors.tau (j+1) 3 = j+1 := by
    simpa only [pow_one,Nat.add_comm 1 j,Nat.choose_succ_self_right] using
      HigherDivisors.tau_prime_pow j 1 3 Nat.prime_three
  rw [HigherDivisors.tau_mul_coprime _ ((by decide : Nat.Coprime 2 3).pow_left N),
    HigherDivisors.tau_prime_pow j N 2 Nat.prime_two,h3]
  simp only [binomialArityMoment,Nat.succ_sub_one,pow_one,Nat.cast_mul]
  ring

lemma choose_normalized_product (j N : ℕ) :
    ((N+j).choose j : ℝ)/((N : ℝ)+1)^j =
      (∏ i ∈ Finset.range j, (1+(i : ℝ)/((N : ℝ)+1)))/(j.factorial : ℝ) := by
  have hf : (0 : ℝ)<j.factorial := by positivity
  have hN : (0 : ℝ)<(N : ℝ)+1 := by positivity
  have hh := Nat.ascFactorial_eq_factorial_mul_choose N j
  rw [Nat.ascFactorial_eq_prod_range] at hh
  have hhR : (j.factorial : ℝ)*((N+j).choose j : ℝ) =
      ∏ i ∈ Finset.range j, ((N : ℝ)+1+(i : ℝ)) := by
    exact_mod_cast hh.symm
  have hprod : (∏ i ∈ Finset.range j, (1+(i : ℝ)/((N : ℝ)+1))) =
      (∏ i ∈ Finset.range j, ((N : ℝ)+1+(i : ℝ)))/((N : ℝ)+1)^j := by
    calc
      _ = ∏ i ∈ Finset.range j, ((N : ℝ)+1+(i : ℝ))/((N : ℝ)+1) := by
        apply Finset.prod_congr rfl
        intro i hi
        field_simp
      _ = _ := by rw [Finset.prod_div_distrib]; simp
  rw [hprod,← hhR]
  field_simp

lemma tendsto_normalized_choose (j : ℕ) :
    Tendsto (fun N : ℕ => ((N+j).choose j : ℝ)/((N : ℝ)+1)^j)
      atTop (𝓝 (1/(j.factorial : ℝ))) := by
  have hfactor (i : ℕ) : Tendsto (fun N : ℕ => 1+(i : ℝ)/((N : ℝ)+1)) atTop (𝓝 1) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply,Nat.cast_add,Nat.cast_one,add_zero] using
      (tendsto_const_nhds.add ht : Tendsto (fun N : ℕ => 1+(i : ℝ)/((N+1 : ℕ) : ℝ)) atTop (𝓝 (1+0)))
  have hp := (tendsto_finset_prod (Finset.range j) (fun i _ => hfactor i)).div_const (j.factorial : ℝ)
  simpa only [Finset.prod_const_one,choose_normalized_product] using hp

lemma binomial_normalized_eq (r k N : ℕ) :
    binomialArityMoment r k N/(binomialScale r N)^(k-1) =
      leadingCoefficient r k*(((N+(k-1)).choose (k-1) : ℝ)/((N : ℝ)+1)^(k-1)) := by
  unfold binomialArityMoment binomialScale leadingCoefficient
  rw [mul_pow,div_pow]
  rw [← pow_mul,← pow_mul,Nat.mul_comm (k-1) r]
  ring

theorem tendsto_binomial_normalized (r k : ℕ) :
    Tendsto (fun N : ℕ => binomialArityMoment r k N/(binomialScale r N)^(k-1))
      atTop (𝓝 (binomialLeadingCoefficient r k)) := by
  have hh := (tendsto_normalized_choose (k-1)).const_mul (leadingCoefficient r k)
  simpa only [binomial_normalized_eq,binomialLeadingCoefficient,mul_one_div] using hh

lemma binomialLeadingCoefficient_one (r : ℕ) : binomialLeadingCoefficient r 1 = 1 := by
  simp [binomialLeadingCoefficient,leadingCoefficient_one]

lemma binomialLeadingCoefficient_two (r : ℕ) : binomialLeadingCoefficient r 2 = 1 := by
  norm_num [binomialLeadingCoefficient,leadingCoefficient_two]

lemma binomialLeadingCoefficient_pos (r k : ℕ) (hk : 1 ≤ k) :
    0 < binomialLeadingCoefficient r k :=
  div_pos (leadingCoefficient_pos r k hk) (by positivity)

lemma factorialLeadingCoefficient_eq (r k : ℕ) (hk : 1 ≤ k) :
    factorialLeadingCoefficient r k = (k : ℝ)*leadingCoefficient r k := by
  have hfact : (k.factorial : ℝ) = (k : ℝ)*((k-1).factorial : ℝ) := by
    have hh := Nat.factorial_succ (k-1)
    rw [Nat.sub_add_cancel hk] at hh
    exact_mod_cast hh
  unfold factorialLeadingCoefficient binomialLeadingCoefficient
  rw [hfact]
  have hf : ((k-1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Unlike the Poisson model, this geometric decay includes the factorial
normalization that occurs in the sufficient moment criterion. -/
theorem tendsto_factorialLeadingCoefficient_div_geometric (r : ℕ) (θ : ℝ)
    (hθ : (1/2 : ℝ)^r < θ) :
    Tendsto (fun k : ℕ => factorialLeadingCoefficient r k/θ^k) atTop (𝓝 0) := by
  have hθ0 : 0 < θ := (pow_pos (by norm_num : (0 : ℝ)<1/2) r).trans hθ
  have hq0 : 0 ≤ (1/2 : ℝ)^r/θ := by positivity
  have hq1 : (1/2 : ℝ)^r/θ < 1 := (div_lt_one hθ0).mpr hθ
  have hh := (tendsto_pow_const_mul_const_pow_of_lt_one (r+1) hq0 hq1).const_mul ((2 : ℝ)^r)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [factorialLeadingCoefficient_eq r k hk,leadingCoefficient_geometric_form r k hk,div_pow,pow_succ]
  ring

/-- Positivity, the correct scale powers, and the first two leading
coefficients do not force the needed factorial-normalized high coefficients.
No such small-coefficient behavior is asserted for actual shifted primes. -/
theorem exists_binomial_model_with_factorial_geometric_deficit (θ : ℝ) (hθ : 0<θ) :
    ∃ r : ℕ, 1 ≤ r ∧ binomialLeadingCoefficient r 1 = 1 ∧
      binomialLeadingCoefficient r 2 = 1 ∧
      (∀ k : ℕ, 1 ≤ k → 0 < binomialLeadingCoefficient r k) ∧
      (∀ k : ℕ, Tendsto (fun N : ℕ => binomialArityMoment r k N/(binomialScale r N)^(k-1))
        atTop (𝓝 (binomialLeadingCoefficient r k))) ∧
      ∀ᶠ k : ℕ in atTop, (k.factorial : ℝ)*binomialLeadingCoefficient r k < θ^k := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1 : ℝ) / 2 < 1)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hpow.eventually (eventually_lt_nhds hθ))
  let r := max 1 R
  have hrt : (1/2 : ℝ)^r < θ := hR r (le_max_right _ _)
  refine ⟨r,le_max_left _ _,binomialLeadingCoefficient_one r,binomialLeadingCoefficient_two r,
    binomialLeadingCoefficient_pos r,tendsto_binomial_normalized r,?_⟩
  filter_upwards [(tendsto_factorialLeadingCoefficient_div_geometric r θ hrt).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with k hk
  exact (div_lt_one (pow_pos hθ k)).mp hk

end Erdos821.ArityModel
