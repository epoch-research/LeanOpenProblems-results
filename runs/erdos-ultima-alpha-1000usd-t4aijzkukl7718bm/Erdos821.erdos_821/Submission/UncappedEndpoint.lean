import Submission.BlockCompositeScales

/-!
# Removing the fixed endpoint coefficient cap

For a fixed ambient exponential scale, n/phi(n) is bounded by a polynomial
in the scale parameter. Any positive exponential sieve-length margin
absorbs the endpoint correction. No condition t <= 5b is needed here.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma totient_ratio_le_exp_primeMass (n N : ℕ) (hn : 0<n) (hnN : n ≤ N) :
    (n : ℝ)/(n.totient : ℝ) ≤ Real.exp (primeTotientMass N) := by
  have hset : n.primeFactors ⊆ (N+1).primesBelow := by
    intro p hp
    have hpN := (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).trans hnN
    exact Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_of_mem_primeFactors hp⟩
  have hmass : (∑ p ∈ n.primeFactors, (p.totient : ℝ)⁻¹) ≤ primeTotientMass N :=
    sum_le_sum_of_subset_of_nonneg hset (fun p _ _ => by positivity)
  rw [Sieve.totient_ratio_eq_prime_product n hn]
  calc
    _ = ∏ p ∈ n.primeFactors, (1+(p.totient : ℝ)⁻¹) := by
      apply prod_congr rfl
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hpR : (1 : ℝ)<p := by exact_mod_cast hpr.one_lt
      have hne : (p : ℝ)-1 ≠ 0 := by linarith
      rw [Nat.totient_prime hpr,Nat.cast_sub hpr.one_lt.le,Nat.cast_one]
      field_simp
      ring
    _ ≤ ∏ p ∈ n.primeFactors, Real.exp ((p.totient : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp ((p.totient : ℝ)⁻¹)
    _ = Real.exp (∑ p ∈ n.primeFactors, (p.totient : ℝ)⁻¹) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hmass

lemma eventually_totient_ratio_ambient_scale (t : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop, ∀ a : ℕ, 0<a → a ≤ independentN t m →
      (a : ℝ)/(a.totient : ℝ) ≤ (2 : ℝ)^m := by
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 8
    (by norm_num : (1 : ℝ)<2)).const_mul (Real.exp 1024*(t : ℝ)^8)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ)<1)),
    eventually_ge_atTop 1] with m hpoly hm
  intro a ha haN
  have htm : 1 ≤ t*m := Nat.mul_pos ht hm
  have hb : Real.exp (primeTotientMass (independentN t m)) ≤
      Real.exp 1024*(t : ℝ)^8*(m : ℝ)^8 := by
    simpa only [independentN,progressionScaleN,mul_assoc,Nat.cast_mul,mul_pow]
      using Sieve.exp_primeTotientMass_scale_upper (t*m) htm
  apply (totient_ratio_le_exp_primeMass a (independentN t m) ha haN).trans (hb.trans ?_)
  have hp : (Real.exp 1024*(t : ℝ)^8*(m : ℝ)^8)/(2 : ℝ)^m ≤ 1 := by
    convert hpoly using 1
    ring
  exact (div_le_one (by positivity : (0 : ℝ)<(2 : ℝ)^m)).mp hp

namespace AnalyticSieve

def EndpointPairUpTo (X J : ℕ) : Prop :=
  ∀ a : ℕ, 0<a → a ≤ X →
    (primePairCofactorCount X a : ℝ) ≤
      (X : ℝ)/(450*(a.totient : ℝ)*((J : ℝ)*Real.log 2)^2)+
        ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1)

/-- Uniformity over all sieve lengths J>=m and all ambient X below the
fixed exponential scale replaces the old cap a<=2^(256J). -/
theorem eventually_endpoint_pair_ambient (t : ℕ) (ht : 1 ≤ t) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ, m ≤ J → ∀ X : ℕ,
      X ≤ independentN t m → EndpointPairUpTo X J := by
  obtain ⟨L,hL⟩ := eventually_atTop.mp Sieve.eventually_prime_pair_mixed_explicit_all
  filter_upwards [eventually_totient_ratio_ambient_scale t ht,eventually_ge_atTop (max 1 L)]
    with m hratio hm
  intro J hmJ X hXN a ha haX
  have hJ : 1 ≤ J := by omega
  have hpair := hL J (by omega)
  let D : ℝ := ((J : ℝ)*Real.log 2)^2
  have hJlog : (1/2 : ℝ) ≤ (J : ℝ)*Real.log 2 := by
    have hlog : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hD : 1 ≤ 450*D := by
    dsimp [D]
    nlinarith [sq_nonneg ((J : ℝ)*Real.log 2-1/2)]
  have hD0 : 0<D := by nlinarith
  have haR : (0 : ℝ)<a := by exact_mod_cast ha
  have hphi : (0 : ℝ)<a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have hN : ((X/a+1 : ℕ) : ℝ) ≤ (X : ℝ)/a+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using add_le_add Nat.cast_div_le (le_refl (1 : ℝ))
  have hb := hpair (X/a+1) a ha
  have hcorr : (a : ℝ)/(450*(a.totient : ℝ)*D) ≤ (2 : ℝ)^(16*J) := by
    calc
      _ = ((a : ℝ)/(a.totient : ℝ))/(450*D) := by ring
      _ ≤ (a : ℝ)/(a.totient : ℝ) := div_le_self (by positivity) hD
      _ ≤ (2 : ℝ)^m := hratio a ha (haX.trans hXN)
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmain : 2*((X/a+1 : ℕ) : ℝ)/(900*((a.totient : ℝ)/a*D)) ≤
      (X : ℝ)/(450*(a.totient : ℝ)*D)+(2 : ℝ)^(16*J) := by
    calc
      _ ≤ 2*((X : ℝ)/a+1)/(900*((a.totient : ℝ)/a*D)) := by gcongr
      _ = (X : ℝ)/(450*(a.totient : ℝ)*D)+(a : ℝ)/(450*(a.totient : ℝ)*D) := by
        field_simp
        ring
      _ ≤ _ := _root_.add_le_add le_rfl hcorr
  change (primePairCofactorCount X a : ℝ) ≤ _ at hb
  change (primePairCofactorCount X a : ℝ) ≤ (X : ℝ)/(450*(a.totient : ℝ)*D)+_
  linarith only [hb,hmain]

end AnalyticSieve
end Erdos821
