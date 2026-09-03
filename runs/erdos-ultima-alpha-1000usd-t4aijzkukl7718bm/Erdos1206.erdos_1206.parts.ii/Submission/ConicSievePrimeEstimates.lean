import Submission.ConicPrimeBlockEstimates
import Submission.ConicMixedLocalSieve

/-! The conic's finite Selberg estimate with its prime-mass hypotheses
discharged quantitatively. -/
namespace Erdos1206.ConicSievePrimeEstimates
open Finset Filter ConicPrimeBlockEstimates FinitePrimeMass QuadraticPrimePrefixBounds
open ConicMixedDirichletCharacter SquarefreeConicCharacterScore SquarefreeConicFamily
open ConicPrimeCharacterScore
open scoped Topology Classical

noncomputable def reciprocalSquares : ℝ := ∑' p : Nat.Primes, 1/(p:ℝ)^2

lemma summable_reciprocalSquares : Summable (fun p : Nat.Primes => 1/(p:ℝ)^2) := by
  have hh : Summable (fun p : Nat.Primes => (p:ℝ)^(-2:ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have he (p : Nat.Primes) : (p:ℝ)^(-2:ℝ)=1/(p:ℝ)^2 := by
    rw [Real.rpow_neg (show (0:ℝ) ≤ p by positivity),Real.rpow_two,one_div]
  simpa only [he] using hh

lemma block_reciprocalSquares (y : ℝ) :
    (∑ p ∈ block y, 1/(p:ℝ)^2) ≤ reciprocalSquares := by
  rw [sum_block]
  exact Summable.sum_le_tsum _ (fun p _ => by positivity) summable_reciprocalSquares

noncomputable def rho (p : ℕ) : ℝ := (4*(p:ℝ)-3)/(p:ℝ)^2

lemma rho_eq {p : ℕ} (hp : 0 < p) : rho p=4/(p:ℝ)-3/(p:ℝ)^2 := by
  dsimp only [rho]
  have hpR : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

lemma rho_le {p : ℕ} (hp : 0 < p) : rho p ≤ 4/(p:ℝ) := by
  rw [rho_eq hp]
  have : (0:ℝ) ≤ 3/(p:ℝ)^2 := by positivity
  linarith

lemma thinned_mass_eq (y : ℝ) :
    (∑ p ∈ block y, (7/8:ℝ)*rho p)=
      (7/2)*(∑ p ∈ block y, 1/(p:ℝ))-(21/8)*(∑ p ∈ block y, 1/(p:ℝ)^2) := by
  rw [mul_sum,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  rw [rho_eq (mem_block hp).1.pos]
  ring

lemma thinned_log_moment_le (y : ℝ) :
    2*(∑ p ∈ block y, ((7/8:ℝ)*rho p)*Real.log p) ≤
      7*(∑ p ∈ block y, Real.log (p:ℝ)/(p:ℝ)) := by
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro p hp
  have hpprime := (mem_block hp).1
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
  have hh := mul_le_mul_of_nonneg_right (rho_le hpprime.pos) hlog
  have he : 4/(p:ℝ)*Real.log p=4*(Real.log (p:ℝ)/(p:ℝ)) := by ring
  rw [he] at hh
  nlinarith only [hh]

/-- This supplies both arithmetic hypotheses of the finite sieve, uniformly
for every sufficiently large real prime cutoff y. -/
theorem eventually_thinned_bounds :
    ∃ E T : ℝ, 0 < T ∧ ∀ᶠ y : ℝ in atTop,
      (7/4)*Real.log (Real.log y)-E ≤ ∑ p ∈ block y, (7/8:ℝ)*rho p ∧
      2*(∑ p ∈ block y, ((7/8:ℝ)*rho p)*Real.log p) ≤ T*Real.log y := by
  obtain ⟨C,D,hD,hbound⟩ := eventually_block_bounds
  refine ⟨(7/2)*C+(21/8)*reciprocalSquares,7*D,by positivity,?_⟩
  filter_upwards [hbound] with y hy
  have hsq := block_reciprocalSquares y
  have hmoment := thinned_log_moment_le y
  rw [thinned_mass_eq]
  constructor
  · linarith [hy.1]
  · nlinarith only [hmoment,hy.2.2]

noncomputable def smallParameters (y : ℝ) (N k : ℕ) : Finset (ℕ × ℕ) :=
  ((range N) ×ˢ (range N)).filter (fun x => 0 < x.2 ∧
    mixedMass (block y) χ ψ (F 0 x.1 x.2) (F 1 x.1 x.2) (F 2 x.1 x.2) (F 3 x.1 x.2) ≤ k)

/-- Explicit upper sieve with all prime-distribution and CRT errors retained.
The exponent 7/4 is strictly greater than one. -/
theorem eventually_small_parameters_count :
    ∃ E T : ℝ, 0 < T ∧ ∀ᶠ y : ℝ in atTop,
      ∀ N z k : ℕ, 1 < z → T*Real.log y ≤ Real.log z →
        ((smallParameters y N k).card:ℝ) ≤
          (8:ℝ)^k*(2*(N:ℝ)^2*Real.exp (E-(7/4)*Real.log (Real.log y))+
            2*(N:ℝ)*(z:ℝ)^6+(z:ℝ)^8) := by
  obtain ⟨E,T,hT,hbound⟩ := eventually_thinned_bounds
  refine ⟨E,T,hT,?_⟩
  filter_upwards [hbound] with y hy
  intro N z k hz hmoment
  have hh := ConicMixedLocalSieve.small_mixedMass_count (block y)
    (fun p hp => mem_block hp) N z k hz (by norm_num : (0:ℝ) < 7/8)
    (by norm_num : (7/8:ℝ) ≤ 1) (hy.2.trans hmoment)
  change ((smallParameters y N k).card:ℝ)*(1-(7/8:ℝ))^k ≤
    2*(N:ℝ)^2*Real.exp (-(∑ p ∈ block y, (7/8:ℝ)*rho p))+
      2*(N:ℝ)*(z:ℝ)^6+(z:ℝ)^8 at hh
  have he := Real.exp_le_exp.mpr (show -(∑ p ∈ block y, (7/8:ℝ)*rho p) ≤
      E-(7/4)*Real.log (Real.log y) by linarith [hy.1])
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*(N:ℝ)^2 by positivity)
  have htotal : ((smallParameters y N k).card:ℝ)*(1/8:ℝ)^k ≤
      2*(N:ℝ)^2*Real.exp (E-(7/4)*Real.log (Real.log y))+
        2*(N:ℝ)*(z:ℝ)^6+(z:ℝ)^8 := by
    norm_num only [show (1:ℝ)-7/8=1/8 by norm_num] at hh
    linarith
  have hmul := mul_le_mul_of_nonneg_left htotal (show 0 ≤ (8:ℝ)^k by positivity)
  have hc : (8:ℝ)^k*(((smallParameters y N k).card:ℝ)*(1/8:ℝ)^k)=
      ((smallParameters y N k).card:ℝ) := by
    rw [mul_left_comm,←mul_pow]
    norm_num
  rwa [hc] at hmul

#print axioms summable_reciprocalSquares
#print axioms eventually_thinned_bounds
#print axioms eventually_small_parameters_count
end Erdos1206.ConicSievePrimeEstimates
