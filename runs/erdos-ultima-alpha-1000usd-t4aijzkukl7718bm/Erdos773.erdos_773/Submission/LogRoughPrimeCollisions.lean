import Submission.RoughPrimeCollisions

/-!
A growing-cutoff obstruction to a proposed arithmetic carrier criterion.
Four distinct prime roots can have a nontrivial square-sum collision even
when all their pairwise norms have no odd prime divisor up to a fixed small
multiple of the logarithm of the root-height bound.
This is not a disproof of Erdős 773.
-/
namespace Erdos773.LogRoughPrimeCollisions
open Finset Filter LogRoughPrimeCarrier RoughPrimeCollisions PrimeColorCollisions
set_option maxHeartbeats 2000000

private lemma log_two_bounds : (1/2:ℝ)≤Real.log 2 ∧ Real.log 2≤1 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h1 h2 ⊢
  exact ⟨by linarith,by linarith⟩

private lemma entropy_budget {x : ℝ} (hx : 65537≤x) :
    32*x/Real.log x ≤ ((65536*x+1)*Real.log 2)/
      (512*Real.log ((65536*x+1)*Real.log 2)) := by
  have hx0 : 0<x := by linarith
  have hx1 : 1<x := by linarith
  have hL : 0<Real.log x := Real.log_pos hx1
  have hb := log_two_bounds
  let X := (65536*x+1)*Real.log 2
  have hXlow : 32768*x≤X := by dsimp [X]; nlinarith only [hb.1,hx0]
  have hXlarge : 1<X := by linarith only [hXlow,hx]
  have hLX : 0<Real.log X := Real.log_pos hXlarge
  have hXhigh : X≤x^2 := by
    dsimp [X]
    have h1 : (65536*x+1)*Real.log 2≤65536*x+1 := by nlinarith only [hb.2,hx0]
    nlinarith only [h1,hx]
  have hLXhigh : Real.log X≤2*Real.log x := by
    have hh := Real.log_le_log (by linarith : 0<X) hXhigh
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  change 32*x/Real.log x≤X/(512*Real.log X)
  apply (div_le_div_iff₀ hL (by positivity)).mpr
  have h1 := mul_le_mul_of_nonneg_left hLXhigh (show 0≤16384*x by positivity)
  have h2 := mul_le_mul_of_nonneg_right hXlow hL.le
  nlinarith only [h1,h2]

private lemma polynomial_decay :
    Tendsto (fun k : ℕ => (128*3*65537:ℝ)*(k:ℝ)^2*Real.exp (-Real.sqrt (k:ℝ)))
      atTop (nhds 0) := by
  have ht : Tendsto (fun k : ℕ => Real.sqrt (k:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4:ℝ) 1 (by norm_num)).comp ht
  have hh' := hh.const_mul (128*3*65537:ℝ)
  simp only [mul_zero] at hh'
  apply hh'.congr'
  filter_upwards with k
  dsimp only [Function.comp_def]
  rw [show (4:ℝ)=(4:ℕ) by norm_num, Real.rpow_natCast]
  have hs : Real.sqrt (k:ℝ)^4=(k:ℝ)^2 := by
    rw [show (4:ℕ)=2*2 by norm_num,pow_mul,Real.sq_sqrt (Nat.cast_nonneg k)]
  rw [hs]
  simp only [neg_mul,one_mul]
  ring

private lemma eventual_entropy :
    ∀ᶠ k : ℕ in atTop,
      128*(Fintype.card ((excluded (k:ℝ) → Bool) × Option (excluded (k:ℝ))) : ℝ)*
        ((65536*k:ℕ)+1 : ℝ)*
        Real.exp (-((((65536*k:ℕ):ℝ)+1)*Real.log 2)/
          (512*Real.log ((((65536*k:ℕ):ℝ)+1)*Real.log 2))) < 1 := by
  have hcount := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  have hlog := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ)<1)
  filter_upwards [hcount,hlog,polynomial_decay.eventually_lt_const (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop 65537] with k hc hl hd hk
  have hkR : (65537:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)<k := by linarith
  have hL : 0<Real.log (k:ℝ) := Real.log_pos (by linarith)
  have hslog : Real.log (k:ℝ)≤Real.sqrt (k:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL.le,
      abs_of_nonneg (Real.rpow_nonneg hk0.le _),one_mul,Real.sqrt_eq_rpow] using hl
  have hlog4 : Real.log 4+1≤4 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    norm_num at hh
    linarith
  let P := excluded (k:ℝ)
  have hcard : (P.card:ℝ)≤4*(k:ℝ)/Real.log (k:ℝ) := by
    have hcc : (Nat.primeCounting k:ℝ)≤(Real.log 4+1)*(k:ℝ)/Real.log (k:ℝ) := by
      simpa using hc
    calc
      _ ≤ (Nat.primeCounting k:ℝ) := by
        have hh := excluded_card (k:ℝ)
        simpa using (show ((excluded (k:ℝ)).card:ℝ)≤Nat.primeCounting ⌊(k:ℝ)⌋₊ by exact_mod_cast hh)
      _ ≤ _ := hcc.trans (by gcongr)
  have hcoarse : (P.card:ℝ)+1≤3*(k:ℝ) := by
    have hh : P.card≤k+1 := by
      dsimp [P,excluded]
      simpa using card_filter_le (s:=range (⌊(k:ℝ)⌋₊+1))
        (p:=fun p => p.Prime ∧ 2<p)
    have hh' : (P.card:ℝ)≤(k:ℝ)+1 := by exact_mod_cast hh
    linarith
  have hpow : (2:ℝ)^P.card≤Real.exp (4*(k:ℝ)/Real.log (k:ℝ)) := by
    calc
      _ = Real.exp ((P.card:ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left log_two_bounds.2 (Nat.cast_nonneg P.card : (0:ℝ)≤P.card)
        linarith only [hh,hcard]
  let E := (((65536*k:ℕ):ℝ)+1)*Real.log 2/
    (512*Real.log ((((65536*k:ℕ):ℝ)+1)*Real.log 2))
  have hE : 32*(k:ℝ)/Real.log (k:ℝ)≤E := by
    simpa only [E,Nat.cast_mul,Nat.cast_ofNat] using entropy_budget hkR
  have hsqrt : Real.sqrt (k:ℝ)≤28*(k:ℝ)/Real.log (k:ℝ) := by
    apply (le_div_iff₀ hL).mpr
    have hh := mul_le_mul_of_nonneg_left hslog (Real.sqrt_nonneg (k:ℝ))
    have hs := Real.sq_sqrt hk0.le
    nlinarith only [hh,hs,hk0]
  have he : Real.exp (4*(k:ℝ)/Real.log (k:ℝ))*Real.exp (-E)≤
      Real.exp (-Real.sqrt (k:ℝ)) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [mul_div_assoc] at hE hsqrt ⊢
    linarith only [hE,hsqrt]
  have hm : (((65536*k:ℕ):ℝ)+1)≤65537*(k:ℝ) := by push_cast; linarith
  have hκ : (Fintype.card ((P → Bool) × Option P):ℝ)=
      (2:ℝ)^P.card*((P.card:ℝ)+1) := by simp
  simp only [neg_div]
  change 128*(Fintype.card ((P → Bool) × Option P):ℝ)*
    (((65536*k:ℕ):ℝ)+1)*Real.exp (-E)<1
  rw [hκ]
  calc
    _ ≤ 128*(Real.exp (4*(k:ℝ)/Real.log (k:ℝ))*(3*(k:ℝ)))*
        (65537*(k:ℝ))*Real.exp (-E) := by gcongr
    _ = (128*3*65537:ℝ)*(k:ℝ)^2*
        (Real.exp (4*(k:ℝ)/Real.log (k:ℝ))*Real.exp (-E)) := by ring
    _ ≤ (128*3*65537:ℝ)*(k:ℝ)^2*Real.exp (-Real.sqrt (k:ℝ)) := by gcongr
    _ < 1 := hd

/-- Prime-root counterexamples to the logarithmic roughness criterion.
The four roots are at most 2^(65536*k+1), while every pairwise norm
(including repeated pairs) avoids all odd prime factors at most k. -/
theorem eventually_logarithmic_prime_collision :
    ∀ᶠ k : ℕ in atTop, ∃ B ⊆ sievePrimes (2^(65536*k)), B.card=4 ∧ FourCollision B (fun _ => ()) ∧
      ¬IsSidon ((B.image (fun n => n^2)) : Set ℕ) ∧
      ∀ a∈B, ∀ b∈B, ∀ p : ℕ, p.Prime → 2<p → p≤k → ¬p ∣ a^2+b^2 := by
  classical
  filter_upwards [eventual_entropy,eventually_ge_atTop 1] with k hc hk
  let P := excluded (k:ℝ)
  let κ := (P → Bool) × Option P
  have hh : FourCollision (sievePrimes (2^(65536*k))) (color P) :=
    prime_color_collision_of_entropy (65536*k) (by omega) κ (color P) hc
  obtain ⟨B,hB,hcard,hfour,hs,hr⟩ := rough_set_of_collision
    (sievePrimes (2^(65536*k))) P (fun _ ha => (mem_filter.mp ha).2.1)
    (fun _ hp => excluded_prime hp) hh
  refine ⟨B,hB,hcard,hfour,hs,?_⟩
  intro a ha b hb p hp hp2 hpk
  apply hr a ha b hb p
  exact (mem_excluded (Nat.cast_nonneg k)).mpr ⟨hp,hp2,by exact_mod_cast hpk⟩


end Erdos773.LogRoughPrimeCollisions
#print axioms Erdos773.LogRoughPrimeCollisions.eventually_logarithmic_prime_collision
