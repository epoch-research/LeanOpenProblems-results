import Submission.ThreeIntervalTotient
import Submission.RestrictedHarmonicWeights

/-! # Corrected reciprocal-totient mass on complete exponential cofactor blocks -/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Sieve
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma corrected_reciprocal_totient_double_prefix (B : ℕ) :
    (∑ n ∈ Icc 1 B, threeCorrection (2*n)/((2*n).totient : ℝ)) ≤
      (39/35 : ℝ)*(harmonic B : ℝ) := by
  let Q := (B+1).primesBelow.erase 2
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime := (Nat.mem_primesBelow.mp (mem_erase.mp hp).2).2
  have heq (n : ℕ) (hn : n ∈ Icc 1 B) :
      threeCorrection (2*n)/((2*n).totient : ℝ) =
        (3/4 : ℝ)*(∏ p ∈ Q with p ∣ n, (1+threePrimeWeight p))/(n : ℝ) := by
    have hn0 : 0<n := by have := (mem_Icc.mp hn).1; omega
    rw [corrected_reciprocal_totient_double_eq n hn0]
    have hset : n.primeFactors.erase 2 = Q.filter (fun p => p ∣ n) := by
      ext p
      constructor
      · intro hp
        obtain ⟨hp2,hpn⟩ := mem_erase.mp hp
        have hpl : p ≤ n := Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hpn)
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hp2,Nat.mem_primesBelow.mpr
          ⟨by have := (mem_Icc.mp hn).2; omega,Nat.prime_of_mem_primeFactors hpn⟩⟩,
          Nat.dvd_of_mem_primeFactors hpn⟩
      · intro hp
        obtain ⟨hpQ,hpn⟩ := mem_filter.mp hp
        exact mem_erase.mpr ⟨(mem_erase.mp hpQ).1,(hQ p hpQ).mem_primeFactors hpn hn0.ne'⟩
    rw [hset]
  have havg := mul_le_mul_of_nonneg_left (harmonic_average_restricted_prime_product B Q hQ
    threePrimeWeight (fun p hp => threePrimeWeight_nonneg p (hQ p hp))) (by norm_num : (0 : ℝ) ≤ 3/4)
  have hH : 0 ≤ (harmonic B : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    _ = (3/4 : ℝ)*∑ n ∈ Icc 1 B, (∏ p ∈ Q with p ∣ n, (1+threePrimeWeight p))/(n : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl (fun n hn => by rw [heq n hn]; ring)
    _ ≤ _ := havg
    _ = (harmonic B : ℝ)*((3/4 : ℝ)*(∏ p ∈ Q, (1+threePrimeWeight p/(p : ℝ)))) := by ring
    _ ≤ (harmonic B : ℝ)*(39/35 : ℝ) :=
      mul_le_mul_of_nonneg_left (corrected_odd_euler_product_upper B) hH
    _ = _ := by ring

lemma sum_even_interval_eq_double (A B : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc (2*A+1) (2*B) with Even n, f n) =
      ∑ n ∈ Icc (A+1) B, f (2*n) := by
  have hset : (Icc (2*A+1) (2*B)).filter (fun n => Even n) =
      (Icc (A+1) B).image (fun n => 2*n) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnI,hne⟩ := mem_filter.mp hn
      have hmod := Nat.even_iff.mp hne
      refine mem_image.mpr ⟨n/2,mem_Icc.mpr ⟨?_,?_⟩,?_⟩ <;>
        have := mem_Icc.mp hnI <;> omega
    · intro hn
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
      have hm' := mem_Icc.mp hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,⟨m,by omega⟩⟩
  rw [hset,sum_image (by intro a ha b hb he; dsimp at he; omega)]

theorem corrected_even_reciprocal_totient_interval (A B : ℕ) (hA : 0<A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (2*A+1) (2*B) with Even n, threeCorrection n/(n.totient : ℝ)) ≤
      (39/35 : ℝ)*Real.log ((B : ℝ)/A)+Real.exp (primeTotientMass B)/(A : ℝ) := by
  rw [sum_even_interval_eq_double]
  exact corrected_reciprocal_totient_double_interval A B hA hAB

noncomputable def correctedEvenBlockMass (a b m : ℕ) : ℝ :=
  ∑ n ∈ Icc (2^(64*a*m)+1) (2^(64*b*m)) with Even n,
    threeCorrection n/(n.totient : ℝ)

lemma correctedEvenBlockMass_upper (a b m : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : 1 ≤ m) :
    correctedEvenBlockMass a b m ≤
      (39/35 : ℝ)*64*((b : ℝ)-a)*m*Real.log 2 +
        (Real.exp 1024*(b : ℝ)^8)*((m : ℝ)^8/(2 : ℝ)^m) := by
  let A : ℕ := 2^(64*a*m-1)
  let B : ℕ := 2^(64*b*m-1)
  have ham : m ≤ a*m := Nat.le_mul_of_pos_left m ha
  have hbm : m ≤ b*m := ham.trans (Nat.mul_le_mul_right m hab)
  have haexp : 1 ≤ 64*a*m := by nlinarith only [ham,hm]
  have hbexp : 1 ≤ 64*b*m := by nlinarith only [hbm,hm]
  have hAB : A ≤ B := by
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_right m (Nat.mul_le_mul_left 64 hab)) 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have htwoA : 2*A=2^(64*a*m) := two_mul_pow_pred_eq _ haexp
  have htwoB : 2*B=2^(64*b*m) := two_mul_pow_pred_eq _ hbexp
  have hlog : Real.log ((B : ℝ)/A) = 64*((b : ℝ)-a)*m*Real.log 2 := by
    rw [Real.log_div (by exact_mod_cast hB.ne' : (B : ℝ) ≠ 0)
      (by exact_mod_cast hA.ne' : (A : ℝ) ≠ 0)]
    simp only [A,B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,
      Nat.cast_sub haexp,Nat.cast_sub hbexp,Nat.cast_mul,Nat.cast_one]
    ring
  have hBcap : B ≤ progressionScaleN (b*m) := by
    change 2^(64*b*m-1) ≤ 2^(64*(b*m))
    apply Nat.pow_le_pow_right (by decide)
    simpa only [mul_assoc] using Nat.sub_le (64*b*m) 1
  have hmass : Real.exp (primeTotientMass B) ≤ Real.exp 1024*(b : ℝ)^8*(m : ℝ)^8 := by
    have h := (Real.exp_le_exp.mpr (primeTotientMass_mono hBcap)).trans
      (exp_primeTotientMass_scale_upper (b*m) (by omega))
    simpa only [Nat.cast_mul,mul_pow,mul_assoc] using h
  have hApow : (2 : ℝ)^m ≤ A := by
    have hn : 2^m ≤ A := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp only [A]
      have hs := Nat.sub_add_cancel haexp
      nlinarith only [ham,hm,hs]
    exact_mod_cast hn
  have herr : Real.exp (primeTotientMass B)/(A : ℝ) ≤
      (Real.exp 1024*(b : ℝ)^8)*((m : ℝ)^8/(2 : ℝ)^m) := by
    calc
      _ ≤ (Real.exp 1024*(b : ℝ)^8*(m : ℝ)^8)/(2 : ℝ)^m := by
        exact div_le_div₀ (by positivity) hmass (by positivity) hApow
      _ = _ := by ring
  have hh := corrected_even_reciprocal_totient_interval A B hA hAB
  rw [htwoA,htwoB,hlog] at hh
  change correctedEvenBlockMass a b m ≤ _ at hh
  exact hh.trans (by nlinarith only [herr])

lemma eventually_correctedEvenBlockMass_upper (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      correctedEvenBlockMass a b m ≤ (39/35 : ℝ)*64*((b : ℝ)-a)*m*Real.log 2+η := by
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 8
    (by norm_num : (1 : ℝ) < 2)).const_mul (Real.exp 1024*(b : ℝ)^8)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds hη),eventually_ge_atTop 1] with m he hm
  exact (correctedEvenBlockMass_upper a b m ha hab hm).trans (_root_.add_le_add le_rfl he)


end Erdos821.Sieve
