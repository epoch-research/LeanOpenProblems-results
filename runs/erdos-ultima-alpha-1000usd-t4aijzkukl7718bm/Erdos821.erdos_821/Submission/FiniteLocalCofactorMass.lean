import Submission.FiniteLocalAverage
import Submission.FiniteLocalPrimePair
import Submission.ThreeCofactorMass

/-! # Corrected exponential cofactor blocks for a fixed retained prime pool -/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Sieve
open AnalyticSieve
set_option maxHeartbeats 3000000

theorem finite_even_reciprocal_totient_interval (D A B : ℕ) (hD : 2 ≤ D) (hDB : D ≤ B) (hA : 0<A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (2*A+1) (2*B) with Even n, finiteLocalCorrection (retainedPrimePool D) n/(n.totient : ℝ)) ≤
      localAverageConstant D*Real.log ((B : ℝ)/A)+Real.exp (primeTotientMass B)/(A : ℝ) := by
  rw [sum_even_interval_eq_double]
  exact finite_corrected_double_interval D A B hD hDB hA hAB

noncomputable def finiteEvenBlockMass (D a b m : ℕ) : ℝ :=
  ∑ n ∈ Icc (2^(64*a*m)+1) (2^(64*b*m)) with Even n,
    finiteLocalCorrection (retainedPrimePool D) n/(n.totient : ℝ)

lemma finiteEvenBlockMass_upper (D a b m : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : 1 ≤ m) (hD : 2 ≤ D) (hDm : D ≤ m) :
    finiteEvenBlockMass D a b m ≤
      localAverageConstant D*64*((b : ℝ)-a)*m*Real.log 2 +
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
  have hDB : D ≤ B := by
    apply hDm.trans
    apply (Nat.lt_two_pow_self (n := m)).le.trans
    apply Nat.pow_le_pow_right (by decide)
    dsimp only [B]
    have hs := Nat.sub_add_cancel hbexp
    nlinarith only [hbm,hm,hs]
  have hh := finite_even_reciprocal_totient_interval D A B hD hDB hA hAB
  rw [htwoA,htwoB,hlog] at hh
  change finiteEvenBlockMass D a b m ≤ _ at hh
  exact hh.trans (by nlinarith only [herr])

lemma eventually_finiteEvenBlockMass_upper (D a b : ℕ) (hD : 2 ≤ D) (ha : 1 ≤ a) (hab : a ≤ b)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      finiteEvenBlockMass D a b m ≤ localAverageConstant D*64*((b : ℝ)-a)*m*Real.log 2+η := by
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 8
    (by norm_num : (1 : ℝ) < 2)).const_mul (Real.exp 1024*(b : ℝ)^8)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds hη),eventually_ge_atTop (max 1 D)] with m he hm
  exact (finiteEvenBlockMass_upper D a b m ha hab ((le_max_left _ _).trans hm) hD ((le_max_right _ _).trans hm)).trans (_root_.add_le_add le_rfl he)



end Erdos821.Sieve
namespace Erdos821.AnalyticSieve

lemma eventually_cofactorBlock_finite_mass (D j : ℕ) (hD : 2 ≤ D) :
    ∀ᶠ m : ℕ in atTop,
      (∑ k ∈ cofactorBlock j m with Even k, Sieve.finiteLocalCorrection (Sieve.retainedPrimePool D) k/(k.totient : ℝ)) ≤
        Sieve.localAverageConstant D*(1+64*(m : ℝ)*Real.log 2) := by
  have hC := Sieve.localAverageConstant_one_le D hD
  by_cases hj : j=0
  · subst j
    filter_upwards [eventually_ge_atTop (max 1 D)] with m hm
    have hm1 : 1 ≤ m := (le_max_left _ _).trans hm
    have hmD : D ≤ m := (le_max_right _ _).trans hm
    let B := 2^(64*m-1)
    have he : 2*B=2^(64*m) := Sieve.two_mul_pow_pred_eq _ (by omega)
    have hset : cofactorBlock 0 m = Icc (2*0+1) (2*B) := by
      rw [he]
      ext k
      simp only [cofactorBlock,cofactorBlockEndpoint_zero,cofactorBlockEndpoint_succ,
        zero_add,mul_one,mul_zero,mem_Ioc,mem_Icc]
      omega
    rw [hset,Sieve.sum_even_interval_eq_double]
    simp only [zero_add]
    have hDB : D ≤ B := by
      apply hmD.trans
      apply (Nat.lt_two_pow_self (n := m)).le.trans
      apply Nat.pow_le_pow_right (by decide)
      dsimp only [B]
      omega
    apply (Sieve.finite_corrected_double_prefix D B hD hDB).trans
    have hH := harmonic_le_one_add_log B
    have hlog : Real.log (B : ℝ) ≤ 64*(m : ℝ)*Real.log 2 := by
      simp only [B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
      have hh : ((64*m-1 : ℕ) : ℝ) ≤ 64*(m : ℝ) := by exact_mod_cast Nat.sub_le (64*m) 1
      exact mul_le_mul_of_nonneg_right hh (Real.log_pos (by norm_num)).le
    exact mul_le_mul_of_nonneg_left (hH.trans (by linarith only [hlog])) (by linarith only [hC])
  · filter_upwards [Sieve.eventually_finiteEvenBlockMass_upper D j (j+1) hD (by omega)
      (Nat.le_succ j) 1 (by norm_num)] with m hm
    have hset : cofactorBlock j m = Icc (2^(64*j*m)+1) (2^(64*(j+1)*m)) := by
      ext k
      simp only [cofactorBlock,cofactorBlockEndpoint,if_neg hj,
        if_neg (Nat.succ_ne_zero j),mem_Ioc,mem_Icc]
      omega
    rw [hset]
    change Sieve.finiteEvenBlockMass D j (j+1) m ≤ _
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left] at hm
    nlinarith only [hm,hC]

lemma eventually_cofactorBlock_finite_mass_all (D h : ℕ) (hD : 2 ≤ D) :
    ∀ᶠ m : ℕ in atTop, ∀ j ∈ range h,
      (∑ k ∈ cofactorBlock j m with Even k, Sieve.finiteLocalCorrection (Sieve.retainedPrimePool D) k/(k.totient : ℝ)) ≤
        Sieve.localAverageConstant D*(1+64*(m : ℝ)*Real.log 2) := by
  rw [eventually_all_finset]
  exact fun j _ => eventually_cofactorBlock_finite_mass D j hD


end Erdos821.AnalyticSieve
