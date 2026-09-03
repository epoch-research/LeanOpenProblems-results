import Submission.TruncatedPrimeMass

/-!
# Scales for nearly sharp logarithmic moment powers

All orders and polynomial parameters are fixed before the scale tends to
infinity. The modulus level is small; no large-modulus estimate is assumed.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 4000000

def nearMomentC (w A : ℕ) : ℕ := 4096*w*(A+20)
def nearMomentR (w A m : ℕ) : ℕ := nearMomentC w A*(m+5)
def nearMomentB (w A m : ℕ) : ℕ := nearMomentR w A m*(logMomentScale m)^(A+19)
def nearMomentT (w A m : ℕ) : ℕ := 64*nearMomentR w A m*(logMomentScale m)^(A+20)
def nearMomentQ (w A m : ℕ) : ℕ := progressionScaleN (nearMomentB w A m*logMomentScale m)
def nearMomentX (w A m : ℕ) : ℕ := progressionScaleN (nearMomentT w A m*logMomentScale m)
noncomputable def nearMomentP (A m : ℕ) : Finset ℕ := powerPrimePool (A+20) (logMomentScale m)
noncomputable def nearMomentPool (A m r : ℕ) : Finset ℕ := primeSubsetModuli (nearMomentP A m) r

lemma nearMomentR_pos (w A m : ℕ) (hw : 1 ≤ w) : 0 < nearMomentR w A m := by
  unfold nearMomentR nearMomentC
  positivity

lemma nearMomentT_pos (w A m : ℕ) (hw : 1 ≤ w) : 0 < nearMomentT w A m := by
  have hR := nearMomentR_pos w A m hw
  unfold nearMomentT logMomentScale
  positivity

lemma nearMoment_level_bound (w A m : ℕ) : 32*nearMomentB w A m ≤ nearMomentT w A m := by
  have hE : 1 ≤ logMomentScale m := (by decide : 1 ≤ 32).trans (logMomentScale_ge m)
  unfold nearMomentB nearMomentT
  rw [show A+20=(A+19)+1 by omega,pow_succ _ (A+19)]
  have h := Nat.le_mul_of_pos_right (32*nearMomentR w A m*(logMomentScale m)^(A+19)) hE
  calc
    _ ≤ 32*(nearMomentR w A m*(logMomentScale m)^(A+19)*logMomentScale m) := by
      simpa only [mul_assoc] using h
    _ ≤ 64*(nearMomentR w A m*(logMomentScale m)^(A+19)*logMomentScale m) :=
      Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring

lemma nearMomentPool_bounds (w A m r : ℕ) (hr : r ≤ nearMomentR w A m) :
    ∀ d ∈ nearMomentPool A m r, 0 < d ∧ d ≤ nearMomentQ w A m := by
  intro d hd
  have hP : ∀ p ∈ nearMomentP A m, p.Prime ∧ progressionScaleN (logMomentScale m) ≤ p ∧
      p ≤ progressionScaleN ((logMomentScale m)^(A+20)) := powerPrimePool_prime_bounds _ _
  refine ⟨primeSubsetModuli_pos _ (fun p hp => (hP p hp).1) hd,?_⟩
  have h := primeSubsetModuli_le _ _ (fun p hp => (hP p hp).2.2) hd
  apply (h.trans (Nat.pow_le_pow_right (by unfold progressionScaleN; positivity) hr)).trans_eq
  simp only [nearMomentQ,nearMomentB,progressionScaleN,← pow_mul]
  apply congrArg (fun e : ℕ => (2 : ℕ)^e)
  rw [show A+20=(A+19)+1 by omega,pow_succ _ (A+19)]
  ring

lemma nearMomentPool_card_le (w A m r : ℕ) (hr : r ≤ nearMomentR w A m) :
    (nearMomentPool A m r).card ≤ nearMomentQ w A m := by
  have hsub : nearMomentPool A m r ⊆ Icc 1 (nearMomentQ w A m) :=
    fun d hd => mem_Icc.mpr (nearMomentPool_bounds w A m r hr d hd)
  exact (card_le_card hsub).trans_eq (by simp)

lemma nearMomentPool_rough (A m r : ℕ) :
    ∀ d ∈ nearMomentPool A m r, ∀ c ∈ d.divisors.erase 1,
      progressionScaleN (logMomentScale m) ≤ c := by
  intro d hd c hc
  exact primeSubsetModuli_rough _ _ (fun p hp =>
    ⟨(powerPrimePool_prime_bounds _ _ p hp).1,(powerPrimePool_prime_bounds _ _ p hp).2.1⟩) hd hc

lemma nearMoment_weight_bound (w A m r : ℕ) (hw : 1 ≤ w) (hr : r ≤ nearMomentR w A m) :
    w^r ≤ (logMomentScale m)^(w*nearMomentC w A) := by
  calc
    _ ≤ w^(nearMomentR w A m) := Nat.pow_le_pow_right hw hr
    _ ≤ (2^w)^(nearMomentR w A m) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = _ := by
      simp only [nearMomentR,logMomentScale,← pow_mul]
      apply congrArg (fun e : ℕ => (2 : ℕ)^e)
      ring

lemma nearMoment_combined_error_bound (w A m r : ℕ) (hw : 1 ≤ w)
    (hr : r ≤ nearMomentR w A m) :
    (∑ d ∈ nearMomentPool A m r, compositeProgressionError d (nearMomentX w A m))+
      2*(nearMomentQ w A m : ℝ)*Real.sqrt (nearMomentX w A m)*Real.log (nearMomentX w A m) ≤
      1000000000000000*(64*(nearMomentC w A : ℝ)+1)^6*
        ((logMomentScale m : ℝ)+1)^(6*(A+22)) *
          (2 : ℝ)^((64*nearMomentT w A m-1)*logMomentScale m) := by
  let E := logMomentScale m
  let C := nearMomentC w A
  let t := nearMomentT w A m
  have hE : 1 ≤ E := (by decide : 1 ≤ 32).trans (logMomentScale_ge m)
  have h := small_rough_pool_combined_error (nearMomentPool A m r) (nearMomentB w A m) t E
    (nearMomentT_pos w A m hw) hE (nearMoment_level_bound w A m)
    (nearMomentPool_bounds w A m r hr) (nearMomentPool_rough A m r)
  have hCE : nearMomentR w A m ≤ C*E :=
    Nat.mul_le_mul_left C Nat.lt_two_pow_self.le
  have hCEr : (nearMomentR w A m : ℝ) ≤ C*(E : ℝ) := by exact_mod_cast hCE
  have hz : ((t : ℝ)+1)*((E : ℝ)+1) ≤ (64*(C : ℝ)+1)*((E : ℝ)+1)^(A+22) := by
    have ht : (t : ℝ) ≤ 64*(C : ℝ)*((E : ℝ)+1)^(A+21) := by
      calc
        (t : ℝ) = 64*(nearMomentR w A m : ℝ)*(E : ℝ)^(A+20) := by simp only [t,nearMomentT,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,E]
        _ ≤ 64*((C : ℝ)*(E : ℝ))*(E : ℝ)^(A+20) := by gcongr
        _ = 64*(C : ℝ)*(E : ℝ)^(A+21) := by rw [show A+21=(A+20)+1 by omega,pow_succ]; ring
        _ ≤ _ := by gcongr; linarith
    have hone : (1 : ℝ) ≤ ((E : ℝ)+1)^(A+21) := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) E])
    have ht' : (t : ℝ)+1 ≤ (64*(C : ℝ)+1)*((E : ℝ)+1)^(A+21) := by nlinarith only [ht,hone]
    have hh := mul_le_mul_of_nonneg_right ht' (show 0 ≤ (E : ℝ)+1 by positivity)
    rw [show A+22=(A+21)+1 by omega,pow_succ]
    nlinarith only [hh]
  apply h.trans
  calc
    _ ≤ 1000000000000000*((64*(C : ℝ)+1)*((E : ℝ)+1)^(A+22))^6*
        (2 : ℝ)^((64*t-1)*E) := by gcongr
    _ = _ := by rw [mul_pow,← pow_mul]; simp only [mul_comm (A+22) 6]; ring

lemma eventually_nearMoment_weighted_error_small (w A : ℕ) (hw : 1 ≤ w) :
    ∀ᶠ m : ℕ in atTop, ∀ r ≤ nearMomentR w A m,
      (w : ℝ)^r*((∑ d ∈ nearMomentPool A m r, compositeProgressionError d (nearMomentX w A m))+
        2*(nearMomentQ w A m : ℝ)*Real.sqrt (nearMomentX w A m)*Real.log (nearMomentX w A m)) ≤
          (nearMomentX w A m : ℝ)/16 := by
  let C := nearMomentC w A
  let D := 16*1000000000000000*(64*C+1)^6
  let n := w*C+6*(A+22)
  have hevent := logMomentScale_tendsto.eventually (eventually_nat_poly_le_two_pow 1 D n)
  filter_upwards [hevent] with m hm r hr
  let E := logMomentScale m
  let F : ℝ := (2 : ℝ)^((64*nearMomentT w A m-1)*E)
  have hpoly : (D : ℝ)*((E : ℝ)+1)^n ≤ (2 : ℝ)^E := by
    exact_mod_cast (show D*(E+1)^n ≤ 2^E by simpa only [one_mul] using hm)
  have hwR : (w : ℝ)^r ≤ ((E : ℝ)+1)^(w*C) := by
    have h : (w : ℝ)^r ≤ (E : ℝ)^(w*C) := by exact_mod_cast nearMoment_weight_bound w A m r hw hr
    exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _)
  have herr := nearMoment_combined_error_bound w A m r hw hr
  have hscaled := mul_le_mul hwR herr (by
    exact add_nonneg (sum_nonneg (fun d hd => (abs_nonneg _).trans
      (composite_progression_discrepancy d (nearMomentX w A m)
        (nearMomentPool_bounds w A m r hr d hd).1))) (by positivity)) (by positivity)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  calc
    _ ≤ (((E : ℝ)+1)^(w*C)*(1000000000000000*(64*(C : ℝ)+1)^6*
        ((E : ℝ)+1)^(6*(A+22))*F))*16 := mul_le_mul_of_nonneg_right hscaled (by norm_num)
    _ = ((D : ℝ)*((E : ℝ)+1)^n)*F := by
      simp only [D,n,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,pow_add]
      ring
    _ ≤ (2 : ℝ)^E*F := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by
      simp only [F,nearMomentX,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
      apply congrArg (fun e : ℕ => (2 : ℝ)^e)
      have ht := nearMomentT_pos w A m hw
      have hs := Nat.sub_add_cancel (show 1 ≤ 64*nearMomentT w A m by omega)
      change E+(64*nearMomentT w A m-1)*E = 64*(nearMomentT w A m*E)
      nlinarith only [hs]

lemma eventually_nearMomentR_add_one_le_scale (w A : ℕ) :
    ∀ᶠ m : ℕ in atTop, nearMomentR w A m+1 ≤ logMomentScale m := by
  have hevent := eventually_nat_poly_le_two_pow 5 (nearMomentC w A+1) 1
  filter_upwards [hevent,eventually_ge_atTop 1] with m hm hm1
  have h : nearMomentR w A m+1 ≤ (nearMomentC w A+1)*(5*m+1) := by
    unfold nearMomentR
    nlinarith [Nat.mul_le_mul_left (nearMomentC w A) (show m+5 ≤ 5*m+1 by omega)]
  apply (h.trans (by simpa only [pow_one] using hm)).trans
  exact Nat.pow_le_pow_right (by decide) (by omega)

end Erdos821
