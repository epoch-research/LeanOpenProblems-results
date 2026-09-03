import Submission.LogLogMomentScales

/-!
# Critical logarithmic moment powers with a log-log loss

The divisor order is fixed while the auxiliary construction parameter grows.
The explicit loss still tends to infinity, so this does not provide a positive
coefficient at the critical power and does not settle Erdős 821.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 5000000

lemma loglogMomentE_square (m : ℕ) :
    loglogMomentE m = (32*loglogMomentA m)^2 := by
  rw [loglogMomentE_eq]
  unfold loglogMomentA
  rw [show (32 : ℕ)=2^5 by decide,← pow_add,← pow_mul]
  apply congrArg (fun e : ℕ => (2 : ℕ)^e)
  ring

lemma log_loglogMomentE_lower (m : ℕ) :
    (m : ℝ)+5 ≤ Real.log (loglogMomentE m : ℝ) := by
  rw [loglogMomentE_eq,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h := mul_le_mul_of_nonneg_right htwo (show 0 ≤ 2*(m : ℝ)+10 by positivity)
  push_cast
  nlinarith only [h]

lemma loglogMoment_log_log_lower (w m : ℕ) (hw : 1 ≤ w) (hm : 32 ≤ m) :
    32*(loglogMomentA m : ℝ) ≤ Real.log (Real.log (loglogMomentX w m : ℝ)) := by
  let A := loglogMomentA m
  let E := loglogMomentE m
  let R := nearMomentR w A (loglogMomentIndex m)
  let N := loglogMomentX w m
  have hR : 0 < R := nearMomentR_pos w A (loglogMomentIndex m) hw
  have hE : 0 < E := loglogMomentE_pos m
  have hscale : E^(A+20) ≤ nearMomentT w A (loglogMomentIndex m)*E := by
    change E^(A+20) ≤ (64*R*E^(A+20))*E
    have h := Nat.le_mul_of_pos_left (E^(A+20))
      (show 0 < 64*R*E by positivity)
    nlinarith only [h]
  have hlog : (E : ℝ)^(A+20) ≤ Real.log (N : ℝ) := by
    have h := log_progression_scale_ge (nearMomentT w A (loglogMomentIndex m)*E)
    change ((nearMomentT w A (loglogMomentIndex m)*E : ℕ) : ℝ) ≤ Real.log N at h
    have hs : (E : ℝ)^(A+20) ≤ ((nearMomentT w A (loglogMomentIndex m)*E : ℕ) : ℝ) := by
      exact_mod_cast hscale
    exact hs.trans h
  have h := Real.log_le_log (by exact_mod_cast Nat.pow_pos hE : (0 : ℝ) < (E : ℝ)^(A+20)) hlog
  rw [Real.log_pow] at h
  have hlogE := log_loglogMomentE_lower m
  have hmR : (32 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left (show (32 : ℝ) ≤ Real.log E by linarith only [hlogE,hmR]) ha
  have hlogE0 : 0 ≤ Real.log E := by linarith only [hlogE,hmR]
  push_cast at h
  change 32*(A : ℝ) ≤ _
  nlinarith only [h,hmul,hlogE0]

lemma loglogMomentE_le_log_log_sq (w m : ℕ) (hw : 1 ≤ w) (hm : 32 ≤ m) :
    (loglogMomentE m : ℝ) ≤ (Real.log (Real.log (loglogMomentX w m : ℝ)))^2 := by
  have h := loglogMoment_log_log_lower w m hw hm
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 32*(loglogMomentA m : ℝ)) h 2
  rw [loglogMomentE_square]
  exact_mod_cast hs

lemma loglogMoment_log_log_pos (w m : ℕ) (hw : 1 ≤ w) (hm : 32 ≤ m) :
    0 < Real.log (Real.log (loglogMomentX w m : ℝ)) := by
  have h := loglogMoment_log_log_lower w m hw hm
  have ha : (0 : ℝ) < loglogMomentA m := by exact_mod_cast loglogMomentA_pos m
  linarith

lemma eventually_loglog_log_upper (w : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (loglogMomentX w m : ℝ) ≤ (loglogMomentE m : ℝ)^(loglogMomentA m+23) := by
  filter_upwards [eventually_loglog_finite_conditions w,eventually_ge_atTop 1] with m hm hm1
  apply log_nearMomentX_le_of_conditions _ _ _ hm.2
  change 4096 ≤ loglogMomentE m
  rw [loglogMomentE_eq]
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 12 ≤ 2*m+10 by omega)
  norm_num at h ⊢
  exact h

/-- The critical power is now retained, at the cost of an explicit growing
power of log log. The positive constant endpoint remains unproved. -/
theorem eventually_loglog_shiftedPrimeMoment_lower (w : ℕ) (hw : 1 ≤ w) :
    ∀ᶠ m : ℕ in atTop,
      (loglogMomentX w m : ℝ)*(Real.log (loglogMomentX w m : ℝ))^(w-1)/
        (Real.log (Real.log (loglogMomentX w m : ℝ)))^(30*w) ≤
          shiftedPrimeMoment (w+1) (loglogMomentX w m) := by
  filter_upwards [eventually_loglog_primeLog_lower w hw,eventually_loglog_log_upper w,
    eventually_ge_atTop 32] with m hlower hupper hm
  let A := loglogMomentA m
  let E := loglogMomentE m
  let N := loglogMomentX w m
  let B : ℝ := Real.log (N : ℝ)
  let H : ℝ := Real.log B
  let Z : ℝ := (E : ℝ)^(w*(A+8))
  have hB : 0 < B := lt_of_lt_of_le (by norm_num)
    (one_le_log_nearMomentX w A (loglogMomentIndex m) hw)
  have hH : 0 < H := loglogMoment_log_log_pos w m hw hm
  have hHpow : 0 < H^(30*w) := pow_pos hH _
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hlogpow : B^w ≤ (E : ℝ)^(w*(A+23)) := by
    have h := pow_le_pow_left₀ hB.le hupper w
    rw [← pow_mul] at h
    change B^w ≤ (E : ℝ)^((A+23)*w) at h
    simpa only [mul_comm (A+23) w] using h
  have hloss : (E : ℝ)^(15*w) ≤ H^(30*w) := by
    have h := pow_le_pow_left₀ hE0 (loglogMomentE_le_log_log_sq w m hw hm) (15*w)
    rw [← pow_mul,show 2*(15*w)=30*w by omega] at h
    exact h
  have he : (E : ℝ)^(w*(A+23)) = Z*(E : ℝ)^(15*w) := by
    dsimp [Z]
    rw [← pow_add]
    apply congrArg (fun e : ℕ => (E : ℝ)^e)
    ring
  rw [he] at hlogpow
  have hBpow : B^w ≤ Z*H^(30*w) := hlogpow.trans
    (mul_le_mul_of_nonneg_left hloss (show 0 ≤ Z from pow_nonneg hE0 _))
  have hmoment : (N : ℝ)*Z ≤ B*shiftedPrimeMoment (w+1) N :=
    hlower.trans (primeLogDivisorMoment_le (w+1) N)
  change (N : ℝ)*B^(w-1)/H^(30*w) ≤ _
  apply (div_le_iff₀ hHpow).mpr
  apply (le_of_mul_le_mul_left ?_ hB)
  calc
    B*((N : ℝ)*B^(w-1)) = (N : ℝ)*B^w := by
      have he : B^(w-1)*B = B^w := by rw [← pow_succ,Nat.sub_add_cancel hw]
      calc
        _ = (N : ℝ)*(B^(w-1)*B) := by ring
        _ = _ := by rw [he]
    _ ≤ (N : ℝ)*(Z*H^(30*w)) := mul_le_mul_of_nonneg_left hBpow (Nat.cast_nonneg _)
    _ = ((N : ℝ)*Z)*H^(30*w) := by ring
    _ ≤ (B*shiftedPrimeMoment (w+1) N)*H^(30*w) :=
      mul_le_mul_of_nonneg_right hmoment hHpow.le
    _ = B*(shiftedPrimeMoment (w+1) N*H^(30*w)) := by ring

lemma loglogMomentE_tendsto : Tendsto loglogMomentE atTop atTop := by
  apply logMomentScale_tendsto.comp
  apply tendsto_atTop_mono (fun m => ?_) tendsto_id
  change m ≤ 2*m+5
  omega

lemma loglogMomentX_tendsto (w : ℕ) (hw : 1 ≤ w) :
    Tendsto (loglogMomentX w) atTop atTop := by
  apply tendsto_atTop_mono (fun m => ?_) loglogMomentE_tendsto
  calc
    loglogMomentE m ≤ progressionScaleN (loglogMomentE m) :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    _ ≤ _ := progressionScaleN_monotone (Nat.le_mul_of_pos_left _
      (nearMomentT_pos w (loglogMomentA m) (loglogMomentIndex m) hw))

/-- A log-log-loss lower bound at every fixed divisor order K>=2. -/
theorem frequently_shiftedPrimeMoment_loglog_loss (K : ℕ) (hK : 2 ≤ K) :
    ∃ᶠ X : ℕ in atTop,
      (X : ℝ)*(Real.log (X : ℝ))^(K-2)/(Real.log (Real.log (X : ℝ)))^(30*(K-1)) ≤
        shiftedPrimeMoment K X := by
  let w := K-1
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hwK : w+1=K := by dsimp [w]; omega
  have hevent := eventually_loglog_shiftedPrimeMoment_lower w hw
  rw [hwK] at hevent
  apply frequently_atTop.mpr
  intro B
  obtain ⟨m,hm,hB⟩ := (hevent.and ((loglogMomentX_tendsto w hw).eventually (eventually_ge_atTop B))).exists
  exact ⟨loglogMomentX w m,hB,by simpa only [w,Nat.sub_sub] using hm⟩

/-- The log-log-loss bound also holds cofinally on every prescribed dyadic
scale family used by the sufficient moment criterion. -/
theorem cofinal_shiftedPrimeMoment_loglog_loss (K t : ℕ) (hK : 2 ≤ K) (ht : 2 ≤ t) :
    ∀ B : ℕ, ∃ L : ℕ, B ≤ L ∧
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L : ℝ))^(K-2)/
        (Real.log (Real.log (momentScaleX t L : ℝ)))^(30*(K-1)) ≤
          shiftedPrimeMoment K (momentScaleX t L) := by
  let w := K-1
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hwK : w+1=K := by dsimp [w]; omega
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_loglog_shiftedPrimeMoment_lower w hw)
  intro B
  let j := max B M+5
  let m := t*j-5
  let A := loglogMomentA m
  let E := loglogMomentE m
  let L := 262144*w*(A+20)*j*E^(A+21)
  have hj : 5 ≤ j := by dsimp [j]; omega
  have hjt : j ≤ t*j := Nat.le_mul_of_pos_left j (by omega)
  have hmp : m+5=t*j := by dsimp [m]; omega
  have hindex : loglogMomentIndex m+5=2*t*j := by
    unfold loglogMomentIndex
    rw [Nat.mul_assoc]
    omega
  have hmM : M ≤ m := by dsimp [m,j] at *; omega
  have hLB : B ≤ L := by
    have hjB : B ≤ j := by dsimp [j]; omega
    apply hjB.trans
    have hfac : 0 < 262144*w*(A+20)*E^(A+21) := by
      have hE := loglogMomentE_pos m
      change 0 < E at hE
      positivity
    have h := Nat.le_mul_of_pos_left j hfac
    simpa only [L,mul_assoc,mul_comm,mul_left_comm] using h
  have heq : loglogMomentX w m = momentScaleX t L := by
    unfold loglogMomentX nearMomentX nearMomentT nearMomentR nearMomentC progressionScaleN momentScaleX
    apply congrArg (fun e : ℕ => (2 : ℕ)^e)
    change 64*(64*(4096*w*(A+20)*(loglogMomentIndex m+5))*E^(A+20)*E) = 128*t*L
    dsimp [L]
    rw [hindex,show A+21=(A+20)+1 by omega,pow_succ _ (A+20)]
    ring
  refine ⟨L,hLB,?_⟩
  have h := hM m hmM
  rw [heq,hwK] at h
  simpa only [w,Nat.sub_sub] using h

end Erdos821
