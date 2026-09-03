import Submission.NearMomentMass

/-!
# Every subcritical logarithmic power for shifted-prime divisor moments

For each fixed order K>=2 and every real alpha<K-2, the moment exceeds
X*(log X)^alpha at arbitrarily large X. This does not establish the
critical logarithmic power with a positive constant, and hence does not
supply the cofinal geometric moment hypothesis used for Erdős 821.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 4000000

lemma one_le_log_nearMomentX (w A m : ℕ) (hw : 1 ≤ w) :
    1 ≤ Real.log (nearMomentX w A m : ℝ) := by
  have hscale : 1 ≤ nearMomentT w A m*logMomentScale m :=
    Nat.mul_pos (nearMomentT_pos w A m hw) (by have := logMomentScale_ge m; omega)
  have h := log_progression_scale_ge (nearMomentT w A m*logMomentScale m)
  have hR : (1 : ℝ) ≤ (nearMomentT w A m*logMomentScale m : ℕ) := by exact_mod_cast hscale
  exact hR.trans h

lemma eventually_log_nearMomentX_le (w A : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (nearMomentX w A m : ℝ) ≤ (logMomentScale m : ℝ)^(A+23) := by
  filter_upwards [eventually_nearMomentR_add_one_le_scale w A,
    logMomentScale_tendsto.eventually (eventually_ge_atTop 4096)] with m hR hE
  let E := logMomentScale m
  have hRR : (nearMomentR w A m : ℝ) ≤ E := by exact_mod_cast (show nearMomentR w A m ≤ E by omega)
  have hER : (4096 : ℝ) ≤ E := by exact_mod_cast hE
  have hlog := log_two_pow_le (64*(nearMomentT w A m*E))
  change Real.log (nearMomentX w A m : ℝ) ≤ _ at hlog
  simp only [nearMomentT,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hlog
  calc
    _ ≤ 4096*(nearMomentR w A m : ℝ)*(E : ℝ)^(A+21) := by
      convert hlog using 1
      rw [show A+21=(A+20)+1 by omega,pow_succ _ (A+20)]
      ring
    _ ≤ (E : ℝ)*(E : ℝ)*(E : ℝ)^(A+21) := by gcongr
    _ = _ := by
      change _ = (E : ℝ)^(A+23)
      rw [show A+23=(A+21)+2 by omega,pow_add _ (A+21) 2,pow_two]
      ring

noncomputable def nearMomentExponent (w A : ℕ) : ℝ :=
  (w : ℝ)*((A : ℝ)+8)/((A : ℝ)+23)-1

/-- A finite-parameter lower bound approaching the critical logarithmic
exponent as A tends to infinity. The order w+1 stays fixed. -/
theorem eventually_nearMoment_log_power (w A : ℕ) (hw : 1 ≤ w) :
    ∀ᶠ m : ℕ in atTop,
      (nearMomentX w A m : ℝ)*(Real.log (nearMomentX w A m : ℝ))^(nearMomentExponent w A) ≤
        shiftedPrimeMoment (w+1) (nearMomentX w A m) := by
  filter_upwards [eventually_nearMoment_primeLog_lower w A hw,eventually_log_nearMomentX_le w A]
    with m hlower hupper
  let N := nearMomentX w A m
  let E := logMomentScale m
  let β : ℝ := (w : ℝ)*((A : ℝ)+8)/((A : ℝ)+23)
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hlog : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by norm_num) (one_le_log_nearMomentX w A m hw)
  have hpow : (Real.log (N : ℝ))^β ≤ (E : ℝ)^(w*(A+8)) := by
    apply (Real.rpow_le_rpow hlog.le hupper hβ).trans_eq
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg E)]
    have he : ((A+23 : ℕ) : ℝ)*β = ((w*(A+8) : ℕ) : ℝ) := by
      dsimp [β]
      push_cast
      field_simp
    rw [he,Real.rpow_natCast]
  have h := (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)).trans
    (hlower.trans (primeLogDivisorMoment_le (w+1) N))
  change (N : ℝ)*(Real.log (N : ℝ))^(β-1) ≤ _
  rw [Real.rpow_sub hlog,Real.rpow_one,← mul_div_assoc]
  apply (div_le_iff₀ hlog).mpr
  simpa only [mul_comm] using h

lemma nearMomentX_tendsto (w A : ℕ) (hw : 1 ≤ w) :
    Tendsto (nearMomentX w A) atTop atTop := by
  apply tendsto_atTop_mono (fun m => ?_) logMomentScale_tendsto
  calc
    logMomentScale m ≤ progressionScaleN (logMomentScale m) :=
      Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    _ ≤ _ := progressionScaleN_monotone (Nat.le_mul_of_pos_left _ (nearMomentT_pos w A m hw))

lemma nearMomentExponent_eq (w A : ℕ) :
    nearMomentExponent w A = (w : ℝ)-1-15*(w : ℝ)/((A : ℝ)+23) := by
  unfold nearMomentExponent
  field_simp
  ring

lemma exists_nearMomentExponent_gt (w : ℕ) (α : ℝ) (_hw : 1 ≤ w)
    (hα : α < (w : ℝ)-1) : ∃ A : ℕ, α < nearMomentExponent w A := by
  let δ := (w : ℝ)-1-α
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A,hA⟩ := exists_nat_gt (15*(w : ℝ)/δ)
  have h1 : 15*(w : ℝ) < (A : ℝ)*δ := (div_lt_iff₀ hδ).mp hA
  have h2 : 15*(w : ℝ)/((A : ℝ)+23) < δ := by
    apply (div_lt_iff₀ (by positivity : 0 < (A : ℝ)+23)).mpr
    nlinarith only [h1,hδ]
  refine ⟨A,?_⟩
  rw [nearMomentExponent_eq]
  dsimp [δ] at h2
  linarith only [h2]

/-- Every fixed order has every logarithmic power strictly below its
critical power. The endpoint coefficient is not asserted. -/
theorem frequently_shiftedPrimeMoment_subcritical_power (K : ℕ) (hK : 2 ≤ K)
    (α : ℝ) (hα : α < (K : ℝ)-2) :
    ∃ᶠ X : ℕ in atTop,
      (X : ℝ)*(Real.log (X : ℝ))^α ≤ shiftedPrimeMoment K X := by
  let w := K-1
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hwK : w+1=K := by dsimp [w]; omega
  have hαw : α < (w : ℝ)-1 := by
    dsimp [w]
    rw [Nat.cast_sub (by omega : 1 ≤ K),Nat.cast_one]
    linarith only [hα]
  obtain ⟨A,hA⟩ := exists_nearMomentExponent_gt w α hw hαw
  have hevent : ∀ᶠ m : ℕ in atTop,
      (nearMomentX w A m : ℝ)*(Real.log (nearMomentX w A m : ℝ))^α ≤
        shiftedPrimeMoment K (nearMomentX w A m) := by
    filter_upwards [eventually_nearMoment_log_power w A hw] with m hm
    rw [hwK] at hm
    apply le_trans _ hm
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_log_nearMomentX w A m hw) hA.le) (Nat.cast_nonneg _)
  apply frequently_atTop.mpr
  intro B
  obtain ⟨m,hm,hB⟩ := (hevent.and ((nearMomentX_tendsto w A hw).eventually (eventually_ge_atTop B))).exists
  exact ⟨nearMomentX w A m,hB,hm⟩

/-- An epsilon form of the subcritical-power theorem. -/
theorem frequently_shiftedPrimeMoment_almost_critical (K : ℕ) (hK : 2 ≤ K)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ᶠ X : ℕ in atTop,
      (X : ℝ)*(Real.log (X : ℝ))^((K : ℝ)-2-δ) ≤ shiftedPrimeMoment K X :=
  frequently_shiftedPrimeMoment_subcritical_power K hK _ (by linarith)

/-- The same lower bound on the exact dyadic scales used by the cofinal
moment criterion, still with a strictly subcritical logarithmic power. -/
theorem cofinal_nearMoment_dyadic_power (w A t : ℕ) (hw : 1 ≤ w) (ht : 1 ≤ t) :
    ∀ B : ℕ, ∃ L : ℕ, B ≤ L ∧
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L : ℝ))^(nearMomentExponent w A) ≤
        shiftedPrimeMoment (w+1) (momentScaleX t L) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_nearMoment_log_power w A hw)
  intro B
  let j := max B M+5
  let m := t*j-5
  let E := logMomentScale m
  let L := 131072*w*(A+20)*j*E^(A+21)
  have hj : 5 ≤ j := by dsimp [j]; omega
  have hjt : j ≤ t*j := Nat.le_mul_of_pos_left j ht
  have hmp : m+5=t*j := by dsimp [m]; omega
  have hmM : M ≤ m := by dsimp [m,j] at *; omega
  have hLB : B ≤ L := by
    have hjB : B ≤ j := by dsimp [j]; omega
    apply hjB.trans
    have hfac : 0 < 131072*w*(A+20)*E^(A+21) := by
      dsimp [E,logMomentScale]
      positivity
    have h := Nat.le_mul_of_pos_left j hfac
    simpa only [L,mul_assoc,mul_comm,mul_left_comm] using h
  have heq : nearMomentX w A m = momentScaleX t L := by
    unfold nearMomentX nearMomentT nearMomentR nearMomentC progressionScaleN momentScaleX
    apply congrArg (fun e : ℕ => (2 : ℕ)^e)
    change 64*(64*(4096*w*(A+20)*(m+5))*E^(A+20)*E) = 128*t*L
    dsimp [L]
    rw [hmp,show A+21=(A+20)+1 by omega,pow_succ _ (A+20)]
    ring
  exact ⟨L,hLB,by simpa only [heq] using hM m hmM⟩

/-- Every strict loss from the critical logarithmic power is unconditionally
available on a cofinal set of the prescribed scales. The zero-loss case
is not included. -/
theorem cofinal_shiftedPrimeMoment_subcritical (K t : ℕ) (hK : 2 ≤ K) (ht : 2 ≤ t)
    (α : ℝ) (hα : α < (K : ℝ)-2) :
    ∀ B : ℕ, ∃ L : ℕ, B ≤ L ∧
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L : ℝ))^α ≤
        shiftedPrimeMoment K (momentScaleX t L) := by
  let w := K-1
  have hw : 1 ≤ w := by dsimp [w]; omega
  have hwK : w+1=K := by dsimp [w]; omega
  have hαw : α < (w : ℝ)-1 := by
    dsimp [w]
    rw [Nat.cast_sub (by omega : 1 ≤ K),Nat.cast_one]
    linarith only [hα]
  obtain ⟨A,hA⟩ := exists_nearMomentExponent_gt w α hw hαw
  intro B
  obtain ⟨L,hL,hm⟩ := cofinal_nearMoment_dyadic_power w A t hw (by omega) (max B 1)
  have hLB : B ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  rw [hwK] at hm
  refine ⟨L,hLB,le_trans ?_ hm⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (one_le_log_momentScaleX t L (by omega) hL1) hA.le

end Erdos821
