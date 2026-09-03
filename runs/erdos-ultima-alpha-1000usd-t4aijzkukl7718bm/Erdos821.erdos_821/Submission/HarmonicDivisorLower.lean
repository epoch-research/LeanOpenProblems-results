import Submission.DivisorMomentOverlap

/-!
# A factorial-scale lower bound for harmonic divisor moments

This elementary bound concerns all integers, not shifted primes. A weighted
prime-progression discrepancy estimate is still needed to transfer it.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 2000000

lemma harmonicMoment_succ (k A : ℕ) :
    harmonicMoment (k+1) A = ∑ m ∈ Finset.Icc 1 A,
      harmonicMoment k (A/m)/(m : ℝ) := by
  unfold harmonicMoment
  simp_rw [tau_cast, div_eq_mul_inv]
  rw [_root_.pow_succ', AnalyticSieve.sum_convolution_weighted _ _ _ (le_refl A)]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  have hset : (Finset.Icc 1 A).filter (fun n => m*n ≤ A) = Finset.Icc 1 (A/m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hd := Nat.div_le_self A m
    have he (n : ℕ) : m*n ≤ A ↔ n ≤ A/m := by
      rw [Nat.le_div_iff_mul_le hm0, mul_comm]
    simp only [he]
    omega
  rw [← Finset.sum_filter, hset, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [natCoe_apply, zeta_apply_ne hm0.ne', Nat.cast_one, one_mul,
    Nat.cast_mul, mul_inv]
  ring

lemma integral_log_kernel (k : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    (∫ x in (1 : ℝ)..B, (Real.log B - Real.log x)^k/x) =
      (Real.log B)^(k+1)/(k+1 : ℝ) := by
  have hxpos (x : ℝ) (hx : x ∈ Set.uIcc 1 B) : 0 < x := by
    rw [Set.uIcc_of_le hB] at hx
    linarith [hx.1]
  have hc : ContinuousOn (fun x : ℝ => (Real.log B - Real.log x)^k/x)
      (Set.uIcc 1 B) := by
    intro x hx
    exact (((continuousAt_const.sub (Real.continuousAt_log (hxpos x hx).ne')).pow k).div
      continuousAt_id (hxpos x hx).ne').continuousWithinAt
  have hd (x : ℝ) (hx : x ∈ Set.uIcc 1 B) :
      HasDerivAt (fun x : ℝ => -(Real.log B-Real.log x)^(k+1)/(k+1 : ℝ))
        ((Real.log B-Real.log x)^k/x) x := by
    have h := ((((Real.hasDerivAt_log (hxpos x hx).ne').const_sub (Real.log B)).pow (k+1)).neg).div_const
      (k+1 : ℝ)
    convert h using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp [neg_div]

lemma log_kernel_sum_lower (k A : ℕ) :
    (Real.log (A+1 : ℝ))^(k+1)/(k+1 : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 A, (Real.log (A+1 : ℝ)-Real.log (m : ℝ))^k/(m : ℝ) := by
  let B : ℝ := A+1
  have hB : 1 ≤ B := by dsimp [B]; exact le_add_of_nonneg_left (Nat.cast_nonneg A)
  have ha : AntitoneOn (fun x : ℝ => (Real.log B-Real.log x)^k/x) (Set.Icc 1 B) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := by linarith [hx.1]
    have hy0 : 0 < y := by linarith [hy.1]
    have hly : 0 ≤ Real.log B-Real.log y :=
      sub_nonneg.mpr (Real.log_le_log hy0 hy.2)
    exact div_le_div₀ (pow_nonneg (sub_nonneg.mpr (Real.log_le_log hx0 hx.2)) k)
      (pow_le_pow_left₀ hly (sub_le_sub_left (Real.log_le_log hx0 hxy) _) k) hx0 hxy
  have hi := AntitoneOn.integral_le_sum_Ico (show 1 ≤ A+1 by omega)
    (show AntitoneOn (fun x : ℝ => (Real.log B-Real.log x)^k/x)
      (Set.Icc ((1 : ℕ) : ℝ) ((A+1 : ℕ) : ℝ)) by
      simpa only [Nat.cast_one, Nat.cast_add, B] using ha)
  simp only [Nat.cast_one, Nat.cast_add] at hi
  rw [integral_log_kernel k B hB] at hi
  simpa only [B, Finset.Ico_succ_right_eq_Icc] using hi

/-- The logarithmic simplex volume is a lower bound, with no exponential
loss in the divisor order. The shift A+1 handles the floor in convolution. -/
theorem harmonicMoment_factorial_lower (k A : ℕ) (hA : 1 ≤ A) :
    (Real.log (A+1 : ℝ))^k/(k.factorial : ℝ) ≤ harmonicMoment k A := by
  induction k generalizing A with
  | zero =>
    simp only [harmonicMoment, tau, pow_zero, ArithmeticFunction.one_apply,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_div, zero_div, Nat.factorial_zero]
    simp [hA]
  | succ k ih =>
    have hkF : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    calc
      _ = ((Real.log (A+1 : ℝ))^(k+1)/(k+1 : ℝ))/(k.factorial : ℝ) := by
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_div]
      _ ≤ (∑ m ∈ Finset.Icc 1 A,
          (Real.log (A+1 : ℝ)-Real.log (m : ℝ))^k/(m : ℝ))/(k.factorial : ℝ) :=
        div_le_div_of_nonneg_right (log_kernel_sum_lower k A) hkF.le
      _ ≤ harmonicMoment (k+1) A := by
        rw [Finset.sum_div, harmonicMoment_succ]
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨hm1,hmA⟩ := Finset.mem_Icc.mp hm
        have hm0 : 0 < m := hm1
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
        have hAm : 1 ≤ A/m := (Nat.one_le_div_iff hm0).mpr hmA
        have hcast : (A+1 : ℝ) ≤ (m : ℝ)*((A/m : ℕ)+1 : ℝ) := by
          exact_mod_cast (show A+1 ≤ m*(A/m+1) from Nat.lt_mul_div_succ A hm0)
        have hr : (A+1 : ℝ)/(m : ℝ) ≤ ((A/m : ℕ)+1 : ℝ) :=
          (div_le_iff₀ hmR).mpr (by linarith [hcast])
        have hlog : Real.log (A+1 : ℝ)-Real.log (m : ℝ) ≤
            Real.log ((A/m : ℕ)+1 : ℝ) := by
          rw [← Real.log_div (by positivity : (A+1 : ℝ) ≠ 0) hmR.ne']
          exact Real.log_le_log (by positivity) hr
        have hbase : 0 ≤ Real.log (A+1 : ℝ)-Real.log (m : ℝ) := by
          apply sub_nonneg.mpr
          apply Real.log_le_log hmR
          have h : (m : ℝ) ≤ A := by exact_mod_cast hmA
          linarith
        calc
          _ = ((Real.log (A+1 : ℝ)-Real.log (m : ℝ))^k/(k.factorial : ℝ))/(m : ℝ) := by ring
          _ ≤ ((Real.log ((A/m : ℕ)+1 : ℝ))^k/(k.factorial : ℝ))/(m : ℝ) :=
            div_le_div_of_nonneg_right
              (div_le_div_of_nonneg_right (pow_le_pow_left₀ hbase hlog k) hkF.le) hmR.le
          _ ≤ _ := div_le_div_of_nonneg_right (ih (A/m) hAm) hmR.le

end Erdos821.HigherDivisors
