import FormalConjecturesUtil
import Submission.SelbergSeparation
import Submission.LogarithmicPrimeGap

/-! Consecutive largest prime factors are separated by every prescribed
subpower multiplicative window on a set of density one. This unsigned theorem
does not determine which of the two factors is larger. -/

namespace Erdos371SubpowerSeparation

open Finset Filter Erdos371RectangleSeparation Erdos371SelbergSeparation
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def envelope (R : ℕ → ℕ) (t : ℕ) : ℕ :=
  (range (2^t)).sup (fun n => Nat.log 2 (R n)) + 1

lemma envelope_bound (R : ℕ → ℕ) {n t : ℕ} (hn : n < 2^t) :
    R n ≤ 2^(envelope R t) := by
  have h1 := Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) (R n)
  have h2 : Nat.log 2 (R n)+1 ≤ envelope R t :=
    Nat.add_le_add_right (le_sup (f := fun n => Nat.log 2 (R n)) (mem_range.mpr hn)) 1
  exact h1.le.trans (Nat.pow_le_pow_right (by decide) h2)

lemma envelope_sublinear (R : ℕ → ℕ)
    (hR : Tendsto (fun n => (Nat.log 2 (R n):ℝ)/(Nat.log 2 n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun t => (envelope R t:ℝ)/t) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hR.eventually_lt_const (half_pos hε))
  let C := (range (max M 2)).sup (fun n => Nat.log 2 (R n))
  have hc : Tendsto (fun t : ℕ => ((C+1:ℕ):ℝ)/t) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨t0,ht0⟩ := eventually_atTop.mp (hc.eventually_lt_const (half_pos hε))
  refine ⟨max t0 1, fun t ht => ?_⟩
  have htpos : (0:ℝ) < t := Nat.cast_pos.mpr (by omega)
  obtain ⟨n,hn,he⟩ := exists_mem_eq_sup (range (2^t))
    ⟨0, mem_range.mpr (Nat.two_pow_pos t)⟩ (fun n => Nat.log 2 (R n))
  have hnlt := mem_range.mp hn
  have hnlog : Nat.log 2 n ≤ t := by
    have hh := Nat.log_mono_right (b := 2) hnlt.le
    simpa only [Nat.log_pow (by decide : 1 < (2:ℕ))] using hh
  have hbound : (Nat.log 2 (R n):ℝ) ≤ (C:ℝ)+(ε/2)*(t:ℝ) := by
    by_cases hnsmall : n < max M 2
    · have hh : Nat.log 2 (R n) ≤ C := le_sup (f := fun n => Nat.log 2 (R n)) (mem_range.mpr hnsmall)
      exact (Nat.cast_le.mpr hh).trans (le_add_of_nonneg_right (by positivity))
    · have hn2 : 2 ≤ n := by omega
      have hn0 : (0:ℝ) < Nat.log 2 n := by
        apply Nat.cast_pos.mpr
        exact Nat.le_log_of_pow_le (by decide) (show 2^1 ≤ n by simpa using hn2)
      have hr := (div_lt_iff₀ hn0).mp (hM n (by omega))
      have hh := mul_le_mul_of_nonneg_left (Nat.cast_le (α := ℝ) |>.mpr hnlog) (half_pos hε).le
      nlinarith [Nat.cast_nonneg (α := ℝ) C]
  have hsmall := (div_lt_iff₀ htpos).mp (ht0 t (by omega))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply (div_lt_iff₀ htpos).mpr
  simp only [envelope,he,Nat.cast_add,Nat.cast_one] at *
  linarith

/-- No monotonicity or divergence assumption is needed on the window `R`.
Subpower growth is expressed here using binary integer logarithms. -/
theorem subpower_hasDensity_zero (R : ℕ → ℕ)
    (hR : Tendsto (fun n => (Nat.log 2 (R n):ℝ)/(Nat.log 2 n:ℝ)) atTop (𝓝 0)) :
    {n | max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) ≤
      R n * min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))}.HasDensity 0 := by
  classical
  let S : Set ℕ := {n | max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) ≤
    R n * min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))}
  have hdyad : Tendsto (fun t : ℕ => S.partialDensity Set.univ (2^t)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (sublinear_width_count_tendsto (envelope R) (envelope_sublinear R hR))
    · intro t
      unfold Set.partialDensity
      positivity
    · intro t
      change S.partialDensity Set.univ (2^t) ≤ ((closeInputs (envelope R t) (2^t)).card:ℝ)/(2:ℝ)^t
      rw [Erdos371ReflectionRange.partialDensity_eq_filter_card]
      have hc : ((range (2^t)).filter fun n => n ∈ S).card ≤
          (closeInputs (envelope R t) (2^t)).card := by
        apply card_le_card
        intro n hn
        obtain ⟨hnN,hc⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨hnN, hc.trans
          (Nat.mul_le_mul_right _ (envelope_bound R (mem_range.mp hnN)))⟩
      have hh := div_le_div_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hc)
        (show (0:ℝ) ≤ (2:ℝ)^t by positivity)
      convert hh using 1 <;> simp only [Nat.cast_pow, Nat.cast_ofNat]
      congr 2
      apply congrArg Finset.card
      ext n
      simp
  apply Erdos371LogarithmicPrimeGap.hasDensity_zero_of_geometric
  have ht : Tendsto (fun t : ℕ => 2*t) atTop atTop :=
    tendsto_atTop_mono (fun t => by omega : ∀ t : ℕ, t ≤ 2*t) tendsto_id
  have hh := hdyad.comp ht
  convert hh using 1
  ext t
  have he : (2:ℕ)^(2*t)=4^t := by rw [pow_mul]; norm_num
  change S.partialDensity Set.univ (4^t) = S.partialDensity Set.univ (2^(2*t))
  rw [he]

lemma natLog_ratio_bound (R : ℕ → ℕ) {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log 2 (R n):ℝ)/(Nat.log 2 n:ℝ) ≤
      2*Real.log (R n:ℝ)/Real.log (n:ℝ) := by
  have hln : (1:ℝ) ≤ Nat.log 2 n := by
    exact_mod_cast (Nat.le_log_of_pow_le (by decide : 1<(2:ℕ))
      (show 2^1≤n by simpa using hn))
  have hln0 : (0:ℝ) < Nat.log 2 n := by linarith
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlogn : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR := Real.natLog_le_logb (R n) 2
  change (Nat.log 2 (R n):ℝ) ≤ Real.log (R n:ℝ)/Real.log 2 at hR
  have hR' := (le_div_iff₀ hlog2).mp hR
  have hn' : Real.log (n:ℝ) ≤ ((Nat.log 2 n:ℝ)+1)*Real.log 2 := by
    have he : (n:ℝ) ≤ (2:ℝ)^(Nat.log 2 n+1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) n).le
    have hh := Real.log_le_log hn0 he
    simpa [Real.log_pow] using hh
  have h1 := mul_le_mul_of_nonneg_left hn' (Nat.cast_nonneg (α := ℝ) (Nat.log 2 (R n)))
  have h2 := mul_le_mul_of_nonneg_left hR' (show 0 ≤ (Nat.log 2 n:ℝ)+1 by positivity)
  have h3 := mul_le_mul_of_nonneg_right (show (Nat.log 2 n:ℝ)+1 ≤ 2*Nat.log 2 n by linarith)
    (Real.log_natCast_nonneg (R n))
  apply (div_le_div_iff₀ hln0 hlogn).mpr
  nlinarith

lemma subpower_natLog_of_log (R : ℕ → ℕ)
    (hR : Tendsto (fun n => Real.log (R n:ℝ)/Real.log (n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (Nat.log 2 (R n):ℝ)/(Nat.log 2 n:ℝ)) atTop (𝓝 0) := by
  have hh := hR.const_mul 2
  simp only [mul_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
  · exact Eventually.of_forall (fun _ => by positivity)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    simpa only [mul_div_assoc] using natLog_ratio_bound R hn

/-- Any prescribed subpower window is negligible for the ratio of consecutive
largest prime factors. This statement involves the absolute separation only. -/
theorem subpower_hasDensity_zero_of_log (R : ℕ → ℕ)
    (hR : Tendsto (fun n => Real.log (R n:ℝ)/Real.log (n:ℝ)) atTop (𝓝 0)) :
    {n | max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) ≤
      R n * min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))}.HasDensity 0 :=
  subpower_hasDensity_zero R (subpower_natLog_of_log R hR)

lemma ceil_rpow_div_tendsto {β : ℝ} (hβ : β < 1) :
    Tendsto (fun t : ℕ => (⌈(t:ℝ)^β⌉₊:ℝ)/t) atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℕ => (t:ℝ)^β/t) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).comp tendsto_natCast_atTop_atTop
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    change (t:ℝ)^(-(1-β)) = (t:ℝ)^β/t
    rw [show -(1-β)=β-1 by ring, Real.rpow_sub (Nat.cast_pos.mpr ht), Real.rpow_one]
  have hu : Tendsto (fun t : ℕ => ((t:ℝ)^β+1)/t) atTop (𝓝 0) := by
    simpa [add_div] using hp.add tendsto_one_div_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · intro t; positivity
  · intro t
    exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)).le
      (Nat.cast_nonneg _)

/-- In particular, every logarithmic-power exponent below one is admissible.
This includes windows much larger than the earlier fourth-root example. -/
theorem log_power_window_hasDensity_zero {β : ℝ} (hβ : β < 1) :
    {n | max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) ≤
      2^⌈((Nat.log 2 n:ℕ):ℝ)^β⌉₊ * min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1))}.HasDensity 0 := by
  apply subpower_hasDensity_zero
  simp only [Nat.log_pow (by decide : 1<(2:ℕ))]
  have hlog : Tendsto (Nat.log 2) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (2^k)] with n hn
    exact Nat.le_log_of_pow_le (by decide) hn
  exact (ceil_rpow_div_tendsto hβ).comp hlog

end Erdos371SubpowerSeparation

#print axioms Erdos371SubpowerSeparation.subpower_hasDensity_zero

#print axioms Erdos371SubpowerSeparation.subpower_hasDensity_zero_of_log

#print axioms Erdos371SubpowerSeparation.log_power_window_hasDensity_zero
