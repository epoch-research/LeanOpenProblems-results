import Submission.UniformRankin

/-!
# Direct prime-support estimates for inverse-totient fibers

Auxiliary estimates only: the exponent loss below is scale-dependent.
-/

open Nat Filter
open scoped Classical

namespace Erdos821
open Sieve

lemma sum_prime_inv_iterated_dyadic_le (J : ℕ) :
    (∑ p ∈ (2 ^ (2 ^ J) + 1).primesBelow, ((p : ℕ) : ℝ)⁻¹) ≤ 1 + 8 * J := by
  induction J with
  | zero => norm_num [Nat.primesBelow, Finset.sum_filter, Finset.sum_range_succ]
  | succ J ih =>
    let P := (2 ^ (2 ^ J) + 1).primesBelow
    let Q := (2 ^ (2 ^ (J + 1)) + 1).primesBelow
    have hPQ : P ⊆ Q := by
      intro p hp
      obtain ⟨hpP, hprime⟩ := Nat.mem_primesBelow.mp hp
      have hpow : 2 ^ (2 ^ J) ≤ 2 ^ (2 ^ (J + 1)) :=
        Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega))
      exact Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hden : 0 < (2 : ℝ) ^ J * Real.log 2 := by positivity
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have hblock : (∑ p ∈ Q \ P, ((p : ℕ) : ℝ)⁻¹) ≤ 8 := by
      apply (mul_le_mul_iff_left₀ hden).mp
      calc
        (∑ p ∈ Q \ P, ((p : ℕ) : ℝ)⁻¹) * ((2 : ℝ) ^ J * Real.log 2) ≤
            ∑ p ∈ Q \ P, Real.log (p : ℝ) / p := by
          rw [Finset.sum_mul]
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpQ, hpP⟩ := Finset.mem_sdiff.mp hp
          have hprime := (Nat.mem_primesBelow.mp hpQ).2
          have hple : 2 ^ (2 ^ J) ≤ p := by
            by_contra h
            exact hpP (Nat.mem_primesBelow.mpr ⟨by omega, hprime⟩)
          have hlogp : (2 : ℝ) ^ J * Real.log 2 ≤ Real.log (p : ℝ) := by
            have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ (2 ^ J) : ℕ) : ℝ))
              (show ((2 ^ (2 ^ J) : ℕ) : ℝ) ≤ p by exact_mod_cast hple)
            simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h
          simpa only [div_eq_mul_inv, mul_comm] using
            mul_le_mul_of_nonneg_left hlogp (inv_nonneg.mpr (Nat.cast_nonneg p))
        _ ≤ ∑ p ∈ Q, Real.log (p : ℝ) / p :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun p hp _ =>
            div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt.le))
              (Nat.cast_nonneg p))
        _ ≤ 2 * Real.log 4 * ((2 ^ (J + 1) : ℕ) : ℝ) := sum_prime_log_div_dyadic_le _
        _ = 8 * ((2 : ℝ) ^ J * Real.log 2) := by
          rw [hlog4]
          push_cast
          rw [pow_succ]
          ring
    change (∑ p ∈ Q, ((p : ℕ) : ℝ)⁻¹) ≤ _
    have heq := (Finset.sum_sdiff hPQ (f := fun p : ℕ => ((p : ℕ) : ℝ)⁻¹)).symm
    rw [heq]
    have hi : (∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹) ≤ 1 + 8 * (J : ℝ) := ih
    push_cast
    linarith

lemma finite_prime_euler_product_le_exp_weight (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (s : ℝ) (hs : 1 / 2 ≤ s) :
    (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) ≤
      Real.exp (uniformRankinBase * ∑ p ∈ P, (p : ℝ) ^ (-s)) := by
  have hr : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hpoint (p : ℕ) (hp : p ∈ P) :
      0 < 1 - (p : ℝ) ^ (-s) ∧
        (1 - (p : ℝ) ^ (-s))⁻¹ ≤ Real.exp (uniformRankinBase * (p : ℝ) ^ (-s)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hpr : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        _ ≤ (2 : ℝ) ^ (-s) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hz : 0 < 1 - (p : ℝ) ^ (-s) := by linarith
    refine ⟨hz, ?_⟩
    calc
      (1 - (p : ℝ) ^ (-s))⁻¹ = 1 + (p : ℝ) ^ (-s) / (1 - (p : ℝ) ^ (-s)) := by
        field_simp
        ring
      _ ≤ 1 + uniformRankinBase * (p : ℝ) ^ (-s) := by
        apply add_le_add_right
        dsimp [uniformRankinBase]
        rw [mul_comm, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          (by linarith) (by linarith)
      _ ≤ _ := by simpa only [add_comm] using
          Real.add_one_le_exp (uniformRankinBase * (p : ℝ) ^ (-s))
  calc
    _ ≤ ∏ p ∈ P, Real.exp (uniformRankinBase * (p : ℝ) ^ (-s)) := by
      apply Finset.prod_le_prod
      · intro p hp; exact inv_nonneg.mpr (hpoint p hp).1.le
      · intro p hp; exact (hpoint p hp).2
    _ = _ := by rw [Finset.mul_sum, Real.exp_sum]

lemma sum_primeFactors_weight_le_at_iterated_scale (J n : ℕ) (hJ : 1 ≤ J)
    (hn : 0 < n) (hbound : n ≤ 2 ^ (2 ^ (2 ^ J))) :
    (∑ p ∈ n.primeFactors, (p : ℝ) ^ (-(1 - 1 / ((2 : ℝ) ^ J)))) ≤ 4 + 16 * J := by
  let T : ℕ := 2 ^ J
  let Y : ℕ := 2 ^ T
  let s : ℝ := 1 - 1 / (T : ℝ)
  let A := n.primeFactors.filter (fun p => p ≤ Y)
  let B := n.primeFactors.filter (fun p => ¬ p ≤ Y)
  have hT : 2 ≤ T := by
    dsimp [T]
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hJ
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have he : 0 < 1 / (T : ℝ) := by positivity
  have hehalf : 1 / (T : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hTR
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hYpow : (Y : ℝ) ^ (1 - s) = 2 := by
    dsimp [Y]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hid : (T : ℝ) * (1 - s) = 1 := by dsimp [s]; field_simp; ring
    rw [hid, Real.rpow_one]
  have hcard : n.primeFactors.card ≤ Y := by
    have hprod : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
      calc
        _ = ∏ _p ∈ n.primeFactors, 2 := by simp
        _ ≤ _ := Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact hprod.trans ((Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)).trans hbound)
  have hAsub : A ⊆ (Y + 1).primesBelow := by
    intro p hp
    obtain ⟨hpn, hpY⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_of_mem_primeFactors hpn⟩
  have hsmall : (∑ p ∈ A, (p : ℝ) ^ (-s)) ≤ 2 * (1 + 8 * (J : ℝ)) := by
    calc
      _ ≤ ∑ p ∈ A, 2 * (p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpn, hpY⟩ := Finset.mem_filter.mp hp
        have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_mem_primeFactors hpn
        calc
          (p : ℝ) ^ (-s) = (p : ℝ) ^ (1 - s) * (p : ℝ)⁻¹ := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hpR]
            congr 1
            ring
          _ ≤ (Y : ℝ) ^ (1 - s) * (p : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow hpR.le (by exact_mod_cast hpY) (by linarith)) (by positivity)
          _ = _ := by rw [hYpow]
      _ = 2 * ∑ p ∈ A, (p : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * ∑ p ∈ (Y + 1).primesBelow, ((p : ℕ) : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hAsub
            (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_prime_inv_iterated_dyadic_le J) (by norm_num)
  have hlarge : (∑ p ∈ B, (p : ℝ) ^ (-s)) ≤ 2 := by
    calc
      _ ≤ ∑ _p ∈ B, (Y : ℝ) ^ (-s) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpY : Y ≤ p := by have := (Finset.mem_filter.mp hp).2; omega
        exact Real.rpow_le_rpow_of_nonpos hYR (by exact_mod_cast hpY) (by linarith)
      _ = (B.card : ℝ) * (Y : ℝ) ^ (-s) := by simp
      _ ≤ (Y : ℝ) * (Y : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Finset.card_filter_le _ _).trans hcard) (Real.rpow_nonneg hYR.le _)
      _ = (Y : ℝ) ^ (1 - s) := by
        nth_rw 1 [← Real.rpow_one (Y : ℝ)]
        rw [← Real.rpow_add hYR]
        congr 1
      _ = 2 := hYpow
  have hsum : (∑ p ∈ n.primeFactors, (p : ℝ) ^ (-s)) ≤ 4 + 16 * (J : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ Y)]
    change (∑ p ∈ A, (p : ℝ) ^ (-s)) + (∑ p ∈ B, (p : ℝ) ^ (-s)) ≤ _
    linarith
  simpa only [s, T, Nat.cast_pow, Nat.cast_ofNat] using hsum

/-- A direct uniform upper bound. The exponent loss `1 / 2^J` tends to zero
as the range of inputs grows; it is not a disproof of the conjecture. -/
theorem g_le_direct_support_rankin (J n : ℕ) (hJ : 1 ≤ J)
    (hn : 0 < n) (hbound : n ≤ 2 ^ (2 ^ (2 ^ J))) :
    (g n : ℝ) ≤
      Real.exp (Real.exp (uniformRankinBase * (4 + 16 * J))) *
        (n : ℝ) ^ (1 - 1 / (2 : ℝ) ^ J) := by
  have hT : (2 : ℝ) ≤ (2 : ℝ) ^ J := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJ
  have he : 1 / (2 : ℝ) ^ J ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hT
  have hs : 1 / 2 ≤ 1 - 1 / (2 : ℝ) ^ J := by linarith
  have hp := finite_prime_euler_product_le_exp_weight n.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) _ hs
  have hw := sum_primeFactors_weight_le_at_iterated_scale J n hJ hn hbound
  have hprod : (∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-(1 - 1 / (2 : ℝ) ^ J)))⁻¹) ≤
      Real.exp (uniformRankinBase * (4 + 16 * J)) :=
    hp.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw uniformRankinBase_pos.le))
  exact (g_le_rpow_mul_exp_primeFactors n hn _ (by linarith)).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hprod) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma eventually_direct_support_prefactor_budget :
    ∀ᶠ J : ℕ in atTop,
      Real.exp (uniformRankinBase * (4 + 16 * (J + 1 : ℕ))) * (2 : ℝ) ^ (J + 2) ≤
        Real.log 2 * (2 : ℝ) ^ (2 ^ J : ℕ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a := 16 * uniformRankinBase + Real.log 2
  let b := 20 * uniformRankinBase + 2 * Real.log 2 - Real.log (Real.log 2)
  have h1 : Tendsto (fun J : ℕ => (J : ℝ) / (2 : ℝ) ^ J) atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have h0 : Tendsto (fun J : ℕ => 1 / (2 : ℝ) ^ J) atTop (nhds 0) := by
    simpa only [pow_zero] using tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)
  have hlim : Tendsto (fun J : ℕ => (a * J + b) / (2 : ℝ) ^ J) atTop (nhds 0) := by
    convert (h1.const_mul a).add (h0.const_mul b) using 1 <;> try simp only [mul_zero, add_zero]
    ext J
    ring
  filter_upwards [hlim.eventually (gt_mem_nhds hlog)] with J hJ
  have hlin : a * (J : ℝ) + b ≤ Real.log 2 * (2 : ℝ) ^ J :=
    ((div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ J)).mp hJ).le
  have harg : uniformRankinBase * (4 + 16 * ((J + 1 : ℕ) : ℝ)) +
      ((J + 2 : ℕ) : ℝ) * Real.log 2 ≤
        Real.log (Real.log 2) + ((2 ^ J : ℕ) : ℝ) * Real.log 2 := by
    dsimp [a, b] at hlin
    push_cast
    linarith
  have hexp := Real.exp_le_exp.mpr harg
  simpa only [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log hlog] using hexp

/-- On adjacent iterated-dyadic windows the prefactor is absorbed into half
of the exponent saving. The remaining loss is still scale-dependent. -/
theorem eventually_g_le_power_on_iterated_windows :
    ∀ᶠ J : ℕ in atTop, ∀ n : ℕ,
      2 ^ (2 ^ (2 ^ J)) ≤ n → n ≤ 2 ^ (2 ^ (2 ^ (J + 1))) →
      (g n : ℝ) ≤ (n : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (J + 2)) := by
  filter_upwards [eventually_direct_support_prefactor_budget] with J hbudget
  intro n hnlo hnhi
  have hn : 0 < n := (pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hnlo
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogn : Real.log 2 * (2 : ℝ) ^ (2 ^ J : ℕ) ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ (2 ^ (2 ^ J)) : ℕ) : ℝ))
      (show ((2 ^ (2 ^ (2 ^ J)) : ℕ) : ℝ) ≤ n by exact_mod_cast hnlo)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_comm] using h
  have hE : Real.exp (uniformRankinBase * (4 + 16 * (J + 1 : ℕ))) ≤
      Real.log n / (2 : ℝ) ^ (J + 2) :=
    (le_div_iff₀ (by positivity)).mpr (hbudget.trans hlogn)
  have hpre : Real.exp (Real.exp (uniformRankinBase * (4 + 16 * (J + 1 : ℕ)))) ≤
      (n : ℝ) ^ (1 / (2 : ℝ) ^ (J + 2)) := by
    rw [Real.rpow_def_of_pos hnR]
    apply Real.exp_le_exp.mpr
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hE
  calc
    (g n : ℝ) ≤ Real.exp (Real.exp (uniformRankinBase * (4 + 16 * (J + 1 : ℕ)))) *
        (n : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (J + 1)) :=
      g_le_direct_support_rankin (J + 1) n (by omega) hn hnhi
    _ ≤ (n : ℝ) ^ (1 / (2 : ℝ) ^ (J + 2)) *
        (n : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (J + 1)) :=
      mul_le_mul_of_nonneg_right hpre (Real.rpow_nonneg hnR.le _)
    _ = _ := by
      rw [← Real.rpow_add hnR]
      congr 1
      rw [show J + 2 = (J + 1) + 1 by omega, pow_succ]
      field_simp
      ring

/-- An unconditional all-input upper bound with an exponent loss of order
`1 / log(log n)`. The loss tends to zero and does not negate Erdős 821. -/
theorem eventually_g_le_power_loglog_loss :
    ∀ᶠ n : ℕ in atTop,
      (g n : ℝ) ≤ (n : ℝ) ^
        (1 - 1 / (2 : ℝ) ^ (Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 2)) := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp eventually_g_le_power_on_iterated_windows
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ (2 ^ (J₀ + 1))))] with n hn
  let M := Nat.log 2 n
  let L := Nat.log 2 M
  let J := Nat.log 2 L
  have hM : 2 ^ (2 ^ (J₀ + 1)) ≤ M := Nat.le_log_of_pow_le (by decide) hn
  have hL : 2 ^ (J₀ + 1) ≤ L := Nat.le_log_of_pow_le (by decide) hM
  have hJ : J₀ + 1 ≤ J := Nat.le_log_of_pow_le (by decide) hL
  have hn0 : n ≠ 0 := by have := (pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hn; omega
  have hM0 : M ≠ 0 := by have := (pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hM; omega
  have hL0 : L ≠ 0 := by have := (pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hL; omega
  have hlo : 2 ^ (2 ^ (2 ^ J)) ≤ n := by
    have h1 : 2 ^ J ≤ L := Nat.pow_log_le_self 2 hL0
    have h2 : 2 ^ L ≤ M := Nat.pow_log_le_self 2 hM0
    have h3 : 2 ^ M ≤ n := Nat.pow_log_le_self 2 hn0
    exact (Nat.pow_le_pow_right (by decide)
      ((Nat.pow_le_pow_right (by decide) h1).trans h2)).trans h3
  have hhi : n ≤ 2 ^ (2 ^ (2 ^ (J + 1))) := by
    have h1 : L < 2 ^ (J + 1) := Nat.lt_pow_succ_log_self (by decide) L
    have h2 : M < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) M
    have h3 : n < 2 ^ (M + 1) := Nat.lt_pow_succ_log_self (by decide) n
    have hMlt : M < 2 ^ (2 ^ (J + 1)) := h2.trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
    exact h3.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  exact hJ₀ J (by omega) n hlo hhi

/-- The new exponent loss vanishes. In particular this upper bound does
not supply any fixed positive exponent loss for a disproof. -/
lemma tendsto_support_rankin_exponent_loss :
    Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^
      (Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 2)) atTop (nhds 0) := by
  have hJ := tendsto_nat_log_two_atTop.comp
    (tendsto_nat_log_two_atTop.comp tendsto_nat_log_two_atTop)
  have hpow : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := (hpow.comp hJ).mul_const ((1 / 2 : ℝ) ^ (2 : ℕ))
  simpa only [Function.comp_apply, mul_zero, zero_mul, one_div_pow, pow_add, mul_inv_rev,
    one_div, inv_pow, mul_comm] using h

#print axioms sum_prime_inv_iterated_dyadic_le
#print axioms sum_primeFactors_weight_le_at_iterated_scale
#print axioms g_le_direct_support_rankin
#print axioms eventually_g_le_power_on_iterated_windows
#print axioms eventually_g_le_power_loglog_loss
#print axioms tendsto_support_rankin_exponent_loss

end Erdos821
