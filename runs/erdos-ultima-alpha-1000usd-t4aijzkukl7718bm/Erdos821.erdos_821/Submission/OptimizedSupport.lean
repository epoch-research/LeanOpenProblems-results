import Submission.SupportRankin

/-!
# Optimizing the scale-dependent prime-support upper bound

These are auxiliary upper bounds, not a settlement of Erdős 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma sum_primeFactors_weight_le_flexible_scale (J n : ℕ) (e : ℝ)
    (he : 0 ≤ e) (he1 : e < 1) (hn : 0 < n) (hbound : n ≤ 2 ^ (2 ^ (2 ^ J))) :
    (∑ p ∈ n.primeFactors, (p : ℝ) ^ (-(1 - e))) ≤
      (2 : ℝ) ^ ((2 : ℝ) ^ J * e) * (2 + 8 * J) := by
  let T : ℕ := 2 ^ J
  let Y : ℕ := 2 ^ T
  let s : ℝ := 1 - e
  let F : ℝ := (2 : ℝ) ^ ((2 : ℝ) ^ J * e)
  have hF : 0 ≤ F := Real.rpow_nonneg (by norm_num) _
  let A := n.primeFactors.filter (fun p => p ≤ Y)
  let B := n.primeFactors.filter (fun p => ¬ p ≤ Y)
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hYpow : (Y : ℝ) ^ (1 - s) = F := by
    dsimp [Y, F]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    dsimp [T, s]
    push_cast
    ring
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
  have hsmall : (∑ p ∈ A, (p : ℝ) ^ (-s)) ≤ F * (1 + 8 * (J : ℝ)) := by
    calc
      _ ≤ ∑ p ∈ A, F * (p : ℝ)⁻¹ := by
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
      _ = F * ∑ p ∈ A, (p : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ F * ∑ p ∈ (Y + 1).primesBelow, ((p : ℕ) : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hAsub
            (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))) hF
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_prime_inv_iterated_dyadic_le J) hF
  have hlarge : (∑ p ∈ B, (p : ℝ) ^ (-s)) ≤ F := by
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
      _ = F := hYpow
  have hsum : (∑ p ∈ n.primeFactors, (p : ℝ) ^ (-s)) ≤ F * (2 + 8 * (J : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ Y)]
    change (∑ p ∈ A, (p : ℝ) ^ (-s)) + (∑ p ∈ B, (p : ℝ) ^ (-s)) ≤ _
    nlinarith
  exact hsum


lemma g_le_flexible_support_rankin (J n : ℕ) (e : ℝ)
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2) (hn : 0 < n) (hbound : n ≤ 2 ^ (2 ^ (2 ^ J))) :
    (g n : ℝ) ≤ Real.exp (Real.exp
      (uniformRankinBase * ((2 : ℝ) ^ ((2 : ℝ) ^ J * e) * (2 + 8 * J)))) *
        (n : ℝ) ^ (1 - e) := by
  have hp := finite_prime_euler_product_le_exp_weight n.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) (1 - e) (by linarith)
  have hw := sum_primeFactors_weight_le_flexible_scale J n e he (by linarith) hn hbound
  have hprod := hp.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hw uniformRankinBase_pos.le))
  exact (g_le_rpow_mul_exp_primeFactors n hn (1 - e) (by linarith)).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hprod) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma eventually_exp_weighted_geometric_budget (r c : ℝ) (hr : ‖r‖ < 2) :
    ∀ᶠ J : ℕ in atTop,
      Real.exp (c * r ^ (J + 1) * (2 + 8 * (J + 1 : ℕ))) * (2 : ℝ) ^ (J + 4) ≤
        Real.log 2 * (2 : ℝ) ^ (2 ^ J : ℕ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : Tendsto (fun J : ℕ => r ^ J / (2 : ℝ) ^ J) atTop (nhds 0) := by
    simpa only [pow_zero, one_mul] using
      (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) 0 hr).tendsto_div_nhds_zero
  have h1 : Tendsto (fun J : ℕ => (J : ℝ) * r ^ J / (2 : ℝ) ^ J) atTop (nhds 0) := by
    simpa only [pow_one] using
      (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (R := ℝ) 1 hr).tendsto_div_nhds_zero
  have hJ : Tendsto (fun J : ℕ => (J : ℝ) / (2 : ℝ) ^ J) atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have hone : Tendsto (fun J : ℕ => 1 / (2 : ℝ) ^ J) atTop (nhds 0) := by
    simpa only [pow_zero] using tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)
  have hlim : Tendsto (fun J : ℕ =>
      (c * r ^ (J + 1) * (2 + 8 * ((J + 1 : ℕ) : ℝ)) +
        ((J + 4 : ℕ) : ℝ) * Real.log 2 - Real.log (Real.log 2)) / (2 : ℝ) ^ J)
      atTop (nhds 0) := by
    convert (((h1.const_mul (8 * c * r)).add (h0.const_mul (10 * c * r))).add
      ((hJ.const_mul (Real.log 2)).add (hone.const_mul (4 * Real.log 2 - Real.log (Real.log 2)))))
      using 1 <;> try simp only [mul_zero, add_zero]
    ext J
    rw [pow_succ]
    push_cast
    ring
  filter_upwards [hlim.eventually (gt_mem_nhds hlog)] with J hJbound
  have hlin := ((div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ J)).mp hJbound).le
  have harg : c * r ^ (J + 1) * (2 + 8 * ((J + 1 : ℕ) : ℝ)) +
      ((J + 4 : ℕ) : ℝ) * Real.log 2 ≤
        Real.log (Real.log 2) + ((2 ^ J : ℕ) : ℝ) * Real.log 2 := by
    push_cast at hlin ⊢
    linarith
  have hexp := Real.exp_le_exp.mpr harg
  simpa only [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log hlog] using hexp

/-- Optimizing the weight improves the loss by a factor of order `J` on
the iterated-dyadic window. It remains a vanishing loss. -/
theorem eventually_g_le_optimized_power_on_windows :
    ∀ᶠ J : ℕ in atTop, ∀ n : ℕ,
      2 ^ (2 ^ (2 ^ J)) ≤ n → n ≤ 2 ^ (2 ^ (2 ^ (J + 1))) →
      (g n : ℝ) ≤ (n : ℝ) ^ (1 - (J + 1 : ℕ) / (2 : ℝ) ^ (J + 4)) := by
  let r : ℝ := (2 : ℝ) ^ (1 / 4 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr : ‖r‖ < 2 := by
    rw [Real.norm_of_nonneg hr0]
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (1 / 4 : ℝ) < 1)
    simpa only [Real.rpow_one] using h
  filter_upwards [eventually_exp_weighted_geometric_budget r uniformRankinBase hr] with J hbudget
  intro n hnlo hnhi
  have hn : 0 < n := (pow_pos (by decide : 0 < (2 : ℕ)) _).trans_le hnlo
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let e : ℝ := ((J + 1 : ℕ) : ℝ) / (4 * (2 : ℝ) ^ (J + 1))
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hehalf : e ≤ 1 / 2 := by
    have hJpow : ((J + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (J + 1) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := J + 1)).le
    dsimp [e]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hYpow : (2 : ℝ) ^ ((2 : ℝ) ^ (J + 1) * e) = r ^ (J + 1) := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    dsimp [e]
    field_simp
  have hid : e / 2 = ((J + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (J + 4) := by
    dsimp [e]
    rw [show J + 4 = (J + 1) + 3 by omega, pow_add]
    norm_num
    ring
  have hlogn : Real.log 2 * (2 : ℝ) ^ (2 ^ J : ℕ) ≤ Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ (2 ^ (2 ^ J)) : ℕ) : ℝ))
      (show ((2 ^ (2 ^ (2 ^ J)) : ℕ) : ℝ) ≤ n by exact_mod_cast hnlo)
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_comm] using h
  have hE : Real.exp (uniformRankinBase * (r ^ (J + 1) * (2 + 8 * (J + 1 : ℕ)))) ≤
      Real.log n / (2 : ℝ) ^ (J + 4) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_assoc] using hbudget.trans hlogn
  have hpre : Real.exp (Real.exp (uniformRankinBase *
      (r ^ (J + 1) * (2 + 8 * (J + 1 : ℕ))))) ≤ (n : ℝ) ^ (e / 2) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / (2 : ℝ) ^ (J + 4)) := by
        rw [Real.rpow_def_of_pos hnR]
        apply Real.exp_le_exp.mpr
        simpa only [div_eq_mul_inv, one_mul] using hE
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        rw [hid]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast (show 1 ≤ J + 1 by omega)
  have hg := g_le_flexible_support_rankin (J + 1) n e he hehalf hn hnhi
  rw [hYpow] at hg
  calc
    (g n : ℝ) ≤ Real.exp (Real.exp (uniformRankinBase *
        (r ^ (J + 1) * (2 + 8 * (J + 1 : ℕ))))) * (n : ℝ) ^ (1 - e) := hg
    _ ≤ (n : ℝ) ^ (e / 2) * (n : ℝ) ^ (1 - e) :=
      mul_le_mul_of_nonneg_right hpre (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (1 - e / 2) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
    _ = _ := by rw [hid]

/-- An unconditional all-input upper bound with an exponent loss of order
`log(log(log n)) / log(log n)`. The loss tends to zero and does not negate Erdős 821. -/
theorem eventually_g_le_optimized_power_loglog_loss :
    ∀ᶠ n : ℕ in atTop,
      (g n : ℝ) ≤ (n : ℝ) ^
        (1 - ((Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 1 : ℕ) : ℝ) /
          (2 : ℝ) ^ (Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 4)) := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp eventually_g_le_optimized_power_on_windows
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

/-- The optimized loss still tends to zero; it is not a fixed-power saving. -/
lemma tendsto_optimized_support_rankin_exponent_loss :
    Tendsto (fun n : ℕ =>
      ((Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 1 : ℕ) : ℝ) /
        (2 : ℝ) ^ (Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 4)) atTop (nhds 0) := by
  have hJ := tendsto_nat_log_two_atTop.comp
    (tendsto_nat_log_two_atTop.comp tendsto_nat_log_two_atTop)
  have h1 : Tendsto (fun j : ℕ => (j : ℝ) / (2 : ℝ) ^ j) atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)
  have h0 : Tendsto (fun j : ℕ => 1 / (2 : ℝ) ^ j) atTop (nhds 0) := by
    simpa only [pow_zero] using tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1 : ℝ) < 2)
  have hlim : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (j + 4))
      atTop (nhds 0) := by
    convert (h1.add h0).div_const ((2 : ℝ) ^ (4 : ℕ)) using 1 <;> try simp only [add_zero, zero_div]
    ext j
    push_cast
    rw [pow_add]
    ring
  exact hlim.comp hJ

#print axioms eventually_g_le_optimized_power_loglog_loss
#print axioms tendsto_optimized_support_rankin_exponent_loss
#print axioms g_le_flexible_support_rankin
#print axioms eventually_g_le_optimized_power_on_windows

end Erdos821
