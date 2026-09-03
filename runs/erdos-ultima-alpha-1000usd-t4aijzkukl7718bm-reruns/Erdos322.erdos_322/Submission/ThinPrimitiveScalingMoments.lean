import Submission.PositivePrimitiveScalingFiniteMoments

/-! Power-saving finite-moment asymptotics are compatible with polynomial
peaks for abstract counts satisfying exact primitive scaling. -/
namespace Erdos322Research.ThinPrimitiveScalingMoments

open Finset ScalingFiniteMoments PrimitiveScalingFiniteMoments
  PositivePrimitiveScalingFiniteMoments Erdos322.MomentReduction
set_option Elab.async false
set_option maxHeartbeats 1000000

lemma fullSpike_nonzero_spec (k D n : ℕ) (hk : 0 < k)
    (hD : ¬ k ∣ D) (hn : fullSpike k D n ≠ 0) :
    ∃ p b : ℕ, p.Prime ∧ 0 < b ∧ p^D*b^k=n ∧ fullSpike k D n=p := by
  classical
  have hpos : 0 < ∑ b ∈ n.divisors.filter (fun b => b^k ∣ n),
      primitiveSpike D (n/b^k) := Nat.pos_of_ne_zero hn
  obtain ⟨b,hbS,hbval⟩ := Finset.sum_pos_iff.mp hpos
  have hb : 0 < b := Nat.pos_of_mem_divisors (mem_filter.mp hbS).1
  let p := primitiveSpike D (n/b^k)
  have hp := primitiveSpike_nonzero D (n/b^k) hbval.ne'
  have hbe : p^D*b^k=n := by
    rw [hp.2]
    exact Nat.div_mul_cancel (mem_filter.mp hbS).2
  refine ⟨p,b,hp.1,hb,hbe,?_⟩
  unfold fullSpike
  apply Finset.sum_eq_single b
  · intro c hcS hcb
    by_contra hcv
    have hc : 0 < c := Nat.pos_of_mem_divisors (mem_filter.mp hcS).1
    have hce : (primitiveSpike D (n/c^k))^D*c^k=n := by
      rw [(primitiveSpike_nonzero D (n/c^k) hcv).2]
      exact Nat.div_mul_cancel (mem_filter.mp hcS).2
    have hh := scaled_prime_power_unique k D p (primitiveSpike D (n/c^k)) b c hk hD
      hp.1 (primitiveSpike_nonzero D (n/c^k) hcv).1 hb hc (hbe.trans hce.symm)
    exact hcb hh.2.symm
  · exact fun h => (h hbS).elim

lemma weighted_power_fiber_card (k D q N p : ℕ) (hk : 0 < k)
    (hD : k*(q+2) ≤ D) (hp : 0 < p) :
    (((Finset.Icc 1 N).filter (fun b => p^D*b^k ≤ N)).card : ℝ) ≤
      (N : ℝ)^(1/(k : ℝ))/(p : ℝ)^(q+2) := by
  let T := (Finset.Icc 1 N).filter (fun b => p^D*b^k ≤ N)
  let R : ℝ := (N : ℝ)^(1/(k : ℝ))/(p : ℝ)^(q+2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsub : T ⊆ Finset.Icc 1 ⌊R⌋₊ := by
    intro b hb
    obtain ⟨hbN,hbe⟩ := mem_filter.mp hb
    have he : (p^(q+2)*b)^k ≤ N := by
      calc
        (p^(q+2)*b)^k = p^(k*(q+2))*b^k := by rw [mul_pow, ← pow_mul, Nat.mul_comm (q+2) k]
        _ ≤ p^D*b^k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp hD)
        _ ≤ N := hbe
    have hrpow : ((N : ℝ)^(1/(k : ℝ)))^k=N := by
      simpa only [one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hk.ne'
    have hex : (((p : ℝ)^(q+2)*(b : ℝ))^k) ≤
        ((N : ℝ)^(1/(k : ℝ)))^k := by
      rw [hrpow]
      exact_mod_cast he
    have hroot : (p : ℝ)^(q+2)*(b : ℝ) ≤ (N : ℝ)^(1/(k : ℝ)) :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) hk.ne').mp hex
    have hbR : (b : ℝ) ≤ R := by
      apply (le_div_iff₀ (pow_pos (by exact_mod_cast hp : (0 : ℝ) < p) _)).mpr
      simpa only [mul_comm] using hroot
    exact Finset.mem_Icc.mpr ⟨(mem_Icc.mp hbN).1,Nat.le_floor hbR⟩
  have hc : T.card ≤ ⌊R⌋₊ := by
    simpa [Nat.card_Icc] using Finset.card_le_card hsub
  exact (show (T.card : ℝ) ≤ (⌊R⌋₊ : ℝ) by exact_mod_cast hc).trans (Nat.floor_le hR)

/-- The positive-order spike moments have root-size, not merely linear, sums. -/
theorem spike_moment_root_bound (k D q N : ℕ) (hk : 0 < k)
    (hD : ¬ k ∣ D) (hq : 0 < q) (hDq : k*(q+2) ≤ D) :
    countMoment (fullSpike k D) q N ≤ momentConstant*(N : ℝ)^(1/(k : ℝ)) := by
  classical
  let S := Finset.Icc 1 N
  have hDpos : 0 < D := by
    have : 0 < k*(q+2) := Nat.mul_pos hk (by omega)
    omega
  have hterm (n : ℕ) (hn : n ∈ S) :
      (fullSpike k D n : ℝ)^q ≤
        ∑ p ∈ S, if ∃ b ∈ S, p^D*b^k=n then (p : ℝ)^q else 0 := by
    by_cases hf : fullSpike k D n=0
    · simp only [hf,Nat.cast_zero,zero_pow hq.ne']
      exact Finset.sum_nonneg (fun p _ => by split_ifs <;> positivity)
    obtain ⟨p,b,hp,hb,he,hval⟩ := fullSpike_nonzero_spec k D n hk hD hf
    have hnpos : 0 < n := (mem_Icc.mp hn).1
    have hpN : p ∈ S := by
      refine mem_Icc.mpr ⟨hp.pos,?_⟩
      have hpd : p ∣ n := (dvd_pow_self p hDpos.ne').trans ⟨b^k,he.symm⟩
      exact (Nat.le_of_dvd hnpos hpd).trans (mem_Icc.mp hn).2
    have hbN : b ∈ S := by
      refine mem_Icc.mpr ⟨hb,?_⟩
      calc
        b ≤ b^k := Nat.le_pow hk
        _ ≤ p^D*b^k := Nat.le_mul_of_pos_left _ (pow_pos hp.pos D)
        _ = n := he
        _ ≤ N := (mem_Icc.mp hn).2
    have hx : ∃ b ∈ S, p^D*b^k=n := ⟨b,hbN,he⟩
    have hs := Finset.single_le_sum (s := S)
      (f := fun p => if ∃ b ∈ S, p^D*b^k=n then (p : ℝ)^q else 0)
      (fun p _ => by dsimp only; split_ifs <;> positivity) hpN
    simpa only [hval,if_pos hx] using hs
  have hcard (p : ℕ) (hpS : p ∈ S) :
      ((S.filter (fun n => ∃ b ∈ S, p^D*b^k=n)).card : ℝ) ≤
        (N : ℝ)^(1/(k : ℝ))/(p : ℝ)^(q+2) := by
    let T := S.filter (fun b => p^D*b^k ≤ N)
    have hsub : S.filter (fun n => ∃ b ∈ S, p^D*b^k=n) ⊆
        T.image (fun b => p^D*b^k) := by
      intro n hn
      obtain ⟨hnS,b,hbS,he⟩ := mem_filter.mp hn
      apply mem_image.mpr
      exact ⟨b,mem_filter.mpr ⟨hbS,he ▸ (mem_Icc.mp hnS).2⟩,he⟩
    have hb : (S.filter (fun n => ∃ b ∈ S, p^D*b^k=n)).card ≤ T.card :=
      (Finset.card_le_card hsub).trans Finset.card_image_le
    exact (show ((S.filter (fun n => ∃ b ∈ S, p^D*b^k=n)).card : ℝ) ≤ T.card
      by exact_mod_cast hb).trans
      (weighted_power_fiber_card k D q N p hk hDq (mem_Icc.mp hpS).1)
  have hsum : ∑ p ∈ S, 1/(p : ℝ)^2 ≤ ∑' p : ℕ, 1/(p : ℝ)^2 :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum S
      (fun p _ => by positivity)
  calc
    countMoment (fullSpike k D) q N ≤
        ∑ n ∈ S, ∑ p ∈ S, if ∃ b ∈ S, p^D*b^k=n then (p : ℝ)^q else 0 :=
      Finset.sum_le_sum hterm
    _ = ∑ p ∈ S, ((S.filter (fun n => ∃ b ∈ S, p^D*b^k=n)).card : ℝ)*(p : ℝ)^q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ ∑ p ∈ S, ((N : ℝ)^(1/(k : ℝ))/(p : ℝ)^(q+2))*(p : ℝ)^q :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right (hcard p hp) (by positivity))
    _ = (N : ℝ)^(1/(k : ℝ))*(∑ p ∈ S, 1/(p : ℝ)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by have := (mem_Icc.mp hp).1; omega)
      rw [pow_add]
      field_simp
    _ ≤ (N : ℝ)^(1/(k : ℝ))*(∑' p : ℕ, 1/(p : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ momentConstant*(N : ℝ)^(1/(k : ℝ)) := by
      unfold momentConstant
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) N) (1/(k : ℝ))]

/-- Every prescribed low moment has leading term exactly `N`, with a
root-size error. The zeroth moment is included. -/
theorem finite_moment_power_saving (k D Q : ℕ) (hk : 0 < k)
    (hD : ¬ k ∣ D) (hDQ : k*(Q+2) ≤ D) :
    ∃ C > (0 : ℝ), ∀ q ≤ Q, ∀ N : ℕ,
      (N : ℝ) ≤ countMoment (positiveFull k D) q N ∧
      countMoment (positiveFull k D) q N ≤ (N : ℝ)+C*(N : ℝ)^(1/(k : ℝ)) := by
  have hC := momentConstant_pos
  refine ⟨2^Q*momentConstant, by positivity, ?_⟩
  intro q hq N
  have hlo : (N : ℝ) ≤ countMoment (positiveFull k D) q N := by
    calc
      (N : ℝ) = ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by simp [Nat.card_Icc]
      _ ≤ countMoment (positiveFull k D) q N := by
        apply Finset.sum_le_sum
        intro n hn
        exact one_le_pow₀ (by exact_mod_cast full_pos k D n (Finset.mem_Icc.mp hn).1)
  refine ⟨hlo, ?_⟩
  by_cases hq0 : q = 0
  · subst q
    simp only [countMoment, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [Nat.card_Icc, Nat.add_one_sub_one]
    exact le_add_of_nonneg_right (by positivity)
  have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (positiveFull k D n : ℝ)^q ≤ 1+2^Q*(fullSpike k D n : ℝ)^q := by
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    simp only [positiveFull, positiveBaseline, if_neg hn0, Nat.cast_add, Nat.cast_one]
    by_cases hs : fullSpike k D n = 0
    · simp [hs, hq0]
    have hs1 : (1 : ℝ) ≤ fullSpike k D n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
    calc
      (1+(fullSpike k D n : ℝ))^q ≤ (2*(fullSpike k D n : ℝ))^q := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
      _ = 2^q*(fullSpike k D n : ℝ)^q := mul_pow _ _ _
      _ ≤ 2^Q*(fullSpike k D n : ℝ)^q :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hq) (by positivity)
      _ ≤ 1+2^Q*(fullSpike k D n : ℝ)^q := by linarith
  have hDq : k*(q+2) ≤ D := (Nat.mul_le_mul_left k (by omega : q+2 ≤ Q+2)).trans hDQ
  calc
    countMoment (positiveFull k D) q N ≤
        ∑ n ∈ Finset.Icc 1 N, (1+2^Q*(fullSpike k D n : ℝ)^q) := Finset.sum_le_sum ht
    _ = (N : ℝ)+2^Q*countMoment (fullSpike k D) q N := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [countMoment, Nat.card_Icc]
    _ ≤ (N : ℝ)+2^Q*(momentConstant*(N : ℝ)^(1/(k : ℝ))) := by
      gcongr
      exact spike_moment_root_bound k D q N hk hD (Nat.pos_of_ne_zero hq0) hDq
    _ = (N : ℝ)+(2^Q*momentConstant)*(N : ℝ)^(1/(k : ℝ)) := by ring

/-- Exact primitive scaling and power-saving asymptotics for arbitrarily many
fixed moments do not imply a subpolynomial pointwise bound for abstract counts. -/
theorem power_saving_finite_moments_do_not_suffice (k Q : ℕ) (hk : 2 ≤ k) :
    ∃ f g : ℕ → ℕ,
      (∀ n, f n=∑ b ∈ n.divisors.filter (fun b => b^k ∣ n), g (n/b^k)) ∧
      (∀ n s, 0 < s → f n ≤ f (n*s^k)) ∧
      (∀ n, g n ≤ f n) ∧
      (∀ n, 0 < n → 1 ≤ f n) ∧
      (∃ C > (0 : ℝ), ∀ q ≤ Q, ∀ N : ℕ,
        (N : ℝ) ≤ countMoment f q N ∧
        countMoment f q N ≤ (N : ℝ)+C*(N : ℝ)^(1/(k : ℝ))) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (g n : ℝ)}.Infinite) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ)^c < (f n : ℝ)}.Infinite) := by
  let D := k*(Q+2)+1
  have hD : ¬ k ∣ D := by
    intro h
    have hm := Nat.mod_eq_zero_of_dvd h
    dsimp [D] at hm
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega : 1 < k)] at hm
    omega
  have hDQ : k*(Q+2) ≤ D := by dsimp [D]; omega
  have hDpos : 0 < D := by dsimp [D]; omega
  exact ⟨positiveFull k D, positivePrimitive k D,
    fun n => exact_scaling k D n (by omega),
    fun n s hs => power_scaling_monotone k D n s (by omega) hs,
    primitive_le_full k D, full_pos k D,
    finite_moment_power_saving k D Q (by omega) hD hDQ,
    primitive_peaks k D hDpos, full_peaks k D hDpos⟩

end Erdos322Research.ThinPrimitiveScalingMoments
