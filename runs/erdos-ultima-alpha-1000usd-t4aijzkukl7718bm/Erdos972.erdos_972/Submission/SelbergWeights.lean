import FormalConjecturesUtil

/-!
Finite Selberg weights for use with the local two-coordinate counting estimates.
This file develops sieve algebra, not a prime-pair lower bound.
-/
namespace Erdos972SelbergWeights

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

lemma sum_moebius_divisors (m : ℕ) :
    (∑ k ∈ m.divisors, (μ k : ℝ)) = if m = 1 then 1 else 0 := by
  change (∑ k ∈ m.divisors, (μ : ArithmeticFunction ℝ) k) = _
  rw [← coe_zeta_mul_apply, coe_zeta_mul_coe_moebius]
  simp only [ArithmeticFunction.one_apply]

lemma sum_divisors_between {R d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hmR : m ≤ R) (hdm : d ∣ m) (f : ℕ → ℝ) :
    (∑ k ∈ (Ioc 0 R).filter (fun k => d ∣ k ∧ k ∣ m), f (m / k)) =
      ∑ j ∈ (m / d).divisors, f ((m / d) / j) := by
  have hmd : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hdm) hd
  apply sum_bij' (fun k _ => k / d) (fun j _ => d * j)
  · intro k hk
    obtain ⟨hkI, hdk, hkm⟩ := mem_filter.mp hk
    apply Nat.mem_divisors.mpr
    exact ⟨Nat.div_dvd_div hdk hkm, hmd.ne'⟩
  · intro j hj
    have hjdvd := Nat.dvd_of_mem_divisors hj
    have hjpos := Nat.pos_of_mem_divisors hj
    have hmul : d * j ∣ m := (Nat.dvd_div_iff_mul_dvd hdm).mp hjdvd
    apply mem_filter.mpr
    exact ⟨mem_Ioc.mpr ⟨Nat.mul_pos hd hjpos, (Nat.le_of_dvd hm hmul).trans hmR⟩,
      dvd_mul_right d j, hmul⟩
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2.1
  · intro j _
    exact Nat.mul_div_cancel_left j hd
  · intro k hk
    congr 1
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' (mem_filter.mp hk).2.1]

lemma upper_moebius_coefficient {R d m : ℕ} (hd : d ∈ Ioc 0 R) (hm : m ∈ Ioc 0 R) :
    (∑ k ∈ Ioc 0 R, if d ∣ k ∧ k ∣ m then (μ (m / k) : ℝ) else 0) =
      if d = m then 1 else 0 := by
  have hd0 := (mem_Ioc.mp hd).1
  have hm0 := (mem_Ioc.mp hm).1
  by_cases hdm : d ∣ m
  · rw [← sum_filter, sum_divisors_between hd0 hm0 (mem_Ioc.mp hm).2 hdm (fun k => (μ k : ℝ)),
      Nat.sum_div_divisors (m / d) (fun k => (μ k : ℝ)), sum_moebius_divisors]
    have he : m / d = 1 ↔ d = m := by
      constructor
      · intro h
        have hh := Nat.mul_div_cancel' hdm
        simpa only [h, mul_one] using hh
      · rintro rfl
        exact Nat.div_self hm0
    simp only [he]
  · have he : d ≠ m := by rintro rfl; exact hdm dvd_rfl
    rw [if_neg he]
    apply sum_eq_zero
    intro k _
    exact if_neg (fun h => hdm (h.1.trans h.2))

noncomputable def upperMu (R : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 R, if d ∣ m then (μ (m / d) : ℝ) * y m else 0

lemma upper_moebius_inversion (R : ℕ) (y : ℕ → ℝ) {d : ℕ} (hd : d ∈ Ioc 0 R) :
    (∑ k ∈ Ioc 0 R, if d ∣ k then upperMu R y k else 0) = y d := by
  classical
  have hswap : (∑ k ∈ Ioc 0 R, if d ∣ k then upperMu R y k else 0) =
      ∑ m ∈ Ioc 0 R, ∑ k ∈ Ioc 0 R,
        if d ∣ k then (if k ∣ m then (μ (m / k) : ℝ) * y m else 0) else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    by_cases h : d ∣ k <;> simp [h, upperMu]
  rw [hswap]
  calc
    (∑ m ∈ Ioc 0 R, ∑ k ∈ Ioc 0 R,
      if d ∣ k then (if k ∣ m then (μ (m / k) : ℝ) * y m else 0) else 0) =
        ∑ m ∈ Ioc 0 R,
          (∑ k ∈ Ioc 0 R, if d ∣ k ∧ k ∣ m then (μ (m / k) : ℝ) else 0) * y m := by
      apply sum_congr rfl
      intro m _
      rw [sum_mul]
      apply sum_congr rfl
      intro k _
      split_ifs <;> simp_all
    _ = ∑ m ∈ Ioc 0 R, if d = m then y m else 0 := by
      apply sum_congr rfl
      intro m hm
      rw [upper_moebius_coefficient hd hm]
      split_ifs <;> simp
    _ = y d := by simp [hd]

noncomputable def sieveMass (R : ℕ) : ℝ :=
  ∑ m ∈ Ioc 0 R, (μ m : ℝ)^2 / m.totient

noncomputable def targetWeight (R m : ℕ) : ℝ :=
  (μ m : ℝ) / (m.totient * sieveMass R)

noncomputable def selbergWeight (R d : ℕ) : ℝ :=
  d * upperMu R (targetWeight R) d

lemma sieveMass_nonneg (R : ℕ) : 0 ≤ sieveMass R := by
  unfold sieveMass
  positivity

lemma one_le_sieveMass {R : ℕ} (hR : 1 ≤ R) : 1 ≤ sieveMass R := by
  have h1 : 1 ∈ Ioc 0 R := mem_Ioc.mpr ⟨by omega, hR⟩
  have h := single_le_sum (f := fun m : ℕ => (μ m : ℝ)^2 / m.totient)
    (s := Ioc 0 R) (fun _ _ => by positivity) h1
  simpa only [moebius_apply_one, Int.cast_one, one_pow, Nat.totient_one,
    Nat.cast_one, div_one, sieveMass] using h

lemma selbergWeight_one {R : ℕ} (hR : 1 ≤ R) : selbergWeight R 1 = 1 := by
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  simp only [selbergWeight, upperMu, targetWeight, Nat.cast_one, one_mul,
    one_dvd, if_true, Nat.div_one]
  calc
    (∑ m ∈ Ioc 0 R, (μ m : ℝ) * ((μ m : ℝ) / (m.totient * sieveMass R))) =
        ∑ m ∈ Ioc 0 R, ((μ m : ℝ)^2 / m.totient) / sieveMass R := by
      apply sum_congr rfl
      intro m _
      field_simp
    _ = sieveMass R / sieveMass R := (sum_div _ _ _).symm
    _ = 1 := div_self hG.ne'

lemma selbergWeight_eq_zero_of_lt {R d : ℕ} (hRd : R < d) :
    selbergWeight R d = 0 := by
  unfold selbergWeight upperMu
  have hz : (∑ m ∈ Ioc 0 R,
      if d ∣ m then (μ (m / d) : ℝ) * targetWeight R m else 0) = 0 := by
    apply sum_eq_zero
    intro m hm
    apply if_neg
    intro hdm
    have := Nat.le_of_dvd (mem_Ioc.mp hm).1 hdm
    have := (mem_Ioc.mp hm).2
    omega
  rw [hz, mul_zero]

lemma sum_selbergWeight_multiples (R : ℕ) {r : ℕ} (hr : r ∈ Ioc 0 R) :
    (∑ d ∈ Ioc 0 R, if r ∣ d then selbergWeight R d / d else 0) = targetWeight R r := by
  convert upper_moebius_inversion R (targetWeight R) hr using 1
  apply sum_congr rfl
  intro d hd
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Ioc.mp hd).1)
  simp only [selbergWeight, mul_div_cancel_left₀ _ hdR]

lemma abs_real_moebius_eq_sq (n : ℕ) : |(μ n : ℝ)| = (μ n : ℝ)^2 := by
  rw [← Int.cast_abs, ← Int.cast_pow, abs_moebius, moebius_sq]

lemma abs_selbergWeight_le {R : ℕ} (hR : 1 ≤ R) (d : ℕ) :
    |selbergWeight R d| ≤ d := by
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hbound (m : ℕ) :
      |if d ∣ m then (μ (m / d) : ℝ) * targetWeight R m else 0| ≤
        ((μ m : ℝ)^2 / m.totient) / sieveMass R := by
    by_cases hd : d ∣ m
    · rw [if_pos hd]
      have hmu : |(μ (m / d) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := m / d))
      have hden : 0 ≤ (m.totient : ℝ) * sieveMass R := by positivity
      simp only [targetWeight, abs_mul, abs_div, abs_of_nonneg hden,
        abs_real_moebius_eq_sq]
      rw [← div_mul_eq_div_div]
      exact mul_le_of_le_one_left (by positivity) (by rwa [← abs_real_moebius_eq_sq])
    · rw [if_neg hd, abs_zero]
      positivity
  have hU : |upperMu R (targetWeight R) d| ≤ 1 := by
    unfold upperMu
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum (fun m _ => hbound m)).trans
    rw [← sum_div]
    change sieveMass R / sieveMass R ≤ 1
    rw [div_self hG.ne']
  unfold selbergWeight
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d)]
  nlinarith [mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg (α := ℝ) d)]

lemma sum_totient_common_divisors {R d e : ℕ} (hd : d ∈ Ioc 0 R) (_he : e ∈ Ioc 0 R) :
    (∑ r ∈ Ioc 0 R, if r ∣ d ∧ r ∣ e then (r.totient : ℝ) else 0) = d.gcd e := by
  have hd0 := (mem_Ioc.mp hd).1
  have hg : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e hd0
  have hfilter : (Ioc 0 R).filter (fun r => r ∣ d ∧ r ∣ e) = (d.gcd e).divisors := by
    ext r
    simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hrd, hre⟩
      exact ⟨Nat.dvd_gcd hrd hre, hg.ne'⟩
    · rintro ⟨hrg, _⟩
      have hrd := hrg.trans (Nat.gcd_dvd_left d e)
      exact ⟨⟨Nat.pos_of_dvd_of_pos hrd hd0, (Nat.le_of_dvd hd0 hrd).trans (mem_Ioc.mp hd).2⟩,
        hrd, hrg.trans (Nat.gcd_dvd_right d e)⟩
  rw [← sum_filter, hfilter]
  exact_mod_cast Nat.sum_totient (d.gcd e)

lemma inv_lcm_eq_gcd_div {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    (d.lcm e : ℝ)⁻¹ = (d.gcd e : ℝ) / ((d : ℝ) * e) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have heR : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hlR : (d.lcm e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero hd.ne' he.ne')
  have hc : (d.gcd e : ℝ) * (d.lcm e : ℝ) = (d : ℝ) * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  field_simp
  nlinarith

noncomputable def quadraticMain (R : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Ioc 0 R, ∑ e ∈ Ioc 0 R, w d * w e / d.lcm e

lemma quadraticMain_diagonal (R : ℕ) (w : ℕ → ℝ) :
    quadraticMain R w = ∑ r ∈ Ioc 0 R,
      (r.totient : ℝ) * (∑ d ∈ Ioc 0 R, if r ∣ d then w d / d else 0)^2 := by
  let S := Ioc 0 R
  let f : ℕ → ℕ → ℝ := fun r d => if r ∣ d then w d / d else 0
  have hterm (d : ℕ) (hd : d ∈ S) (e : ℕ) (he : e ∈ S) :
      w d * w e / d.lcm e = ∑ r ∈ S, (r.totient : ℝ) * f r d * f r e := by
    have hi := inv_lcm_eq_gcd_div (mem_Ioc.mp hd).1 (mem_Ioc.mp he).1
    rw [div_eq_mul_inv, hi, ← sum_totient_common_divisors hd he]
    calc
      w d * w e * ((∑ r ∈ S, if r ∣ d ∧ r ∣ e then (r.totient : ℝ) else 0) /
          ((d : ℝ) * e)) =
          ∑ r ∈ S, w d * w e * ((if r ∣ d ∧ r ∣ e then (r.totient : ℝ) else 0) /
            ((d : ℝ) * e)) := by rw [sum_div, mul_sum]
      _ = _ := by
        apply sum_congr rfl
        intro r _
        dsimp [f]
        split_ifs <;> simp_all
        ring
  calc
    quadraticMain R w = ∑ d ∈ S, ∑ e ∈ S, ∑ r ∈ S,
        (r.totient : ℝ) * f r d * f r e := by
      apply sum_congr rfl
      intro d hd
      exact sum_congr rfl (fun e he => hterm d hd e he)
    _ = ∑ d ∈ S, ∑ r ∈ S, ∑ e ∈ S, (r.totient : ℝ) * f r d * f r e := by
      apply sum_congr rfl
      intro d _
      rw [sum_comm]
    _ = ∑ r ∈ S, ∑ d ∈ S, ∑ e ∈ S, (r.totient : ℝ) * f r d * f r e := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro r _
      simp_rw [← mul_sum, ← sum_mul, ← mul_sum]
      dsimp [f]
      ring

lemma quadraticMain_selbergWeight {R : ℕ} (hR : 1 ≤ R) :
    quadraticMain R (selbergWeight R) = 1 / sieveMass R := by
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  rw [quadraticMain_diagonal]
  calc
    (∑ r ∈ Ioc 0 R, (r.totient : ℝ) *
        (∑ d ∈ Ioc 0 R, if r ∣ d then selbergWeight R d / d else 0)^2) =
        ∑ r ∈ Ioc 0 R, ((μ r : ℝ)^2 / r.totient) / sieveMass R ^ 2 := by
      apply sum_congr rfl
      intro r hr
      rw [sum_selbergWeight_multiples R hr]
      have ht : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (mem_Ioc.mp hr).1)
      unfold targetWeight
      field_simp
    _ = sieveMass R / sieveMass R ^ 2 := (sum_div _ _ _).symm
    _ = 1 / sieveMass R := by field_simp

#print axioms upper_moebius_inversion
#print axioms selbergWeight_one
#print axioms abs_selbergWeight_le
#print axioms quadraticMain_selbergWeight

end Erdos972SelbergWeights
