import FormalConjecturesUtil

/-!
# Euler's four-term square obstruction

An elementary infinite descent proves that the product of four positive,
nonconstant terms of an arithmetic progression is not a square.  No coprimality
assumption on the progression is needed.  This file is independent of `Spec`.

The descent starts with `c² + 10a²b² = a⁴ + 9b⁴`.  After removing the gcd,
`(a² - 5b²)² - c² = 16b⁴` splits into coprime fourth powers.  This gives one
of the quartics with coefficient triples `(1,5,4)` or `(2,5,2)`, with either
sign.  All four cases lead to a positive `(1,5,4)` quartic with a smaller
second parameter.  Factoring `(2t² + 5v²)² - 4s² = 9v⁴` then returns to a
strictly smaller original quartic.  Strong induction on `max a b` finishes
this elementary argument.
-/

namespace Erdos672.Progression.FourTermDescent

set_option maxHeartbeats 4000000

private lemma square_split {x y z : ℕ} (hcop : x.Coprime y)
    (h : x * y = z ^ 2) : ∃ u v, x = u ^ 2 ∧ y = v ^ 2 ∧ z = u * v ∧ u.Coprime v := by
  have hi : IsUnit (gcd x y) := by
    apply Nat.isUnit_iff.mpr
    change x.gcd y = 1
    exact hcop.gcd_eq_one
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hi h
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow (a := y) (b := x)
    (by rw [gcd_comm]; exact hi) (by simpa [mul_comm] using h)
  have hz : z = u * v := by
    apply (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp
    simpa [hu, hv, mul_pow] using h.symm
  have huv : u.Coprime v := by
    have h' : (u ^ 2).Coprime (v ^ 2) := by simpa only [hu, hv] using hcop
    exact (Nat.coprime_pow_right_iff (by decide : 0 < 2) u v).mp
      ((Nat.coprime_pow_left_iff (by decide : 0 < 2) u (v ^ 2)).mp h')
  exact ⟨u, v, hu, hv, hz, huv⟩

private lemma pow4split {x y z : ℕ} (hcop : x.Coprime y)
    (h : x * y = z ^ 4) : ∃ u v, x = u ^ 4 ∧ y = v ^ 4 ∧ z = u * v ∧ u.Coprime v := by
  have hi : IsUnit (gcd x y) := by
    apply Nat.isUnit_iff.mpr
    change x.gcd y = 1
    exact hcop.gcd_eq_one
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hi h
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow (a := y) (b := x)
    (by rw [gcd_comm]; exact hi) (by simpa [mul_comm] using h)
  have hz : z = u * v := by
    apply (Nat.pow_left_inj (by decide : 4 ≠ 0)).mp
    simpa [hu, hv, mul_pow] using h.symm
  have huv : u.Coprime v := by
    have h' : (u ^ 4).Coprime (v ^ 4) := by simpa [hu, hv] using hcop
    exact (Nat.coprime_pow_right_iff (by decide : 0 < 4) u v).mp
      ((Nat.coprime_pow_left_iff (by decide : 0 < 4) u (v ^ 4)).mp h')
  exact ⟨u, v, hu, hv, hz, huv⟩

private lemma coefficient_pow4split {x y z k : ℕ} (hk : 0 < k)
    (hcop : x.Coprime y) (hxk : k.Coprime x) (h : x * y = k * z ^ 4) :
    ∃ u v, x = u ^ 4 ∧ y = k * v ^ 4 ∧ z = u * v ∧ u.Coprime v := by
  have hky : k ∣ y := hxk.dvd_of_dvd_mul_left (h ▸ dvd_mul_right k (z ^ 4))
  obtain ⟨y', hy'⟩ := hky
  have h' : x * y' = z ^ 4 := by
    apply Nat.mul_left_cancel hk
    nlinarith only [h, hy']
  have hc' : x.Coprime y' := hcop.of_dvd_right ⟨k, by simpa [mul_comm] using hy'⟩
  obtain ⟨u, v, hu, hv, hz, hc⟩ := pow4split hc' h'
  exact ⟨u, v, hu, by simpa [hv] using hy', hz, hc⟩

private lemma prime_square_power_split {x y z p : ℕ} (hp : p.Prime)
    (hcop : x.Coprime y) (h : x * y = p ^ 2 * z ^ 4) :
    (∃ u v, x = u ^ 4 ∧ y = p ^ 2 * v ^ 4 ∧ z = u * v ∧ u.Coprime v) ∨
    (∃ u v, y = u ^ 4 ∧ x = p ^ 2 * v ^ 4 ∧ z = u * v ∧ u.Coprime v) := by
  by_cases hx : p ∣ x
  · have hy : ¬p ∣ y := by
      intro hy
      have : p ∣ 1 := by simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hx hy
      exact hp.not_dvd_one this
    right
    apply coefficient_pow4split (pow_pos hp.pos _) hcop.symm
      ((hp.coprime_iff_not_dvd.mpr hy).pow_left 2)
    simpa [mul_comm] using h
  · left
    exact coefficient_pow4split (pow_pos hp.pos _) hcop
      ((hp.coprime_iff_not_dvd.mpr hx).pow_left 2) h

private lemma coprime_of_sum_product {x y : ℕ} (h : (x + y).Coprime (x * y)) :
    x.Coprime y := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  apply Nat.dvd_one.mp
  have hd : x.gcd y ∣ (x + y).gcd (x * y) :=
    Nat.dvd_gcd (dvd_add (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y))
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left x y) y)
  simpa [h.gcd_eq_one] using hd

private lemma split_halves {a c : ℕ} (hc : c < a) (hpar : a % 2 = c % 2) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = a ∧ y = x + c := by
  refine ⟨(a - c) / 2, (a - c) / 2 + c, ?_, ?_, ?_, rfl⟩ <;> omega

private lemma split_difference {a c : ℕ} (hc : c < a) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = 2 * a ∧ y = x + 2 * c := by
  refine ⟨a - c, a + c, ?_, ?_, ?_, ?_⟩ <;> omega

private lemma three_not_dvd_sum_squares {a b : ℕ} (hcop : a.Coprime b) :
    ¬3 ∣ a ^ 2 + b ^ 2 := by
  intro h
  have hm := Nat.mod_eq_zero_of_dvd h
  have ha := Nat.mod_lt a (by decide : 0 < 3)
  have hb := Nat.mod_lt b (by decide : 0 < 3)
  simp only [Nat.add_mod, Nat.pow_mod, Nat.mod_mod] at hm
  have hh : ¬(a % 3 = 0 ∧ b % 3 = 0) := by
    rintro ⟨ha, hb⟩
    have : 3 ∣ 1 := by
      simpa [hcop.gcd_eq_one] using
        Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hb)
    norm_num at this
  interval_cases a % 3 <;> interval_cases b % 3 <;> norm_num at hm
  all_goals omega

private lemma three_not_dvd_sum_ten {a b : ℕ} (hcop : a.Coprime b) :
    ¬3 ∣ a ^ 2 + 10 * b ^ 2 := by
  intro h
  apply three_not_dvd_sum_squares hcop
  apply Nat.dvd_of_mod_eq_zero
  have hm := Nat.mod_eq_zero_of_dvd h
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod, show 10 % 3 = 1 by decide,
    one_mul] using hm

private lemma three_not_dvd_four_sum_ten {a b : ℕ} (hcop : a.Coprime b) :
    ¬3 ∣ 4 * a ^ 2 + 10 * b ^ 2 := by
  intro h
  apply three_not_dvd_sum_squares hcop
  apply Nat.dvd_of_mod_eq_zero
  have hm := Nat.mod_eq_zero_of_dvd h
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod, show 10 % 3 = 1 by decide,
    show 4 % 3 = 1 by decide, one_mul] using hm

private lemma coprime_linear_sum {a b k m : ℕ} (hcop : a.Coprime b)
    (hk : k.Coprime b) : (k * a ^ 2 + m * b ^ 2).Coprime b := by
  rw [show m * b ^ 2 = (m * b) * b by ring, Nat.coprime_add_mul_right_left]
  exact hk.mul_left (hcop.pow_left 2)

private lemma first_to_quartic {t v s : ℕ} (ht : 0 < t) (hv : 0 < v)
    (hcop : t.Coprime v) (h : s ^ 2 = t ^ 4 + 5 * t ^ 2 * v ^ 2 + 4 * v ^ 4) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a.Coprime b ∧
      c ^ 2 + 10 * a ^ 2 * b ^ 2 = a ^ 4 + 9 * b ^ 4 ∧ max a b ≤ v := by
  by_cases hve : 2 ∣ v
  · obtain ⟨w, hw⟩ := hve
    have hw0 : 0 < w := by omega
    have htw : t.Coprime w := hcop.of_dvd_right ⟨2, by simpa [mul_comm] using hw⟩
    have htodd : t % 2 = 1 := by
      have hn : ¬2 ∣ t := by
        intro hdt
        have : 2 ∣ 1 := by simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hdt ⟨w, hw⟩
        norm_num at this
      have : t % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hn
      omega
    have hsodd : s % 2 = 1 := by
      have hm := congrArg (fun n : ℕ => n % 2) h
      simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod, hw, htodd] at hm
      have hsmod := Nat.mod_lt s (by decide : 0 < 2)
      interval_cases s % 2 <;> norm_num at hm
      all_goals rfl
    rw [hw] at h
    let A := t ^ 2 + 10 * w ^ 2
    have hA : A ^ 2 = s ^ 2 + 36 * w ^ 4 := by
      dsimp [A]
      nlinarith only [h]
    have hsA : s < A := by nlinarith [pow_pos hw0 4]
    have hpar : A % 2 = s % 2 := by
      dsimp [A]
      simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod, htodd, hsodd]
      norm_num
    obtain ⟨x, y, hx, hy, hsum, hdiff⟩ := split_halves hsA hpar
    have hprod : x * y = 9 * w ^ 4 := by nlinarith only [hA, hsum, hdiff]
    have hsumw : (x + y).Coprime w := by
      rw [hsum]
      simpa [A] using coprime_linear_sum (k := 1) (m := 10) htw (Nat.coprime_one_left w)
    have hsum3 : (x + y).Coprime 3 := by
      rw [hsum]
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr (three_not_dvd_sum_ten htw)).symm
    have hxy : x.Coprime y := coprime_of_sum_product (by
      rw [hprod]
      exact (hsum3.pow_right 2).mul_right (hsumw.pow_right 4))
    rcases prime_square_power_split Nat.prime_three hxy hprod with hh | hh
    all_goals
      obtain ⟨a, b, ha, hb, hab, habcop⟩ := hh
      have ha0 : 0 < a := by nlinarith only [hw0, hab]
      have hb0 : 0 < b := by nlinarith only [hw0, hab]
      refine ⟨a, b, t, ha0, hb0, ht, habcop, ?_, ?_⟩
      · dsimp [A] at hsum
        nlinarith only [hsum, ha, hb, hab, hw]
      · have ha_le : a ≤ w := by nlinarith only [hab, hb0]
        have hb_le : b ≤ w := by nlinarith only [hab, ha0]
        exact max_le (by omega) (by omega)
  · have hvodd : v % 2 = 1 := by
      have : v % 2 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hve
      omega
    let A := 2 * t ^ 2 + 5 * v ^ 2
    have hA : A ^ 2 = (2 * s) ^ 2 + 9 * v ^ 4 := by
      dsimp [A]
      nlinarith only [h]
    have hsA : 2 * s < A := by nlinarith [pow_pos hv 4]
    obtain ⟨x, y, hx, hy, hsum, hdiff⟩ := split_difference hsA
    have hprod : x * y = 9 * v ^ 4 := by nlinarith only [hA, hsum, hdiff]
    have hsumv : (x + y).Coprime v := by
      rw [hsum]
      have hc4 : Nat.Coprime 4 v := by
        exact (Nat.prime_two.coprime_iff_not_dvd.mpr hve).pow_left 2
      change (2 * (2 * t ^ 2 + 5 * v ^ 2)).Coprime v
      rw [show 2 * (2 * t ^ 2 + 5 * v ^ 2) = 4 * t ^ 2 + 10 * v ^ 2 by ring]
      exact coprime_linear_sum (k := 4) (m := 10) hcop hc4
    have hsum3 : (x + y).Coprime 3 := by
      apply Nat.Coprime.symm
      apply Nat.prime_three.coprime_iff_not_dvd.mpr
      rw [hsum]
      change ¬3 ∣ 2 * (2 * t ^ 2 + 5 * v ^ 2)
      rw [show 2 * (2 * t ^ 2 + 5 * v ^ 2) = 4 * t ^ 2 + 10 * v ^ 2 by ring]
      exact three_not_dvd_four_sum_ten hcop
    have hxy : x.Coprime y := coprime_of_sum_product (by
      rw [hprod]
      exact (hsum3.pow_right 2).mul_right (hsumv.pow_right 4))
    rcases prime_square_power_split Nat.prime_three hxy hprod with hh | hh
    all_goals
      obtain ⟨a, b, ha, hb, hab, habcop⟩ := hh
      have ha0 : 0 < a := by nlinarith only [hv, hab]
      have hb0 : 0 < b := by nlinarith only [hv, hab]
      refine ⟨a, b, 2 * t, ha0, hb0, by omega, habcop, ?_, ?_⟩
      · dsimp [A] at hsum
        nlinarith only [hsum, ha, hb, hab]
      · have ha_le : a ≤ v := by nlinarith only [hab, hb0]
        have hb_le : b ≤ v := by nlinarith only [hab, ha0]
        exact max_le ha_le hb_le

private lemma coefficient_square_split {x y z k : ℕ} (hk : 0 < k)
    (hcop : x.Coprime y) (hxk : k.Coprime x) (h : x * y = k * z ^ 2) :
    ∃ u v, x = u ^ 2 ∧ y = k * v ^ 2 ∧ z = u * v ∧ u.Coprime v := by
  have hky : k ∣ y := hxk.dvd_of_dvd_mul_left (h ▸ dvd_mul_right k (z ^ 2))
  obtain ⟨y', hy'⟩ := hky
  have h' : x * y' = z ^ 2 := by
    apply Nat.mul_left_cancel hk
    nlinarith only [h, hy']
  have hc' : x.Coprime y' := hcop.of_dvd_right ⟨k, by simpa [mul_comm] using hy'⟩
  obtain ⟨u, v, hu, hv, hz, hc⟩ := square_split hc' h'
  exact ⟨u, v, hu, by simpa [hv] using hy', hz, hc⟩

private lemma two_square_split {x y z : ℕ} (hcop : x.Coprime y)
    (h : x * y = 2 * z ^ 2) :
    (∃ u v, x = u ^ 2 ∧ y = 2 * v ^ 2 ∧ z = u * v ∧ u.Coprime v) ∨
    (∃ u v, y = u ^ 2 ∧ x = 2 * v ^ 2 ∧ z = u * v ∧ u.Coprime v) := by
  by_cases hx : 2 ∣ x
  · have hy : ¬2 ∣ y := by
      intro hy
      have : 2 ∣ 1 := by simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hx hy
      norm_num at this
    right
    exact coefficient_square_split (by decide) hcop.symm
      (Nat.prime_two.coprime_iff_not_dvd.mpr hy) (by simpa [mul_comm] using h)
  · left
    exact coefficient_square_split (by decide) hcop
      (Nat.prime_two.coprime_iff_not_dvd.mpr hx) h

private lemma not_both_dvd {a b p : ℕ} (hcop : a.Coprime b) (hp : p.Prime) :
    ¬(p ∣ a ∧ p ∣ b) := by
  rintro ⟨ha, hb⟩
  apply hp.not_dvd_one
  simpa [hcop.gcd_eq_one] using Nat.dvd_gcd ha hb

private lemma positive_second_mod {t v s : ℕ} (hcop : t.Coprime v)
    (h : s ^ 2 = 2 * t ^ 4 + 5 * t ^ 2 * v ^ 2 + 2 * v ^ 4) :
    t % 2 = 1 ∧ v % 2 = 1 ∧ s % 2 = 1 ∧ 3 ∣ s ∧ ¬3 ∣ t ∧ ¬3 ∣ v := by
  have hnb2 : ¬(t % 2 = 0 ∧ v % 2 = 0) := by
    simpa only [Nat.dvd_iff_mod_eq_zero] using not_both_dvd hcop Nat.prime_two
  have hodd : t % 2 = 1 ∧ v % 2 = 1 ∧ s % 2 = 1 := by
    have hm := congrArg (fun n : ℕ => n % 4) h
    simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] at hm
    have ht4 := Nat.mod_lt t (by decide : 0 < 4)
    have hv4 := Nat.mod_lt v (by decide : 0 < 4)
    have hs4 := Nat.mod_lt s (by decide : 0 < 4)
    have htlink : t % 2 = (t % 4) % 2 := by omega
    have hvlink : v % 2 = (v % 4) % 2 := by omega
    have hslink : s % 2 = (s % 4) % 2 := by omega
    interval_cases t % 4 <;> interval_cases v % 4 <;> interval_cases s % 4 <;>
      norm_num at hm <;> omega
  have hnb3 : ¬(t % 3 = 0 ∧ v % 3 = 0) := by
    simpa only [Nat.dvd_iff_mod_eq_zero] using not_both_dvd hcop Nat.prime_three
  have hthree : s % 3 = 0 ∧ t % 3 ≠ 0 ∧ v % 3 ≠ 0 := by
    have hm := congrArg (fun n : ℕ => n % 3) h
    simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] at hm
    have ht3 := Nat.mod_lt t (by decide : 0 < 3)
    have hv3 := Nat.mod_lt v (by decide : 0 < 3)
    have hs3 := Nat.mod_lt s (by decide : 0 < 3)
    interval_cases t % 3 <;> interval_cases v % 3 <;> interval_cases s % 3 <;>
      norm_num at hm <;> omega
  exact ⟨hodd.1, hodd.2.1, hodd.2.2, Nat.dvd_of_mod_eq_zero hthree.1,
    by simpa only [Nat.dvd_iff_mod_eq_zero] using hthree.2.1,
    by simpa only [Nat.dvd_iff_mod_eq_zero] using hthree.2.2⟩

private lemma square_mod_three {a : ℕ} (h : ¬3 ∣ a) : a ^ 2 % 3 = 1 := by
  have ha : a % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using h
  have hb := Nat.mod_lt a (by decide : 0 < 3)
  rw [Nat.pow_mod]
  interval_cases a % 3 <;> norm_num
  all_goals omega

private lemma positive_second_to_first_ordered {t v s : ℕ} (htv : v < t)
    (_hv : 0 < v) (hcop : t.Coprime v)
    (h : s ^ 2 = 2 * t ^ 4 + 5 * t ^ 2 * v ^ 2 + 2 * v ^ 4) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧
      c ^ 2 = a ^ 4 + 5 * a ^ 2 * b ^ 2 + 4 * b ^ 4 ∧ 3 * b ^ 2 < s := by
  obtain ⟨htodd, hvodd, hsodd, hs3, ht3, hv3⟩ := positive_second_mod hcop h
  let B := t ^ 2 - v ^ 2
  have hB : B + v ^ 2 = t ^ 2 := by
    dsimp [B]
    exact Nat.sub_add_cancel (Nat.pow_le_pow_left (by omega) 2)
  have hB0 : 0 < B := by nlinarith only [hB, htv]
  have ht2 : t ^ 2 % 2 = 1 := by simp [Nat.pow_mod, htodd]
  have hv2 : v ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hvodd]
  have hB2 : 2 ∣ B := Nat.dvd_of_mod_eq_zero (by omega)
  have hB3 : 3 ∣ B := Nat.dvd_of_mod_eq_zero (by
    have := square_mod_three ht3
    have := square_mod_three hv3
    omega)
  have hB6 : 6 ∣ B := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) hB2 hB3
  obtain ⟨D, hBD⟩ := hB6
  obtain ⟨z, hsz⟩ := hs3
  have hD : 0 < D := by omega
  have hrel : z ^ 2 = (t * v) ^ 2 + 8 * D ^ 2 := by
    have hh : s ^ 2 = (3 * (t * v)) ^ 2 + 2 * B ^ 2 := by
      nlinarith only [h, hB]
    rw [hsz, hBD] at hh
    nlinarith only [hh]
  have hzodd : z % 2 = 1 := by
    have hm := congrArg (fun n : ℕ => n % 2) hsz
    simp only [Nat.mul_mod, Nat.mod_mod, hsodd] at hm
    norm_num at hm
    omega
  have htvodd : (t * v) % 2 = 1 := by simp [Nat.mul_mod, htodd, hvodd]
  have hz : t * v < z := by nlinarith [sq_pos_of_pos hD]
  obtain ⟨x, y, hx, hy, hsum, hdiff⟩ := split_halves hz (by omega)
  have hprod : x * y = 2 * D ^ 2 := by nlinarith only [hrel, hsum, hdiff]
  have hzD : z.Coprime D := by
    apply Nat.coprime_of_dvd
    intro p hp hpz hpD
    have hpz2 : p ∣ z ^ 2 := hpz.trans (dvd_pow_self z (by decide : 2 ≠ 0))
    have hpD2 : p ∣ 8 * D ^ 2 := dvd_mul_of_dvd_right
      (hpD.trans (dvd_pow_self D (by decide : 2 ≠ 0))) 8
    have hpTV2 : p ∣ (t * v) ^ 2 := (Nat.dvd_add_iff_left hpD2).mpr (hrel ▸ hpz2)
    have hpTV : p ∣ t * v := hp.dvd_of_dvd_pow hpTV2
    have hpB : p ∣ B := hBD ▸ dvd_mul_of_dvd_right hpD 6
    rcases hp.dvd_mul.mp hpTV with hpt | hpv
    · have hpt2 : p ∣ t ^ 2 := hpt.trans (dvd_pow_self t (by decide : 2 ≠ 0))
      have hpv2 : p ∣ v ^ 2 := (Nat.dvd_add_iff_right hpB).mpr (hB ▸ hpt2)
      exact not_both_dvd hcop hp ⟨hpt, hp.dvd_of_dvd_pow hpv2⟩
    · have hpv2 : p ∣ v ^ 2 := hpv.trans (dvd_pow_self v (by decide : 2 ≠ 0))
      have hpt2 : p ∣ t ^ 2 := hB ▸ dvd_add hpB hpv2
      exact not_both_dvd hcop hp ⟨hp.dvd_of_dvd_pow hpt2, hpv⟩
  have hz2 : z.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr (by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega)).symm
  have hxy : x.Coprime y := coprime_of_sum_product (by
    rw [hprod, hsum]
    exact hz2.mul_right (hzD.pow_right 2))
  rcases two_square_split hxy hprod with hh | hh
  all_goals
    obtain ⟨a, b, ha, hb, hab, habcop⟩ := hh
    have ha0 : 0 < a := by nlinarith only [hD, hab]
    have hb0 : 0 < b := by nlinarith only [hD, hab]
    have hsum' : a ^ 2 + 2 * b ^ 2 = z := by omega
    have hc2 : 2 ∣ t ^ 2 + v ^ 2 := Nat.dvd_of_mod_eq_zero (by
      have hm : (t ^ 2 + v ^ 2) % 2 = 0 := by simp [Nat.add_mod, ht2, hv2]
      exact hm)
    obtain ⟨c, hc⟩ := hc2
    refine ⟨a, b, c, ha0, hb0, habcop, ?_, ?_⟩
    · nlinarith only [hB, hBD, hab, hdiff, ha, hb, hc]
    · nlinarith only [hsum', hsz, ha0]

private lemma positive_second_to_first {t v s : ℕ} (ht : 0 < t) (hv : 0 < v)
    (hne : t ≠ v) (hcop : t.Coprime v)
    (h : s ^ 2 = 2 * t ^ 4 + 5 * t ^ 2 * v ^ 2 + 2 * v ^ 4) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧
      c ^ 2 = a ^ 4 + 5 * a ^ 2 * b ^ 2 + 4 * b ^ 4 ∧ 3 * b ^ 2 < s := by
  rcases lt_or_gt_of_ne hne with htv | hvt
  · apply positive_second_to_first_ordered htv ht hcop.symm
    nlinarith only [h]
  · exact positive_second_to_first_ordered hvt hv hcop h

private lemma negative_first_mod_three {t v s : ℕ} (hcop : t.Coprime v)
    (h : s ^ 2 + t ^ 4 + 4 * v ^ 4 = 5 * t ^ 2 * v ^ 2) :
    3 ∣ s ∧ ¬3 ∣ t ∧ ¬3 ∣ v := by
  have hnb : ¬(t % 3 = 0 ∧ v % 3 = 0) := by
    simpa only [Nat.dvd_iff_mod_eq_zero] using not_both_dvd hcop Nat.prime_three
  have hm := congrArg (fun n : ℕ => n % 3) h
  simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] at hm
  have ht3 := Nat.mod_lt t (by decide : 0 < 3)
  have hv3 := Nat.mod_lt v (by decide : 0 < 3)
  have hs3 := Nat.mod_lt s (by decide : 0 < 3)
  simp only [Nat.dvd_iff_mod_eq_zero]
  interval_cases t % 3 <;> interval_cases v % 3 <;> interval_cases s % 3 <;>
    norm_num at hm <;> omega

private lemma negative_first_to_first {t v s : ℕ} (_ht : 0 < t) (_hv : 0 < v)
    (hs : 0 < s) (hcop : t.Coprime v)
    (h : s ^ 2 + t ^ 4 + 4 * v ^ 4 = 5 * t ^ 2 * v ^ 2) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧
      c ^ 2 = a ^ 4 + 5 * a ^ 2 * b ^ 2 + 4 * b ^ 4 ∧ b < v := by
  have hst : 0 < s ^ 2 := pow_pos hs _
  have hlow : v ^ 2 < t ^ 2 := by
    by_contra hh
    have hd : v ^ 2 - t ^ 2 + t ^ 2 = v ^ 2 := Nat.sub_add_cancel (by omega)
    have hz : s ^ 2 + (v ^ 2 - t ^ 2) ^ 2 + 3 * v ^ 2 * (v ^ 2 - t ^ 2) = 0 := by
      nlinarith only [h, hd]
    nlinarith only [hz, hst]
  have hhigh : t ^ 2 < 4 * v ^ 2 := by
    by_contra hh
    have hd : t ^ 2 - 4 * v ^ 2 + 4 * v ^ 2 = t ^ 2 := Nat.sub_add_cancel (by omega)
    have hz : s ^ 2 + (t ^ 2 - 4 * v ^ 2) ^ 2 + 3 * v ^ 2 * (t ^ 2 - 4 * v ^ 2) = 0 := by
      nlinarith only [h, hd]
    nlinarith only [hz, hst]
  let X := t ^ 2 - v ^ 2
  let Y := 4 * v ^ 2 - t ^ 2
  have hX : X + v ^ 2 = t ^ 2 := Nat.sub_add_cancel (by omega)
  have hY : Y + t ^ 2 = 4 * v ^ 2 := Nat.sub_add_cancel (by omega)
  have hX0 : 0 < X := by omega
  have hY0 : 0 < Y := by omega
  obtain ⟨hs3, ht3, hv3⟩ := negative_first_mod_three hcop h
  have htmod := square_mod_three ht3
  have hvmod := square_mod_three hv3
  have hX3 : 3 ∣ X := Nat.dvd_of_mod_eq_zero (by omega)
  have hY3 : 3 ∣ Y := Nat.dvd_of_mod_eq_zero (by
    have hm : (4 * v ^ 2) % 3 = 1 := by simp [Nat.mul_mod, hvmod]
    omega)
  obtain ⟨x, hx⟩ := hX3
  obtain ⟨y, hy⟩ := hY3
  obtain ⟨z, hz⟩ := hs3
  have hx0 : 0 < x := by omega
  have hy0 : 0 < y := by omega
  have hsum : x + y = v ^ 2 := by nlinarith only [hX, hY, hx, hy]
  have htx : t ^ 2 = v ^ 2 + 3 * x := by omega
  have hprod : x * y = z ^ 2 := by
    have hh : X * Y = s ^ 2 := by nlinarith only [h, hX, hY]
    rw [hx, hy, hz] at hh
    nlinarith only [hh]
  have hxy : x.Coprime y := by
    apply Nat.coprime_of_dvd
    intro p hp hpx hpy
    have hpv2 : p ∣ v ^ 2 := hsum ▸ dvd_add hpx hpy
    have hpt2 : p ∣ t ^ 2 := htx ▸ dvd_add hpv2 (dvd_mul_of_dvd_right hpx 3)
    exact not_both_dvd hcop hp ⟨hp.dvd_of_dvd_pow hpt2, hp.dvd_of_dvd_pow hpv2⟩
  obtain ⟨u, w, hu, hw, _, huw⟩ := square_split hxy hprod
  have hu0 : 0 < u := by nlinarith only [hx0, hu]
  have hw0 : 0 < w := by nlinarith only [hy0, hw]
  have hv2 : v ^ 2 = u ^ 2 + w ^ 2 := by omega
  have ht2 : t ^ 2 = 4 * u ^ 2 + w ^ 2 := by omega
  refine ⟨w, u, t * v, hw0, hu0, huw.symm, ?_, ?_⟩
  · calc
      (t * v) ^ 2 = t ^ 2 * v ^ 2 := by ring
      _ = w ^ 4 + 5 * w ^ 2 * u ^ 2 + 4 * u ^ 4 := by rw [ht2, hv2]; ring
  · nlinarith only [hv2, hw0]

private lemma negative_second_to_positive_second {t v s : ℕ} (_ht : 0 < t)
    (_hv : 0 < v) (hs : 0 < s) (hne : t ≠ v) (hcop : t.Coprime v)
    (h : s ^ 2 + 2 * t ^ 4 + 2 * v ^ 4 = 5 * t ^ 2 * v ^ 2) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ a.Coprime b ∧
      (3 * (t * v)) ^ 2 = 2 * a ^ 4 + 5 * a ^ 2 * b ^ 2 + 2 * b ^ 4 := by
  have hst : 0 < s ^ 2 := pow_pos hs _
  have hlow : v ^ 2 < 2 * t ^ 2 := by
    by_contra hh
    have hd : v ^ 2 - 2 * t ^ 2 + 2 * t ^ 2 = v ^ 2 := Nat.sub_add_cancel (by omega)
    have hz : s ^ 2 + 2 * (v ^ 2 - 2 * t ^ 2) ^ 2 + 3 * t ^ 2 * (v ^ 2 - 2 * t ^ 2) = 0 := by
      nlinarith only [h, hd]
    nlinarith only [hz, hst]
  have hhigh : t ^ 2 < 2 * v ^ 2 := by
    by_contra hh
    have hd : t ^ 2 - 2 * v ^ 2 + 2 * v ^ 2 = t ^ 2 := Nat.sub_add_cancel (by omega)
    have hz : s ^ 2 + 2 * (t ^ 2 - 2 * v ^ 2) ^ 2 + 3 * v ^ 2 * (t ^ 2 - 2 * v ^ 2) = 0 := by
      nlinarith only [h, hd]
    nlinarith only [hz, hst]
  let X := 2 * t ^ 2 - v ^ 2
  let Y := 2 * v ^ 2 - t ^ 2
  have hX : X + v ^ 2 = 2 * t ^ 2 := Nat.sub_add_cancel (by omega)
  have hY : Y + t ^ 2 = 2 * v ^ 2 := Nat.sub_add_cancel (by omega)
  have hX0 : 0 < X := by omega
  have hY0 : 0 < Y := by omega
  have hprod : X * Y = s ^ 2 := by nlinarith only [h, hX, hY]
  have hsum : X + Y = t ^ 2 + v ^ 2 := by omega
  have hXY : 2 * X + Y = 3 * t ^ 2 := by omega
  have hYX : X + 2 * Y = 3 * v ^ 2 := by omega
  have hxy : X.Coprime Y := by
    let g := X.gcd Y
    have hgX : g ∣ X := Nat.gcd_dvd_left X Y
    have hgY : g ∣ Y := Nat.gcd_dvd_right X Y
    have hgT : g ∣ 3 * t ^ 2 := hXY ▸ dvd_add (dvd_mul_of_dvd_right hgX 2) hgY
    have hgV : g ∣ 3 * v ^ 2 := hYX ▸ dvd_add hgX (dvd_mul_of_dvd_right hgY 2)
    have hg3 : g ∣ 3 := by
      have hh := Nat.dvd_gcd hgT hgV
      rw [Nat.gcd_mul_left, (hcop.pow 2 2).gcd_eq_one, mul_one] at hh
      exact hh
    have hgS : g ∣ t ^ 2 + v ^ 2 := hsum ▸ dvd_add hgX hgY
    have hS3 : (t ^ 2 + v ^ 2).Coprime 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr (three_not_dvd_sum_squares hcop)).symm
    exact (hS3.of_dvd_left hgS).eq_one_of_dvd hg3
  obtain ⟨a, b, ha, hb, _, hab⟩ := square_split hxy hprod
  have ha0 : 0 < a := by nlinarith only [hX0, ha]
  have hb0 : 0 < b := by nlinarith only [hY0, hb]
  have hne' : a ≠ b := by
    intro heq
    have hh : t ^ 2 = v ^ 2 := by nlinarith only [hX, hY, ha, hb, heq]
    exact hne ((Nat.pow_left_inj (by decide : 2 ≠ 0)).mp hh)
  refine ⟨a, b, ha0, hb0, hne', hab, ?_⟩
  nlinarith only [hX, hY, ha, hb]

private lemma parity_of_square_relation {A c b : ℕ}
    (h : A ^ 2 = c ^ 2 + 16 * b ^ 4) : A % 2 = c % 2 := by
  have hm := congrArg (fun n : ℕ => n % 2) h
  simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] at hm
  have hA := Nat.mod_lt A (by decide : 0 < 2)
  have hc := Nat.mod_lt c (by decide : 0 < 2)
  interval_cases A % 2 <;> interval_cases c % 2 <;> norm_num at hm
  all_goals rfl

private lemma quartic_factor_cover {A b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hcop : A.Coprime b) (hfour : 2 ∣ A → 4 ∣ A)
    (h : A ^ 2 = c ^ 2 + 16 * b ^ 4) :
    (∃ t v : ℕ, 0 < t ∧ 0 < v ∧ t.Coprime v ∧ b = t * v ∧
      A = 4 * t ^ 4 + v ^ 4) ∨
    (∃ t v : ℕ, 0 < t ∧ 0 < v ∧ t.Coprime v ∧ b = t * v ∧
      A = 2 * t ^ 4 + 2 * v ^ 4 ∧ t ≠ v) := by
  have hcA : c < A := by nlinarith [pow_pos hb 4]
  by_cases hAe : 2 ∣ A
  · have hA4 : 4 ∣ A := hfour hAe
    obtain ⟨A', hAA'⟩ := hA4
    have hc4 : 4 ∣ c := by
      apply (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
      have hh : 16 ∣ c ^ 2 := by
        apply (Nat.dvd_add_iff_left (dvd_mul_right 16 (b ^ 4))).mpr
        rw [← h, hAA']
        exact ⟨A' ^ 2, by ring⟩
      exact hh
    obtain ⟨c', hcc'⟩ := hc4
    have hh : A' ^ 2 = c' ^ 2 + b ^ 4 := by
      rw [hAA', hcc'] at h
      nlinarith only [h]
    have hcA' : c' < A' := by nlinarith [pow_pos hb 4]
    obtain ⟨x, y, hx, hy, hsum, hdiff⟩ := split_difference hcA'
    have hprod : x * y = b ^ 4 := by nlinarith only [hh, hsum, hdiff]
    have hA'b : A'.Coprime b := hcop.of_dvd_left ⟨4, by simpa [mul_comm] using hAA'⟩
    have h2b : Nat.Coprime 2 b := by
      apply Nat.prime_two.coprime_iff_not_dvd.mpr
      intro h2
      exact not_both_dvd hcop Nat.prime_two ⟨hAe, h2⟩
    have hxy : x.Coprime y := coprime_of_sum_product (by
      rw [hprod, hsum]
      exact (h2b.mul_left hA'b).pow_right 4)
    obtain ⟨t, v, ht, hv, htv, htvco⟩ := pow4split hxy hprod
    have ht0 : 0 < t := by nlinarith only [hb, htv]
    have hv0 : 0 < v := by nlinarith only [hb, htv]
    have htvne : t ≠ v := by
      intro heq
      rw [heq] at ht
      have : c' = 0 := by nlinarith only [ht, hv, hdiff]
      omega
    right
    refine ⟨t, v, ht0, hv0, htvco, htv, ?_, htvne⟩
    nlinarith only [hAA', hsum, ht, hv]
  · have h2A : A.Coprime 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hAe).symm
    obtain ⟨x, y, hx, hy, hsum, hdiff⟩ := split_halves hcA (parity_of_square_relation h)
    have hprod : x * y = 4 * b ^ 4 := by nlinarith only [h, hsum, hdiff]
    have hxy : x.Coprime y := coprime_of_sum_product (by
      rw [hprod, hsum]
      exact (h2A.pow_right 2).mul_right (hcop.pow_right 4))
    rcases prime_square_power_split Nat.prime_two hxy hprod with hh | hh
    all_goals
      obtain ⟨v, t, hv, ht, htv, htvco⟩ := hh
      have ht0 : 0 < t := by nlinarith only [hb, htv]
      have hv0 : 0 < v := by nlinarith only [hb, htv]
      left
      refine ⟨t, v, ht0, hv0, htvco.symm, by simpa [mul_comm] using htv, ?_⟩
      nlinarith only [hsum, ht, hv]

private lemma quartic_covers {a b c : ℕ} (_ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hcop : a.Coprime b)
    (h : c ^ 2 + 10 * a ^ 2 * b ^ 2 = a ^ 4 + 9 * b ^ 4) :
    ∃ t v : ℕ, 0 < t ∧ 0 < v ∧ t.Coprime v ∧ b = t * v ∧
      ((a ^ 2 = v ^ 4 + 5 * v ^ 2 * t ^ 2 + 4 * t ^ 4) ∨
       (a ^ 2 = 2 * t ^ 4 + 5 * t ^ 2 * v ^ 2 + 2 * v ^ 4 ∧ t ≠ v) ∨
       (a ^ 2 + v ^ 4 + 4 * t ^ 4 = 5 * v ^ 2 * t ^ 2) ∨
       (a ^ 2 + 2 * t ^ 4 + 2 * v ^ 4 = 5 * t ^ 2 * v ^ 2 ∧ t ≠ v)) := by
  by_cases hlow : 5 * b ^ 2 ≤ a ^ 2
  · let A := a ^ 2 - 5 * b ^ 2
    have hA : A + 5 * b ^ 2 = a ^ 2 := Nat.sub_add_cancel hlow
    have hAcop : A.Coprime b := by
      have hh : (A + (5 * b) * b).Coprime b := by
        have he : A + (5 * b) * b = a ^ 2 := by nlinarith only [hA]
        rw [he]
        exact hcop.pow_left 2
      exact (Nat.coprime_add_mul_right_left A b (5 * b)).mp hh
    have hfour : 2 ∣ A → 4 ∣ A := by
      intro h2A
      have hnb : ¬(a % 2 = 0 ∧ b % 2 = 0) := by
        simpa only [Nat.dvd_iff_mod_eq_zero] using not_both_dvd hcop Nat.prime_two
      have hmod := congrArg (fun n : ℕ => n % 4) hA
      simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] at hmod
      have hA2 : A % 2 = 0 := Nat.mod_eq_zero_of_dvd h2A
      have ha4 := Nat.mod_lt a (by decide : 0 < 4)
      have hb4 := Nat.mod_lt b (by decide : 0 < 4)
      have hA4 := Nat.mod_lt A (by decide : 0 < 4)
      have halink : a % 2 = (a % 4) % 2 := by omega
      have hblink : b % 2 = (b % 4) % 2 := by omega
      have hAlink : A % 2 = (A % 4) % 2 := by omega
      apply Nat.dvd_of_mod_eq_zero
      interval_cases a % 4 <;> interval_cases b % 4 <;> interval_cases A % 4 <;>
        norm_num at hmod <;> omega
    have hrel : A ^ 2 = c ^ 2 + 16 * b ^ 4 := by nlinarith only [h, hA]
    rcases quartic_factor_cover hb hc hAcop hfour hrel with hh | hh
    · obtain ⟨t, v, ht, hv, htv, hb', hA'⟩ := hh
      refine ⟨t, v, ht, hv, htv, hb', Or.inl ?_⟩
      rw [hb'] at hA
      nlinarith only [hA, hA']
    · obtain ⟨t, v, ht, hv, htv, hb', hA', hne⟩ := hh
      refine ⟨t, v, ht, hv, htv, hb', Or.inr (Or.inl ⟨?_, hne⟩)⟩
      rw [hb'] at hA
      nlinarith only [hA, hA']
  · let A := 5 * b ^ 2 - a ^ 2
    have hA : A + a ^ 2 = 5 * b ^ 2 := Nat.sub_add_cancel (by omega)
    have hAcop : A.Coprime b := by
      apply Nat.coprime_of_dvd
      intro p hp hpA hpb
      have hpb2 : p ∣ 5 * b ^ 2 := dvd_mul_of_dvd_right (dvd_pow hpb (by decide : 2 ≠ 0)) 5
      have hpa2 : p ∣ a ^ 2 := (Nat.dvd_add_iff_right hpA).mpr (hA ▸ hpb2)
      exact not_both_dvd hcop hp ⟨hp.dvd_of_dvd_pow hpa2, hpb⟩
    have hfour : 2 ∣ A → 4 ∣ A := by
      intro h2A
      have hnb : ¬(a % 2 = 0 ∧ b % 2 = 0) := by
        simpa only [Nat.dvd_iff_mod_eq_zero] using not_both_dvd hcop Nat.prime_two
      have hmod := congrArg (fun n : ℕ => n % 4) hA
      simp only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] at hmod
      have hA2 : A % 2 = 0 := Nat.mod_eq_zero_of_dvd h2A
      have ha4 := Nat.mod_lt a (by decide : 0 < 4)
      have hb4 := Nat.mod_lt b (by decide : 0 < 4)
      have hA4 := Nat.mod_lt A (by decide : 0 < 4)
      have halink : a % 2 = (a % 4) % 2 := by omega
      have hblink : b % 2 = (b % 4) % 2 := by omega
      have hAlink : A % 2 = (A % 4) % 2 := by omega
      apply Nat.dvd_of_mod_eq_zero
      interval_cases a % 4 <;> interval_cases b % 4 <;> interval_cases A % 4 <;>
        norm_num at hmod <;> omega
    have hrel : A ^ 2 = c ^ 2 + 16 * b ^ 4 := by nlinarith only [h, hA]
    rcases quartic_factor_cover hb hc hAcop hfour hrel with hh | hh
    · obtain ⟨t, v, ht, hv, htv, hb', hA'⟩ := hh
      refine ⟨t, v, ht, hv, htv, hb', Or.inr (Or.inr (Or.inl ?_))⟩
      rw [hb'] at hA
      nlinarith only [hA, hA']
    · obtain ⟨t, v, ht, hv, htv, hb', hA', hne⟩ := hh
      refine ⟨t, v, ht, hv, htv, hb', Or.inr (Or.inr (Or.inr ⟨?_, hne⟩))⟩
      rw [hb'] at hA
      nlinarith only [hA, hA']

private lemma quartic_to_first {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hcop : a.Coprime b)
    (h : c ^ 2 + 10 * a ^ 2 * b ^ 2 = a ^ 4 + 9 * b ^ 4) :
    ∃ t v s : ℕ, 0 < t ∧ 0 < v ∧ t.Coprime v ∧
      s ^ 2 = t ^ 4 + 5 * t ^ 2 * v ^ 2 + 4 * v ^ 4 ∧ v < max a b := by
  obtain ⟨t, v, ht, hv, htv, hb', hcases⟩ := quartic_covers ha hb hc hcop h
  rcases hcases with hfirst | ⟨hsecond, hne⟩ | hnegative | ⟨hnegative, hne⟩
  · have hb_lt : b < a := by
      apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp
      rw [hb']
      nlinarith only [hfirst, pow_pos ht 4]
    have ht_le : t ≤ b := by nlinarith only [hb', hv]
    exact ⟨v, t, a, hv, ht, htv.symm, hfirst,
      lt_of_le_of_lt ht_le (lt_of_lt_of_le hb_lt (le_max_left a b))⟩
  · obtain ⟨t', v', s', ht', hv', hcop', hfirst, hbound⟩ :=
      positive_second_to_first ht hv hne htv hsecond
    have hv'a : v' < a := by nlinarith only [hbound, hv']
    exact ⟨t', v', s', ht', hv', hcop', hfirst, lt_of_lt_of_le hv'a (le_max_left a b)⟩
  · obtain ⟨t', v', s', ht', hv', hcop', hfirst, hbound⟩ :=
      negative_first_to_first hv ht ha htv.symm hnegative
    have ht_le : t ≤ b := by nlinarith only [hb', hv]
    exact ⟨t', v', s', ht', hv', hcop', hfirst,
      lt_of_lt_of_le hbound (le_trans ht_le (le_max_right a b))⟩
  · obtain ⟨t', v', ht', hv', hne', hcop', hsecond⟩ :=
      negative_second_to_positive_second ht hv ha hne htv hnegative
    obtain ⟨t'', v'', s'', ht'', hv'', hcop'', hfirst, hbound⟩ :=
      positive_second_to_first ht' hv' hne' hcop' hsecond
    have hv''b : v'' < b := by nlinarith only [hbound, hb', hv'']
    exact ⟨t'', v'', s'', ht'', hv'', hcop'', hfirst,
      lt_of_lt_of_le hv''b (le_max_right a b)⟩

private lemma quartic_to_smaller {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hcop : a.Coprime b)
    (h : c ^ 2 + 10 * a ^ 2 * b ^ 2 = a ^ 4 + 9 * b ^ 4) :
    ∃ a' b' c' : ℕ, 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ a'.Coprime b' ∧
      c' ^ 2 + 10 * a' ^ 2 * b' ^ 2 = a' ^ 4 + 9 * b' ^ 4 ∧ max a' b' < max a b := by
  obtain ⟨t, v, s, ht, hv, htv, hfirst, hbound⟩ := quartic_to_first ha hb hc hcop h
  obtain ⟨a', b', c', ha', hb', hc', hab', hq', hmax⟩ := first_to_quartic ht hv htv hfirst
  exact ⟨a', b', c', ha', hb', hc', hab', hq', lt_of_le_of_lt hmax hbound⟩

private theorem quartic_no_solution_coprime : ∀ m a b c : ℕ, max a b = m →
    0 < a → 0 < b → 0 < c → a.Coprime b →
    c ^ 2 + 10 * a ^ 2 * b ^ 2 = a ^ 4 + 9 * b ^ 4 → False := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a b c hm ha hb hc hcop h
    obtain ⟨a', b', c', ha', hb', hc', hcop', h', hlt⟩ := quartic_to_smaller ha hb hc hcop h
    exact ih (max a' b') (by omega) a' b' c' rfl ha' hb' hc' hcop' h'

/-- The quartic underlying Euler's four-term obstruction has no positive solution. -/
theorem quartic_no_solution {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    c ^ 2 + 10 * a ^ 2 * b ^ 2 ≠ a ^ 4 + 9 * b ^ 4 := by
  intro h
  obtain ⟨a', b', hcop, haa', hbb'⟩ := Nat.exists_coprime a b
  generalize hgg : a.gcd b = g at haa' hbb'
  have hg : 0 < g := by rw [← hgg]; exact Nat.gcd_pos_of_pos_left b ha
  have ha' : 0 < a' := by nlinarith only [ha, haa']
  have hb' : 0 < b' := by nlinarith only [hb, hbb']
  have hdR : g ^ 4 ∣ a ^ 4 + 9 * b ^ 4 := by
    refine ⟨a' ^ 4 + 9 * b' ^ 4, ?_⟩
    rw [haa', hbb']
    ring
  have hdM : g ^ 4 ∣ 10 * a ^ 2 * b ^ 2 := by
    refine ⟨10 * a' ^ 2 * b' ^ 2, ?_⟩
    rw [haa', hbb']
    ring
  have hdC : g ^ 4 ∣ c ^ 2 := (Nat.dvd_add_iff_left hdM).mpr (h ▸ hdR)
  have hgc : g ^ 2 ∣ c := by
    apply (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    simpa [← pow_mul] using hdC
  obtain ⟨c', hcc'⟩ := hgc
  have hc' : 0 < c' := by nlinarith only [hc, hcc']
  have h' : c' ^ 2 + 10 * a' ^ 2 * b' ^ 2 = a' ^ 4 + 9 * b' ^ 4 := by
    apply Nat.mul_left_cancel (pow_pos hg 4)
    calc
      g ^ 4 * (c' ^ 2 + 10 * a' ^ 2 * b' ^ 2) = c ^ 2 + 10 * a ^ 2 * b ^ 2 := by
        rw [hcc', haa', hbb']
        ring
      _ = a ^ 4 + 9 * b ^ 4 := h
      _ = g ^ 4 * (a' ^ 4 + 9 * b' ^ 4) := by
        rw [haa', hbb']
        ring
  exact quartic_no_solution_coprime (max a' b') a' b' c' rfl ha' hb' hc' hcop h'

end Erdos672.Progression.FourTermDescent

namespace Erdos672.Progression

/-- **Euler's four-term theorem**: four positive terms in a nonconstant
arithmetic progression cannot have square product.  No gcd hypothesis is needed. -/
theorem four_term_product_ne_square (n d q : ℕ) (hn : 0 < n) (hd : 0 < d) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  intro h
  have hprod : 0 < n * (n + d) * (n + 2 * d) * (n + 3 * d) := by positivity
  have hq : 0 < q := by nlinarith only [h, hprod]
  apply FourTermDescent.quartic_no_solution (a := 2 * n + 3 * d) (b := d) (c := 4 * q)
    (by omega) hd (by omega)
  nlinarith only [h]

/-- The `Finset.range 4` form of Euler's four-term square obstruction. -/
theorem range_four_product_ne_square (n d q : ℕ) (hn : 0 < n) (hd : 0 < d) :
    (∏ i ∈ Finset.range 4, (n + i * d)) ≠ q ^ 2 := by
  simpa [Finset.prod_range_succ] using four_term_product_ne_square n d q hn hd

end Erdos672.Progression
