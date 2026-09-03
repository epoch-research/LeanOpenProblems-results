import Submission.Explore

/-!
A contracting remainder map for comparisons whose two largest prime factors
have product greater than the index. It reverses the comparison outside the
prime-successor exception. The map is not injective and no density-preserving
property is claimed.
-/

namespace Erdos371

private lemma maxPrimeFac_prime_mul_small (p a : ℕ) (hp : p.Prime)
    (ha : 0 < a) (hap : a < p) : Nat.maxPrimeFac (p * a) = p := by
  rw [Nat.maxPrimeFac_mul hp.ne_zero ha.ne', hp.maxPrimeFac_eq_self]
  exact max_eq_left (Nat.maxPrimeFac_le.trans hap.le)

/-- A prime and a smaller cofactor select a falling CRT root. -/
lemma prime_cofactor_remainder_fall (n p b : ℕ) (hp : p.Prime)
    (hb : 1 < b) (hbp : b < p) (hpn : p ∣ n) (hbn : b ∣ n + 1) :
    0 < n % (p * b) ∧ Nat.maxPrimeFac (n % (p * b)) = p ∧
      Nat.maxPrimeFac (n % (p * b) + 1) < p := by
  let m := n % (p * b)
  have hmod := Nat.mod_modEq n (p * b)
  have hpm : p ∣ m := (hmod.dvd_iff (Nat.dvd_mul_right p b)).mpr hpn
  have hbm : b ∣ m + 1 := ((hmod.add_right 1).dvd_iff (Nat.dvd_mul_left b p)).mpr hbn
  have hm : m < p * b := Nat.mod_lt n (Nat.mul_pos hp.pos (by omega))
  have hm0 : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    rw [he, zero_add, Nat.dvd_one] at hbm
    omega
  have hm1 : m + 1 < p * b := by
    by_contra h
    have he : m + 1 = p * b := by omega
    have hd : p ∣ m + 1 := by rw [he]; exact Nat.dvd_mul_right p b
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hpm).mpr hd)
  have ha0 : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm0 hpm) hp.pos
  have hap : m / p < p :=
    ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by nlinarith : m < b * p)).trans hbp
  have hc0 : 0 < (m + 1) / b := Nat.div_pos (Nat.le_of_dvd (by omega) hbm) (by omega)
  have hcp : (m + 1) / b < p := (Nat.div_lt_iff_lt_mul (by omega)).mpr hm1
  refine ⟨hm0, ?_, ?_⟩
  · change Nat.maxPrimeFac m = p
    rw [← Nat.mul_div_cancel' hpm]
    exact maxPrimeFac_prime_mul_small p (m / p) hp ha0 hap
  · change Nat.maxPrimeFac (m + 1) < p
    rw [← Nat.mul_div_cancel' hbm, Nat.maxPrimeFac_mul (by omega : b ≠ 0) hc0.ne']
    exact max_lt (Nat.maxPrimeFac_le.trans_lt hbp) (Nat.maxPrimeFac_le.trans_lt hcp)

/-- Reversing the divisibility orientation selects a rising CRT root. -/
lemma prime_cofactor_remainder_rise (n p b : ℕ) (hp : p.Prime)
    (hb : 0 < b) (hbp : b < p) (hbn : b ∣ n) (hpn : p ∣ n + 1) :
    0 < n % (p * b) ∧ Nat.maxPrimeFac (n % (p * b)) < p ∧
      Nat.maxPrimeFac (n % (p * b) + 1) = p := by
  let m := n % (p * b)
  have hmod := Nat.mod_modEq n (p * b)
  have hbm : b ∣ m := (hmod.dvd_iff (Nat.dvd_mul_left b p)).mpr hbn
  have hpm : p ∣ m + 1 := ((hmod.add_right 1).dvd_iff (Nat.dvd_mul_right p b)).mpr hpn
  have hm : m < p * b := Nat.mod_lt n (Nat.mul_pos hp.pos hb)
  have hm0 : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    rw [he, zero_add] at hpm
    exact hp.not_dvd_one hpm
  have ha0 : 0 < m / b := Nat.div_pos (Nat.le_of_dvd hm0 hbm) hb
  have hap : m / b < p := (Nat.div_lt_iff_lt_mul hb).mpr hm
  have hc0 : 0 < (m + 1) / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpm) hp.pos
  have hcp : (m + 1) / p < p := by
    have he := Nat.mul_div_cancel' hpm
    have hb' : (m + 1) / p ≤ b := by nlinarith [hp.pos]
    exact hb'.trans_lt hbp
  refine ⟨hm0, ?_, ?_⟩
  · change Nat.maxPrimeFac m < p
    rw [← Nat.mul_div_cancel' hbm, Nat.maxPrimeFac_mul hb.ne' ha0.ne']
    exact max_lt (Nat.maxPrimeFac_le.trans_lt hbp) (Nat.maxPrimeFac_le.trans_lt hap)
  · change Nat.maxPrimeFac (m + 1) = p
    rw [← Nat.mul_div_cancel' hpm]
    exact maxPrimeFac_prime_mul_small p ((m + 1) / p) hp hc0 hcp

/-- Reduce modulo the smaller largest prime times the cofactor of the larger. -/
def primeCofactorDescent (n : ℕ) : ℕ :=
  if Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) then
    n % (Nat.maxPrimeFac n * primeCofactor (n + 1))
  else n % (Nat.maxPrimeFac (n + 1) * primeCofactor n)

/-- On the large-product region, excluding a prime successor, the map strictly
lowers the index, reverses its sign, and replaces the larger prime label by the
previous smaller label. The final inequality quantifies contraction when the
original prime factors are separated. -/
theorem primeCofactorDescent_structure (n : ℕ) (hn : 1 < n)
    (hsize : n < Nat.maxPrimeFac n * Nat.maxPrimeFac (n + 1))
    (hnot : ¬ (n + 1).Prime) :
    0 < primeCofactorDescent n ∧ primeCofactorDescent n < n ∧
    factorSign (primeCofactorDescent n) = -factorSign n ∧
    max (Nat.maxPrimeFac (primeCofactorDescent n))
        (Nat.maxPrimeFac (primeCofactorDescent n + 1)) =
      min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) ∧
    primeCofactorDescent n * max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) <
      (n + 1) * min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) := by
  let p := Nat.maxPrimeFac n
  let q := Nat.maxPrimeFac (n + 1)
  let a := primeCofactor n
  let b := primeCofactor (n + 1)
  have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hq : q.Prime := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hpa : p * a = n := maxPrimeFac_mul_primeCofactor n
  have hqb : q * b = n + 1 := maxPrimeFac_mul_primeCofactor (n + 1)
  have ha : 0 < a := by nlinarith
  have hb : 0 < b := by nlinarith
  have hdpa : p ∣ n := Nat.maxPrimeFac_dvd
  have hdqb : q ∣ n + 1 := Nat.maxPrimeFac_dvd
  have hda : a ∣ n := ⟨p, by nlinarith⟩
  have hdb : b ∣ n + 1 := ⟨q, by nlinarith⟩
  change n < p * q at hsize
  have hsize' : n + 1 < p * q := by
    by_contra h
    have he : n + 1 = p * q := by omega
    have hd : p ∣ n + 1 := by rw [he]; exact Nat.dvd_mul_right p q
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hdpa).mpr hd)
  have haq : a < q := by nlinarith [hp.pos]
  have hbp : b < p := by nlinarith [hq.pos]
  by_cases h : p < q
  · have hb1 : 1 < b := by
      by_contra hb1
      have he : b = 1 := by omega
      have hqn : q = n + 1 := by simpa [he] using hqb
      exact hnot (hqn ▸ hq)
    have hT : primeCofactorDescent n = n % (p * b) := by
      simp only [primeCofactorDescent, show Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) from h,
        if_true]
      rfl
    obtain ⟨hm0, hmp, hmq⟩ := prime_cofactor_remainder_fall n p b hp hb1 hbp hdpa hdb
    have hm : n % (p * b) < p * b := Nat.mod_lt _ (Nat.mul_pos hp.pos hb)
    have hMn : p * b ≤ n := by nlinarith
    have hsign : factorSign (n % (p * b)) = -factorSign n := by
      have hnew : ¬ Nat.maxPrimeFac (n % (p * b)) < Nat.maxPrimeFac (n % (p * b) + 1) := by omega
      simp only [factorSign, predicateSign, if_neg hnew,
        if_pos (show Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) from h)]
    rw [hT]
    refine ⟨hm0, hm.trans_le hMn, hsign, ?_, ?_⟩
    · change max _ _ = min p q
      rw [hmp, max_eq_left hmq.le, min_eq_left h.le]
    · change n % (p * b) * max p q < (n + 1) * min p q
      rw [max_eq_right h.le, min_eq_left h.le]
      have hm' := Nat.mul_lt_mul_of_pos_right hm hq.pos
      nlinarith
  · have hqp : q < p := by
      have hne : q ≠ p := consecutive_maxPrimeFac_ne n
      omega
    have hT : primeCofactorDescent n = n % (q * a) := by
      simp only [primeCofactorDescent, if_neg (show ¬ Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) from h)]
      rfl
    obtain ⟨hm0, hmp, hmq⟩ := prime_cofactor_remainder_rise n q a hq ha haq hda hdqb
    have hm : n % (q * a) < q * a := Nat.mod_lt _ (Nat.mul_pos hq.pos ha)
    have hMn : q * a < n := by nlinarith
    have hsign : factorSign (n % (q * a)) = -factorSign n := by
      have hnew : Nat.maxPrimeFac (n % (q * a)) < Nat.maxPrimeFac (n % (q * a) + 1) := by omega
      simp only [factorSign, predicateSign, if_pos hnew,
        if_neg (show ¬ Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) from h)]
      norm_num
    rw [hT]
    refine ⟨hm0, hm.trans hMn, hsign, ?_, ?_⟩
    · change max _ _ = min p q
      rw [hmq, max_eq_right hmp.le, min_eq_right hqp.le]
    · change n % (q * a) * max p q < (n + 1) * min p q
      rw [max_eq_left hqp.le, min_eq_right hqp.le]
      have hm' := Nat.mul_lt_mul_of_pos_right hm hp.pos
      nlinarith

/-- Prime successors are genuine exceptions: their remainder is zero. -/
lemma primeCofactorDescent_eq_zero_of_prime_successor (n : ℕ) (hp : (n + 1).Prime) :
    primeCofactorDescent n = 0 := by
  have h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) := by
    rw [hp.maxPrimeFac_eq_self]
    exact Nat.maxPrimeFac_le.trans_lt (Nat.lt_succ_self n)
  have hc : primeCofactor (n + 1) = 1 := by
    rw [primeCofactor, hp.maxPrimeFac_eq_self]
    exact Nat.div_self (by omega)
  rw [primeCofactorDescent, if_pos h, hc, mul_one]
  exact Nat.mod_eq_zero_of_dvd Nat.maxPrimeFac_dvd

lemma primeCofactorDescent_zero_iff (n : ℕ) (hn : 1 < n)
    (hsize : n < Nat.maxPrimeFac n * Nat.maxPrimeFac (n + 1)) :
    primeCofactorDescent n = 0 ↔ (n + 1).Prime := by
  constructor
  · intro hz
    by_contra hnot
    have hpos := (primeCofactorDescent_structure n hn hsize hnot).1
    omega
  · exact primeCofactorDescent_eq_zero_of_prime_successor n

/-- A power separation of the original labels gives a power contraction of
the index. This controls the image size, not the multiplicities of the map. -/
theorem primeCofactorDescent_power_bound (N n : ℕ) (δ : ℝ)
    (hN : 0 < N) (hn : 1 < n) (hnN : n < N)
    (hsize : n < Nat.maxPrimeFac n * Nat.maxPrimeFac (n + 1)) (hnot : ¬ (n + 1).Prime)
    (hsep : (N : ℝ)^δ * (min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) ≤
      (max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ)) :
    (primeCofactorDescent n : ℝ) < (N : ℝ)^(1 - δ) := by
  have h := (primeCofactorDescent_structure n hn hsize hnot).2.2.2.2
  have hr : (primeCofactorDescent n : ℝ) *
        (max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) <
      (n + 1 : ℕ) * (min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) := by
    exact_mod_cast h
  have hmin : (0 : ℝ) < (min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) := by
    exact_mod_cast lt_min (Nat.prime_maxPrimeFac_of_one_lt n hn).pos
      (Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)).pos
  have hnn : (n + 1 : ℕ) ≤ (N : ℝ) := by exact_mod_cast (show n + 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow := Real.rpow_pos_of_pos hNpos δ
  have hbound : (primeCofactorDescent n : ℝ) * (N : ℝ)^δ < N := by
    apply (mul_lt_mul_iff_left₀ hmin).mp
    calc
      _ = (primeCofactorDescent n : ℝ) *
          ((N : ℝ)^δ * (min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ)) := by ring
      _ ≤ (primeCofactorDescent n : ℝ) *
          (max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) :=
        mul_le_mul_of_nonneg_left hsep (Nat.cast_nonneg _)
      _ < (n + 1 : ℕ) * (min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) := hr
      _ ≤ (N : ℝ) * (min (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1)) : ℕ) :=
        mul_le_mul_of_nonneg_right hnn hmin.le
  rw [Real.rpow_sub hNpos, Real.rpow_one]
  exact (lt_div_iff₀ hpow).mpr hbound

/-- Staying below the endpoint does not make this map a pairing. These two
inputs satisfy the descent hypotheses but collide. -/
theorem primeCofactorDescent_collision :
    primeCofactorDescent 14 = 4 ∧ primeCofactorDescent 44 = 4 ∧
    14 < Nat.maxPrimeFac 14 * Nat.maxPrimeFac 15 ∧
    44 < Nat.maxPrimeFac 44 * Nat.maxPrimeFac 45 ∧
    ¬ Nat.Prime 15 ∧ ¬ Nat.Prime 45 := by
  decide +kernel

/-- A valid descent may leave the large-product region. The structure
lemma therefore cannot simply be iterated on every resulting index. -/
theorem primeCofactorDescent_leaves_large_product :
    245 < Nat.maxPrimeFac 245 * Nat.maxPrimeFac 246 ∧ ¬ Nat.Prime 246 ∧
    primeCofactorDescent 245 = 35 ∧
    Nat.maxPrimeFac 35 * Nat.maxPrimeFac 36 ≤ 35 ∧ primeCofactorDescent 35 = 5 := by
  decide +kernel

#print axioms prime_cofactor_remainder_fall
#print axioms prime_cofactor_remainder_rise
#print axioms primeCofactorDescent_structure
#print axioms primeCofactorDescent_collision
#print axioms primeCofactorDescent_zero_iff
#print axioms primeCofactorDescent_power_bound
#print axioms primeCofactorDescent_leaves_large_product

end Erdos371
