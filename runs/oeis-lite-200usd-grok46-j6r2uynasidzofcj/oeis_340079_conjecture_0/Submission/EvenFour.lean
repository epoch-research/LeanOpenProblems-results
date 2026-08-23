import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset Int

/-! Even four-prime case of the A340079 conjecture. -/

lemma cast_two_mul_sub' (q : ℕ) (hq : 1 ≤ q) :
    ((2 * q - 1 : ℕ) : ℤ) = 2 * (q : ℤ) - 1 := by
  have h2q : 1 ≤ 2 * q := by omega
  rw [Nat.cast_sub h2q]
  push_cast
  rfl

lemma three_prod_expand (q r s : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ((3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1 : ℕ) : ℤ) =
      24 * (q : ℤ) * r * s - 12 * (q * r + q * s + r * s)
        + 6 * (q + r + s) - 2 := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_one]
  rw [cast_two_mul_sub' q hq, cast_two_mul_sub' r hr, cast_two_mul_sub' s hs]
  ring

def evenCZ (q r : ℕ) : ℤ := 6 * (q : ℤ) * r - 3 * q - 3 * r + 1

def evenDeltaZ (q r s : ℕ) : ℤ :=
  6 * ((q : ℤ) * r + q * s + r * s) - 3 * (q + r + s) + 1

lemma evenCZ_pos {q r : ℕ} (hq : 5 ≤ q) (hr : 5 ≤ r) : 0 < evenCZ q r := by
  unfold evenCZ
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (5 : ℤ) ≤ r := by exact_mod_cast hr
  nlinarith

lemma evenDeltaZ_decomp (q r s : ℕ) :
    evenDeltaZ q r s = (s : ℤ) * (6 * q + 6 * r - 3) + evenCZ q r := by
  unfold evenDeltaZ evenCZ
  ring

lemma three_prod_eq_twelve_n_sub (q r s : ℕ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ((3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1 : ℕ) : ℤ) =
      12 * (2 * (q : ℤ) * r * s) - 2 * evenDeltaZ q r s := by
  rw [three_prod_expand q r s hq hr hs]
  unfold evenDeltaZ
  ring

lemma cancel_two_odd {n : ℕ} {a : ℤ} (_hodd : Odd n)
    (h : ((2 * n : ℕ) : ℤ) ∣ 2 * a) :
    (n : ℤ) ∣ a := by
  have h' : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; rfl
  rw [h'] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hk' : (2 : ℤ) * a = 2 * (↑n * k) := by
    convert hk using 1
    ring
  exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) hk'

lemma two_qrs_dvd_imp_delta {q r s : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (_hq5 : 5 ≤ q) (_hr5 : 5 ≤ r) (_hs5 : 5 ≤ s)
    (hdvd : (2 * q * r * s) ∣ 3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1) :
    (q * r * s : ℤ) ∣ evenDeltaZ q r s := by
  have hex := three_prod_eq_twelve_n_sub q r s hq.pos hr.pos hs.pos
  have hI : ((2 * q * r * s : ℕ) : ℤ) ∣
      ((3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1 : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdvd
  rw [hex] at hI
  have h12 : ((2 * q * r * s : ℕ) : ℤ) ∣ 12 * (2 * (q : ℤ) * r * s) := by
    refine ⟨12, ?_⟩
    push_cast; ring
  have hsub := Int.dvd_sub h12 hI
  have heq : 12 * (2 * (q : ℤ) * r * s) -
      (12 * (2 * (q : ℤ) * r * s) - 2 * evenDeltaZ q r s) =
      2 * evenDeltaZ q r s := by ring
  rw [heq] at hsub
  have hodd : Odd (q * r * s) :=
    ((hq.odd_of_ne_two (by omega)).mul (hr.odd_of_ne_two (by omega))).mul
      (hs.odd_of_ne_two (by omega))
  have : ((2 * (q * r * s) : ℕ) : ℤ) ∣ 2 * evenDeltaZ q r s := by
    convert hsub using 1
    push_cast; ring
  exact cancel_two_odd hodd this

lemma evenCZ_of_s_dvd {q r s : ℕ}
    (h : (s : ℤ) ∣ evenDeltaZ q r s) :
    (s : ℤ) ∣ evenCZ q r := by
  have hs : (s : ℤ) ∣ (s : ℤ) * (6 * q + 6 * r - 3) := dvd_mul_right _ _
  have hsub := Int.dvd_sub h hs
  have : evenDeltaZ q r s - (s : ℤ) * (6 * q + 6 * r - 3) = evenCZ q r := by
    rw [evenDeltaZ_decomp]; ring
  rwa [this] at hsub

lemma s_dvd_evenCZ_of_qrs_dvd {q r s : ℕ}
    (h : (q * r * s : ℤ) ∣ evenDeltaZ q r s) :
    (s : ℤ) ∣ evenCZ q r :=
  evenCZ_of_s_dvd (dvd_trans ⟨(q : ℤ) * r, by ring⟩ h)

lemma exists_t_of_s_dvd_C {q r s : ℕ}
    (h : (s : ℤ) ∣ evenCZ q r) :
    ∃ t : ℤ, evenCZ q r = s * t ∧
      evenDeltaZ q r s = s * (6 * q + 6 * r - 3 + t) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ht, ?_⟩
  rw [evenDeltaZ_decomp, ht]
  ring

lemma qrs_dvd_imp_qr_dvd_coeff {q r s : ℕ} {t : ℤ}
    (hΔ : evenDeltaZ q r s = s * (6 * q + 6 * r - 3 + t))
    (hdvd : (q * r * s : ℤ) ∣ evenDeltaZ q r s)
    (hspos : (0 : ℤ) < s) :
    (q * r : ℤ) ∣ (6 * q + 6 * r - 3 + t) := by
  rw [hΔ] at hdvd
  have hmul : (s * (q * r) : ℤ) ∣ s * (6 * q + 6 * r - 3 + t) := by
    convert hdvd using 1; ring
  exact (mul_dvd_mul_iff_left hspos.ne').1 hmul

lemma t_le_of_s_ge_r {q r s : ℕ} {t : ℤ}
    (hq : 5 ≤ q) (hr : 5 ≤ r) (hs : r ≤ s)
    (ht : evenCZ q r = (s : ℤ) * t) :
    t ≤ 6 * (q : ℤ) - 3 := by
  have hs' : (r : ℤ) ≤ s := by exact_mod_cast hs
  have hr0 : (0 : ℤ) < r := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 5) hr)
  have hs0 : (0 : ℤ) < s := lt_of_lt_of_le hr0 hs'
  have h1 : evenCZ q r ≤ (r : ℤ) * (6 * q - 3) := by
    unfold evenCZ
    nlinarith
  have : (s : ℤ) * t ≤ s * (6 * (q : ℤ) - 3) := by
    rw [← ht]
    nlinarith
  exact (mul_le_mul_iff_of_pos_left hs0).1 this

lemma t_pos_of_C_pos_s_pos {q r s : ℕ} {t : ℤ}
    (hC : 0 < evenCZ q r) (hs : 0 < s)
    (ht : evenCZ q r = (s : ℤ) * t) : 0 < t := by
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  nlinarith

lemma k_eq_one_or_two {q r : ℕ} {t k : ℤ}
    (hq : 5 ≤ q) (hr : 7 ≤ r)
    (ht : 0 < t) (htle : t ≤ 6 * (q : ℤ) - 3)
    (hk : 6 * (q : ℤ) + 6 * r - 3 + t = k * q * r) :
    k = 1 ∨ k = 2 := by
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (7 : ℤ) ≤ r := by exact_mod_cast hr
  have hlt : 6 * (q : ℤ) + 6 * r - 3 + t < 3 * q * r := by nlinarith
  have hkpos : 0 < k := by
    have lhs : (0 : ℤ) < 6 * q + 6 * r - 3 + t := by nlinarith
    nlinarith
  have hkle : k ≤ 2 := by
    have : k * q * r < 3 * q * r := by rwa [← hk]
    nlinarith
  omega

lemma exists_k_of_qr_dvd {q r : ℕ} {t : ℤ}
    (hdvd : (q * r : ℤ) ∣ (6 * q + 6 * r - 3 + t)) :
    ∃ k : ℤ, 6 * (q : ℤ) + 6 * r - 3 + t = k * q * r := by
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  convert hk using 1
  ring


lemma divisors_1501 : Nat.divisors 1501 = {1, 19, 79, 1501} := by native_decide
lemma divisors_3809 : Nat.divisors 3809 = {1, 13, 293, 3809} := by native_decide
lemma divisors_5359 : Nat.divisors 5359 = {1, 23, 233, 5359} := by native_decide

lemma natAbs_dvd_of_int_dvd {d n : ℤ} (h : d ∣ n) : d.natAbs ∣ n.natAbs :=
  Int.natAbs_dvd_natAbs.mpr h

lemma abs_dvd_mem_divisors {d : ℤ} {n : ℕ} (hn : n ≠ 0) (h : d ∣ (n : ℤ)) :
    d.natAbs ∈ Nat.divisors n :=
  Nat.mem_divisors.2 ⟨natAbs_dvd_of_int_dvd h, hn⟩

lemma prime_eq_five_seven_eleven_thirteen {q : ℕ}
    (hq : q.Prime) (h5 : 5 ≤ q) (h17 : q < 17) :
    q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 := by
  revert hq
  interval_cases q <;> decide

lemma prime_eq_seven_eleven_thirteen {r : ℕ}
    (hr : r.Prime) (h7 : 7 ≤ r) (h17 : r < 17) :
    r = 7 ∨ r = 11 ∨ r = 13 := by
  revert hr
  interval_cases r <;> decide

lemma seventeen_le_of_prime_gt_thirteen {q : ℕ} (hq : q.Prime) (h : 13 < q) : 17 ≤ q := by
  have hne14 : q ≠ 14 := fun eq ↦ (by decide : ¬ Nat.Prime 14) (eq ▸ hq)
  have hne15 : q ≠ 15 := fun eq ↦ (by decide : ¬ Nat.Prime 15) (eq ▸ hq)
  have hne16 : q ≠ 16 := fun eq ↦ (by decide : ¬ Nat.Prime 16) (eq ▸ hq)
  omega

lemma nineteen_le_of_prime_gt_seventeen {r : ℕ} (hr : r.Prime) (h : 17 < r) : 19 ≤ r := by
  have hne18 : r ≠ 18 := fun eq ↦ (by decide : ¬ Nat.Prime 18) (eq ▸ hr)
  omega

/-- k = 1 and q = 5 gives t < 0. -/
lemma k1_q5_t_neg {r : ℕ} {t : ℤ} (hr : 5 ≤ r)
    (heq : 6 * (5 : ℤ) + 6 * r - 3 + t = (5 : ℤ) * r) :
    t < 0 := by
  have hr' : (5 : ℤ) ≤ r := by exact_mod_cast hr
  nlinarith

/-- k = 1, q ≥ 17, r ≥ 19 contradicts t ≤ 6q − 3. -/
lemma k1_qlarge_impossible {q r : ℕ} {t : ℤ}
    (hq : 17 ≤ q) (hr : 19 ≤ r)
    (htle : t ≤ 6 * (q : ℤ) - 3)
    (heq : 6 * (q : ℤ) + 6 * r - 3 + t = (q : ℤ) * r) : False := by
  have hq' : (17 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (19 : ℤ) ≤ r := by exact_mod_cast hr
  nlinarith

/-- k = 2 and r ≥ 17 contradicts t ≤ 6q − 3 (using q ≥ 5). -/
lemma k2_rlarge_impossible {q r : ℕ} {t : ℤ}
    (hq : 5 ≤ q) (hr : 17 ≤ r)
    (htle : t ≤ 6 * (q : ℤ) - 3)
    (heq : 6 * (q : ℤ) + 6 * r - 3 + t = 2 * q * r) : False := by
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (17 : ℤ) ≤ r := by exact_mod_cast hr
  nlinarith



lemma evenCZ_7 (r : ℕ) : evenCZ 7 r = 39 * (r : ℤ) - 20 := by
  unfold evenCZ; ring

lemma evenCZ_11 (r : ℕ) : evenCZ 11 r = 63 * (r : ℤ) - 32 := by
  unfold evenCZ; ring

lemma evenCZ_13 (r : ℕ) : evenCZ 13 r = 75 * (r : ℤ) - 38 := by
  unfold evenCZ; ring

lemma evenCZ_5 (r : ℕ) : evenCZ 5 r = 27 * (r : ℤ) - 14 := by
  unfold evenCZ; ring


lemma not_prime_of_int_eq_nat (r n : ℕ) (hr : r.Prime) (hn : ¬ n.Prime)
    (heq : (r : ℤ) = (n : ℤ)) : False := by
  have : r = n := by exact_mod_cast heq
  exact hn (this ▸ hr)

lemma natAbs_pos_eq {d : ℤ} {n : ℕ} (hd : 0 < d) (h : d.natAbs = n) :
    d = n := by
  have : d = n ∨ d = - (n : ℤ) := Int.natAbs_eq_iff.mp h
  rcases this with h | h
  · exact h
  · have : (n : ℤ) ≥ 0 := by exact_mod_cast (Nat.zero_le n)
    nlinarith

/-- k = 1, q = 7 and t > 0: r − 39 is a positive divisor of 1501, never giving a prime r. -/
lemma k1_q7_impossible {r s : ℕ} {t : ℤ}
    (hr : r.Prime) (htpos : 0 < t)
    (ht : evenCZ 7 r = (s : ℤ) * t)
    (heq : 6 * (7 : ℤ) + 6 * r - 3 + t = (7 : ℤ) * r) : False := by
  have htval : t = (r : ℤ) - 39 := by linarith
  have hC := evenCZ_7 r
  have hprod : (s : ℤ) * t = 39 * r - 20 := by rw [← ht, hC]
  have h1501 : (s - 39 : ℤ) * t = 1501 := by
    have hid : (39 * (r : ℤ) - 20) = 39 * (r - 39) + 1501 := by ring
    rw [htval] at hprod
    linarith
  have hdiv : t ∣ (1501 : ℤ) := ⟨s - 39, by linarith⟩
  have habs := abs_dvd_mem_divisors (by decide : 1501 ≠ 0) hdiv
  rw [divisors_1501] at habs
  simp only [Finset.mem_insert, Finset.mem_singleton] at habs
  have hreq : (r : ℤ) = t + 39 := by linarith [htval]
  rcases habs with h | h | h | h
  · have ht1 : t = 1 := natAbs_pos_eq htpos h
    rw [ht1] at hreq
    norm_num at hreq
    exact not_prime_of_int_eq_nat r 40 hr (by norm_num) hreq
  · have ht19 : t = 19 := natAbs_pos_eq htpos h
    rw [ht19] at hreq
    norm_num at hreq
    exact not_prime_of_int_eq_nat r 58 hr (by norm_num) hreq
  · have ht79 : t = 79 := natAbs_pos_eq htpos h
    rw [ht79] at hreq
    norm_num at hreq
    exact not_prime_of_int_eq_nat r 118 hr (by norm_num) hreq
  · have ht1501 : t = 1501 := natAbs_pos_eq htpos h
    rw [ht1501] at hreq
    norm_num at hreq
    exact not_prime_of_int_eq_nat r 1540 hr (by norm_num) hreq

/-- k = 1, q = 11: t = 5r − 63 divides 3809 and never yields integer r. -/
lemma k1_q11_impossible {r s : ℕ} {t : ℤ}
    (htpos : 0 < t)
    (ht : evenCZ 11 r = (s : ℤ) * t)
    (heq : 6 * (11 : ℤ) + 6 * r - 3 + t = (11 : ℤ) * r) : False := by
  have htval : t = 5 * (r : ℤ) - 63 := by linarith
  have hC := evenCZ_11 r
  have hprod : (s : ℤ) * t = 63 * r - 32 := by rw [← ht, hC]
  -- 5*(63r-32) - 63*(5r-63) = 3809
  have h3809 : (5 * s - 63 : ℤ) * t = 3809 := by
    have hid : (5 : ℤ) * (63 * r - 32) - 63 * (5 * r - 63) = 3809 := by ring
    rw [← htval] at hid
    linarith
  have hdiv : t ∣ (3809 : ℤ) := ⟨5 * s - 63, by linarith⟩
  have habs := abs_dvd_mem_divisors (by norm_num : 3809 ≠ 0) hdiv
  rw [divisors_3809] at habs
  simp only [Finset.mem_insert, Finset.mem_singleton] at habs
  -- r = (t + 63) / 5 must be an integer, so 5 ∣ t+63
  have h5 : (5 : ℤ) ∣ t + 63 := ⟨r, by linarith [htval]⟩
  rcases habs with h | h | h | h
  · have ht1 : t = 1 := natAbs_pos_eq htpos h
    rw [ht1] at h5
    exact (by norm_num : ¬ (5 : ℤ) ∣ 64) h5
  · have ht13 : t = 13 := natAbs_pos_eq htpos h
    rw [ht13] at h5
    exact (by norm_num : ¬ (5 : ℤ) ∣ 76) h5
  · have ht293 : t = 293 := natAbs_pos_eq htpos h
    rw [ht293] at h5
    exact (by norm_num : ¬ (5 : ℤ) ∣ 356) h5
  · have ht3809 : t = 3809 := natAbs_pos_eq htpos h
    rw [ht3809] at h5
    exact (by norm_num : ¬ (5 : ℤ) ∣ 3872) h5

/-- k = 1, q = 13: t = 7r − 75 divides 5359; no prime r. -/
lemma k1_q13_impossible {r s : ℕ} {t : ℤ}
    (hr : r.Prime) (htpos : 0 < t)
    (ht : evenCZ 13 r = (s : ℤ) * t)
    (heq : 6 * (13 : ℤ) + 6 * r - 3 + t = (13 : ℤ) * r) : False := by
  have htval : t = 7 * (r : ℤ) - 75 := by linarith
  have hC := evenCZ_13 r
  have hprod : (s : ℤ) * t = 75 * r - 38 := by rw [← ht, hC]
  have h5359 : (7 * s - 75 : ℤ) * t = 5359 := by
    have hid : (7 : ℤ) * (75 * r - 38) - 75 * (7 * r - 75) = 5359 := by ring
    rw [← htval] at hid
    linarith
  have hdiv : t ∣ (5359 : ℤ) := ⟨7 * s - 75, by linarith⟩
  have habs := abs_dvd_mem_divisors (by norm_num : 5359 ≠ 0) hdiv
  rw [divisors_5359] at habs
  simp only [Finset.mem_insert, Finset.mem_singleton] at habs
  have h7 : (7 : ℤ) ∣ t + 75 := ⟨r, by linarith [htval]⟩
  rcases habs with h | h | h | h
  · have ht1 : t = 1 := natAbs_pos_eq htpos h
    rw [ht1] at h7
    exact (by norm_num : ¬ (7 : ℤ) ∣ 76) h7
  · have ht23 : t = 23 := natAbs_pos_eq htpos h
    have hr7 : 7 * (r : ℤ) = t + 75 := by linarith [htval]
    rw [ht23] at hr7
    norm_num at hr7
    -- 7r = 98, r = 14
    have : (r : ℤ) = 14 := by
      have : 7 * (r : ℤ) = 7 * 14 := by norm_num [hr7]
      exact mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0) this
    exact not_prime_of_int_eq_nat r 14 hr (by norm_num) this
  · have ht233 : t = 233 := natAbs_pos_eq htpos h
    have hr7 : 7 * (r : ℤ) = t + 75 := by linarith [htval]
    rw [ht233] at hr7
    norm_num at hr7
    -- 7r = 308, r = 44
    have : (r : ℤ) = 44 := by
      have : 7 * (r : ℤ) = 7 * 44 := by norm_num [hr7]
      exact mul_left_cancel₀ (by norm_num : (7 : ℤ) ≠ 0) this
    exact not_prime_of_int_eq_nat r 44 hr (by norm_num) this
  · have ht5359 : t = 5359 := natAbs_pos_eq htpos h
    have hr7 : 7 * (r : ℤ) = t + 75 := by linarith [htval]
    rw [ht5359] at hr7
    -- 7r = 5434, 5434 = 7*776 + 2, not divisible
    rw [ht5359] at h7
    exact (by norm_num : ¬ (7 : ℤ) ∣ 5434) h7

lemma k2_q5_r7_impossible {s : ℕ} {t : ℤ}
    (hs : s.Prime)
    (ht : evenCZ 5 7 = (s : ℤ) * t)
    (heq : 6 * (5 : ℤ) + 6 * 7 - 3 + t = 2 * 5 * 7) : False := by
  have htval : t = 1 := by linarith
  have hC : evenCZ 5 7 = 175 := by unfold evenCZ; norm_num
  have : (s : ℤ) * t = 175 := by rw [← ht, hC]
  rw [htval] at this
  have : (s : ℤ) = 175 := by linarith
  exact not_prime_of_int_eq_nat s 175 hs (by norm_num) this

lemma k2_q5_r11_impossible {s : ℕ} {t : ℤ}
    (ht : evenCZ 5 11 = (s : ℤ) * t)
    (heq : 6 * (5 : ℤ) + 6 * 11 - 3 + t = 2 * 5 * 11) : False := by
  have htval : t = 17 := by linarith
  have hC : evenCZ 5 11 = 283 := by unfold evenCZ; norm_num
  have : (s : ℤ) * t = 283 := by rw [← ht, hC]
  rw [htval] at this
  -- 17 * s = 283, 283 / 17 = 16 rem 11
  have : (17 : ℤ) ∣ 283 := ⟨s, by linarith⟩
  exact (by norm_num : ¬ (17 : ℤ) ∣ 283) this

lemma k2_q5_r13_impossible {s : ℕ} {t : ℤ}
    (ht : evenCZ 5 13 = (s : ℤ) * t)
    (heq : 6 * (5 : ℤ) + 6 * 13 - 3 + t = 2 * 5 * 13) : False := by
  have htval : t = 25 := by linarith
  have hC : evenCZ 5 13 = 337 := by unfold evenCZ; norm_num
  have : (s : ℤ) * t = 337 := by rw [← ht, hC]
  rw [htval] at this
  have : (25 : ℤ) ∣ 337 := ⟨s, by linarith⟩
  exact (by norm_num : ¬ (25 : ℤ) ∣ 337) this

/-- k = 2 forces q = 5 and r ∈ {7, 11, 13}; none work. -/
lemma k2_impossible {q r s : ℕ} {t : ℤ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hq5 : 5 ≤ q) (hr7 : 7 ≤ r) (hqr : q ≤ r) (hne : q ≠ r)
    (htpos : 0 < t) (htle : t ≤ 6 * (q : ℤ) - 3)
    (ht : evenCZ q r = (s : ℤ) * t)
    (heq : 6 * (q : ℤ) + 6 * r - 3 + t = 2 * q * r) : False := by
  have hr17 : r < 17 := by
    by_contra h
    exact k2_rlarge_impossible hq5 (by omega : 17 ≤ r) htle heq
  have hr_cases := prime_eq_seven_eleven_thirteen hr hr7 hr17
  have hq17 : q < 17 := lt_of_le_of_lt hqr hr17
  have hq_cases := prime_eq_five_seven_eleven_thirteen hq hq5 hq17
  -- q < r since q ≤ r and q ≠ r, and r ∈ {7,11,13}, so q = 5 (the only option < 7)
  have hq5eq : q = 5 := by
    rcases hq_cases with rfl | rfl | rfl | rfl
    · rfl
    · rcases hr_cases with rfl | rfl | rfl
      · exact (hne rfl).elim
      · omega -- 7 ≤ 11, but wait q=7, r=11 is possible for k=2?
      · omega
    · rcases hr_cases with rfl | rfl | rfl <;> omega
    · rcases hr_cases with rfl | rfl | rfl <;> omega
  subst hq5eq
  -- For q=5, k=2: q(r-6) ≤ 3(r-1) => 5(r-6) ≤ 3(r-1) => 5r-30 ≤ 3r-3 => 2r ≤ 27 => r ≤ 13.5
  -- already r ∈ {7,11,13}
  rcases hr_cases with rfl | rfl | rfl
  · exact k2_q5_r7_impossible hs ht heq
  · exact k2_q5_r11_impossible ht heq
  · exact k2_q5_r13_impossible ht heq

/-- k = 1 is impossible for primes 5 ≤ q ≤ r, q ≠ r. -/
lemma k1_impossible {q r s : ℕ} {t : ℤ}
    (hq : q.Prime) (hr : r.Prime) (_hs : s.Prime)
    (hq5 : 5 ≤ q) (_hr7 : 7 ≤ r) (hqr : q ≤ r) (hne : q ≠ r)
    (htpos : 0 < t) (htle : t ≤ 6 * (q : ℤ) - 3)
    (ht : evenCZ q r = (s : ℤ) * t)
    (heq : 6 * (q : ℤ) + 6 * r - 3 + t = (q : ℤ) * r) : False := by
  rcases lt_or_ge q 17 with hqlt | hqge
  · have hq_cases := prime_eq_five_seven_eleven_thirteen hq hq5 hqlt
    rcases hq_cases with rfl | rfl | rfl | rfl
    · exact (lt_irrefl (0 : ℤ) (lt_trans htpos (k1_q5_t_neg (le_trans hq5 hqr) heq))).elim
    · exact k1_q7_impossible hr htpos ht heq
    · exact k1_q11_impossible htpos ht heq
    · exact k1_q13_impossible hr htpos ht heq
  · have hr19 : 19 ≤ r := by
      have : q < r := lt_of_le_of_ne hqr hne
      have : 17 < r := lt_of_le_of_lt hqge this
      exact nineteen_le_of_prime_gt_seventeen hr this
    exact k1_qlarge_impossible hqge hr19 htle heq

lemma not_dvd_pillai_four_primes_even {q r s : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hq5 : 5 ≤ q) (hqr : q ≤ r) (hrs : r ≤ s)
    (hne_qr : q ≠ r) (_hne_qs : q ≠ s) (_hne_rs : r ≠ s) :
    ¬ (2 * q * r * s) ∣ 3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1 := by
  intro hdvd
  have hr7 : 7 ≤ r := by
    have hlt : q < r := lt_of_le_of_ne hqr hne_qr
    have : 5 < r := lt_of_le_of_lt hq5 hlt
    have hne6 : r ≠ 6 := fun eq ↦ (by norm_num : ¬ Nat.Prime 6) (eq ▸ hr)
    omega
  have hr5 : 5 ≤ r := le_trans (by norm_num : 5 ≤ 7) hr7
  have hs5 : 5 ≤ s := le_trans hr5 hrs
  have hΔ := two_qrs_dvd_imp_delta hq hr hs hq5 hr5 hs5 hdvd
  have hC := s_dvd_evenCZ_of_qrs_dvd hΔ
  obtain ⟨t, ht, hΔt⟩ := exists_t_of_s_dvd_C hC
  have hspos : 0 < s := hs.pos
  have hsposZ : (0 : ℤ) < s := by exact_mod_cast hspos
  have hqr_dvd := qrs_dvd_imp_qr_dvd_coeff hΔt hΔ hsposZ
  obtain ⟨k, hk⟩ := exists_k_of_qr_dvd hqr_dvd
  have hCpos : 0 < evenCZ q r := evenCZ_pos hq5 hr5
  have htpos : 0 < t := t_pos_of_C_pos_s_pos hCpos hspos ht
  have htle : t ≤ 6 * (q : ℤ) - 3 := t_le_of_s_ge_r hq5 hr5 hrs ht
  have hk12 := k_eq_one_or_two hq5 hr7 htpos htle hk
  rcases hk12 with rfl | rfl
  · refine k1_impossible hq hr hs hq5 hr7 hqr hne_qr htpos htle ht ?_
    simpa using hk
  · exact k2_impossible hq hr hs hq5 hr7 hqr hne_qr htpos htle ht hk

lemma not_dvd_pillai_four_primes_even_unsorted {q r s : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hq5 : 5 ≤ q) (hr5 : 5 ≤ r) (hs5 : 5 ≤ s)
    (hne_qr : q ≠ r) (hne_qs : q ≠ s) (hne_rs : r ≠ s) :
    ¬ (2 * q * r * s) ∣ 3 * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1 := by
  wlog hord : q ≤ r ∧ r ≤ s generalizing q r s
  · intro hdvd
    rcases le_total q r with hqr | hrq
    · rcases le_total r s with hrs | hsr
      · exact this hq hr hs hq5 hr5 hs5 hne_qr hne_qs hne_rs ⟨hqr, hrs⟩ hdvd
      · rcases le_total q s with hqs | hsq
        · apply this hq hs hr hq5 hs5 hr5 hne_qs hne_qr hne_rs.symm ⟨hqs, hsr⟩
          convert hdvd using 1 <;> ring
        · apply this hs hq hr hs5 hq5 hr5 hne_qs.symm hne_rs.symm hne_qr ⟨hsq, hqr⟩
          convert hdvd using 1 <;> ring
    · rcases le_total r s with hrs | hsr
      · rcases le_total q s with hqs | hsq
        · apply this hr hq hs hr5 hq5 hs5 hne_qr.symm hne_rs hne_qs ⟨hrq, hqs⟩
          convert hdvd using 1 <;> ring
        · apply this hr hs hq hr5 hs5 hq5 hne_rs hne_qr.symm hne_qs.symm ⟨hrs, hsq⟩
          convert hdvd using 1 <;> ring
      · rcases le_total q s with hqs | hsq
        · have : q = r := le_antisymm (hqs.trans hsr) hrq
          exact (hne_qr this).elim
        · apply this hs hr hq hs5 hr5 hq5 hne_rs.symm hne_qs.symm hne_qr.symm ⟨hsr, hrq⟩
          convert hdvd using 1 <;> ring
  exact not_dvd_pillai_four_primes_even hq hr hs hq5 hord.1 hord.2 hne_qr hne_qs hne_rs
