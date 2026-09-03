import Submission.Development

/-!
# Arithmetic obstruction to nonrectangular positive geometric truncations

These lemmas concern termwise denominator clearing, not reduced denominators
of sums. They do not settle the conjecture in `Submission/Spec.lean`.
-/

namespace GeometricClearingBarrier

lemma prime_dvd_pred_factorial_gt_succ {k p : ℕ} (hk : 2 ≤ k)
    (hp : p.Prime) (hd : p ∣ k.factorial - 1) : k + 1 < p := by
  have hf := Nat.factorial_pos k
  have hkp : k < p := by
    by_contra h
    have hfd : p ∣ k.factorial := Nat.dvd_factorial hp.pos (by omega)
    have h1 : p ∣ 1 := by
      have hh := Nat.dvd_sub hfd hd
      simpa only [Nat.sub_sub_self hf] using hh
    exact hp.not_dvd_one h1
  by_contra h
  have he : p = k + 1 := by omega
  subst p
  letI : Fact (k + 1).Prime := ⟨hp⟩
  have hw := ZMod.wilsons_lemma (k + 1)
  simp only [Nat.add_sub_cancel] at hw
  have hd' : (k.factorial : ZMod (k + 1)) - 1 = 0 := by
    have hh := (ZMod.natCast_eq_zero_iff (k.factorial - 1) (k + 1)).mpr hd
    simpa only [Nat.cast_sub hf, Nat.cast_one] using hh
  have htwo : (2 : ZMod (k + 1)) = 0 := by
    rw [hw] at hd'
    linear_combination -hd'
  have hdiv : k + 1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (k + 1)).mp htwo
  have := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
  omega

lemma pred_factorial_coprime_succ_factorial {k : ℕ} (hk : 2 ≤ k) :
    (k.factorial - 1).Coprime (k + 1).factorial := by
  apply Nat.coprime_of_dvd
  intro p hp hd hdf
  have := prime_dvd_pred_factorial_gt_succ hk hp hd
  have := hp.dvd_factorial.mp hdf
  omega

lemma even_dvd_pred_factorial {m : ℕ} (hm : 6 ≤ m) (he : Even m) :
    m ∣ (m - 1).factorial := by
  obtain ⟨a, ha⟩ := he
  have ham : m = 2 * a := by omega
  have ha3 : 3 ≤ a := by omega
  have h1 : 2 * a ∣ (2 : ℕ).factorial * a.factorial := by
    simpa using Nat.mul_dvd_mul (dvd_refl 2)
      (Nat.dvd_factorial (by omega : 0 < a) le_rfl)
  have h2 := Nat.factorial_mul_factorial_dvd_factorial_add 2 a
  rw [ham]
  exact h1.trans (h2.trans (Nat.factorial_dvd_factorial (by omega)))

lemma pred_factorial_ne_prime_succ_two_pow {k e : ℕ} (hk : 4 ≤ k)
    (hp : (k + 2).Prime) : k.factorial - 1 ≠ (k + 2) ^ e := by
  intro heq
  have ho := hp.odd_of_ne_two (by omega)
  obtain ⟨a, ha⟩ := ho
  have heven : Even (k + 1) := ⟨a, by omega⟩
  have hk5 : 5 ≤ k := by omega
  have hd : k + 1 ∣ k.factorial := by
    simpa only [Nat.add_sub_cancel] using
      even_dvd_pred_factorial (show 6 ≤ k + 1 by omega) heven
  have hmod : (k + 2) % (k + 1) = 1 := by
    have hh : k + 2 = (k + 1) + 1 := by omega
    rw [hh, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (by omega : 1 < k + 1)]
  have hf := Nat.factorial_pos k
  have hf' : k.factorial = (k + 2) ^ e + 1 := by omega
  have hh := Nat.mod_eq_zero_of_dvd hd
  rw [hf', Nat.add_mod, Nat.pow_mod, hmod] at hh
  simp only [one_pow] at hh
  have hsmall : 1 % (k + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hsmall, show 1 + 1 = 2 by rfl, Nat.mod_eq_of_lt (by omega : 2 < k + 1)] at hh
  omega

/-- At least one prime factor exceeds the two indices immediately after k. -/
theorem exists_prime_dvd_pred_factorial_gt_add_two {k : ℕ} (hk : 4 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ p ∣ k.factorial - 1 ∧ k + 2 < p := by
  have hf : 24 ≤ k.factorial := by
    simpa using Nat.factorial_le hk
  by_cases hp : (k + 2).Prime
  · obtain ⟨e, u, hu, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd
      (show k.factorial - 1 ≠ 0 by omega) (k + 2) (by omega)
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, mul_one] at heq
      exact pred_factorial_ne_prime_succ_two_pow hk hp heq
    obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd hu1
    have hd : p ∣ k.factorial - 1 := by
      rw [heq]
      exact dvd_mul_of_dvd_right hpd _
    have hgt := prime_dvd_pred_factorial_gt_succ (by omega) hpp hd
    have hne : p ≠ k + 2 := by
      rintro rfl
      exact hu hpd
    exact ⟨p, hpp, hd, by omega⟩
  · obtain ⟨p, hpp, hd⟩ := Nat.exists_prime_and_dvd
      (show k.factorial - 1 ≠ 1 by omega)
    have hgt := prime_dvd_pred_factorial_gt_succ (by omega) hpp hd
    have hne : p ≠ k + 2 := by rintro rfl; exact hp hpp
    exact ⟨p, hpp, hd, by omega⟩

open Erdos68Development

/-- Clearing the last two exact rows and a geometric prefix of the next row
already requires a multiplier exceeding the reciprocal of that row's error. -/
theorem clearing_two_rows_bound {n r M : ℕ} (hn : 2 ≤ n) (hM : 0 < M)
    (h0 : denom n ∣ M) (h1 : denom (n + 1) ∣ M)
    (hr : (n + 4).factorial ^ r ∣ M) :
    (n + 4).factorial ^ r * denom (n + 2) < M := by
  obtain ⟨p, hp, hpd, hgt⟩ :=
    exists_prime_dvd_pred_factorial_gt_add_two (show 4 ≤ n + 2 by omega)
  change p ∣ denom n at hpd
  have hcp : p.Coprime (denom (n + 1)) :=
    (denom_consecutive_coprime n).of_dvd_left hpd
  have hdf : (denom (n + 1)).Coprime (n + 4).factorial := by
    simpa only [denom, Nat.add_assoc, show 1 + 2 = 3 by rfl,
      show 3 + 1 = 4 by rfl] using
      pred_factorial_coprime_succ_factorial (show 2 ≤ n + 3 by omega)
  have hpf : p.Coprime (n + 4).factorial :=
    hp.coprime_factorial_of_lt (by omega)
  have hdvd : denom (n + 1) * p * (n + 4).factorial ^ r ∣ M :=
    ((hdf.mul_left hpf).pow_right r).mul_dvd_of_dvd_of_dvd
      (hcp.symm.mul_dvd_of_dvd_of_dvd h1 (hpd.trans h0)) hr
  have hnum : denom (n + 2) < denom (n + 1) * p := by
    have he := denom_nat_succ (n + 1)
    have hl := denom_ge_add_five (show 2 ≤ n + 1 by omega)
    have hm := Nat.mul_le_mul_left (denom (n + 1))
      (show n + 5 ≤ p by omega)
    simp only [Nat.add_assoc] at he hl
    nlinarith
  have hpwr : 0 < (n + 4).factorial ^ r := by positivity
  calc
    (n + 4).factorial ^ r * denom (n + 2) <
        (n + 4).factorial ^ r * (denom (n + 1) * p) :=
      Nat.mul_lt_mul_of_pos_left hnum hpwr
    _ = denom (n + 1) * p * (n + 4).factorial ^ r := by ring
    _ ≤ M := Nat.le_of_dvd hM hdvd

noncomputable def rowPrefix (k r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, powerTerm j k

lemma rowPrefix_error (k r : ℕ) :
    term k - rowPrefix k r =
      1 / (((k + 2).factorial : ℝ) ^ r * ((k + 2).factorial - 1)) := by
  have ha : (0 : ℝ) < (k + 2).factorial := by positivity
  have hb : (0 : ℝ) < (k + 2).factorial - 1 := denom_pos k
  induction r with
  | zero => simp [rowPrefix, term]
  | succ r ih =>
    have hp : ((k + 2).factorial : ℝ) ^ r ≠ 0 := pow_ne_zero _ ha.ne'
    rw [rowPrefix, Finset.sum_range_succ]
    change term k - (rowPrefix k r + powerTerm r k) = _
    rw [sub_add_eq_sub_sub, ih]
    unfold powerTerm
    rw [pow_succ]
    field_simp
    ring

lemma rowPrefix_le (k r : ℕ) : rowPrefix k r ≤ term k := by
  have h := rowPrefix_error k r
  have hp : 0 < (k + 2).factorial - (1 : ℝ) := denom_pos k
  have hr : 0 ≤ 1 / (((k + 2).factorial : ℝ) ^ r * ((k + 2).factorial - 1)) :=
    le_of_lt (by positivity)
  linarith

/-- Exact initial rows followed by independently truncated geometric rows. -/
noncomputable def mixedApprox (n L : ℕ) (orders : ℕ → ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 2), term k) +
    ∑ k ∈ Finset.range (L + 1), rowPrefix (n + 2 + k) (orders k)

lemma mixedApprox_error_lower (n L : ℕ) (orders : ℕ → ℕ) :
    1 / (((n + 4).factorial : ℝ) ^ orders 0 * ((n + 4).factorial - 1)) <
      (∑' k : ℕ, term k) - mixedApprox n L orders := by
  have hpartial := (partial_sum_error (n + 2 + (L + 1))).1
  rw [Finset.sum_range_add] at hpartial
  have hfinite : term (n + 2) - rowPrefix (n + 2) (orders 0) ≤
      ∑ k ∈ Finset.range (L + 1),
        (term (n + 2 + k) - rowPrefix (n + 2 + k) (orders k)) := by
    simpa only [Nat.add_zero] using
      (Finset.single_le_sum
        (fun k (_ : k ∈ Finset.range (L + 1)) =>
          sub_nonneg.mpr (rowPrefix_le (n + 2 + k) (orders k)))
        (show 0 ∈ Finset.range (L + 1) by simp))
  rw [rowPrefix_error, Finset.sum_sub_distrib] at hfinite
  rw [show n + 2 + 2 = n + 4 by omega] at hfinite
  unfold mixedApprox
  linarith

/-- No choice of the separate geometric truncation lengths repairs termwise
clearing once at least the first four rows have been summed exactly.
This theorem does not apply to an arbitrary reduced denominator. -/
theorem mixedApprox_termwise_scaled_error_gt_one {n L M : ℕ}
    (orders : ℕ → ℕ) (hn : 2 ≤ n) (hM : 0 < M)
    (h0 : denom n ∣ M) (h1 : denom (n + 1) ∣ M)
    (hr : (n + 4).factorial ^ orders 0 ∣ M) :
    1 < (M : ℝ) * ((∑' k : ℕ, term k) - mixedApprox n L orders) := by
  have hbound := clearing_two_rows_bound hn hM h0 h1 hr
  have hbound' : ((n + 4).factorial : ℝ) ^ orders 0 *
      ((n + 4).factorial - 1) < M := by
    have hd : (denom (n + 2) : ℝ) = (n + 4).factorial - 1 := by
      simp only [denom, Nat.add_assoc, show 2 + 2 = 4 by rfl,
        Nat.cast_sub (Nat.factorial_pos _), Nat.cast_one]
    rw [← hd]
    exact_mod_cast hbound
  have hd : 0 < ((n + 4).factorial : ℝ) ^ orders 0 *
      ((n + 4).factorial - 1) := by
    have hp := denom_pos (n + 2)
    simp only [Nat.add_assoc, show 2 + 2 = 4 by rfl] at hp
    positivity
  have hfirst : 1 < (M : ℝ) *
      (1 / (((n + 4).factorial : ℝ) ^ orders 0 * ((n + 4).factorial - 1))) := by
    rw [mul_one_div]
    exact (one_lt_div hd).mpr hbound'
  exact hfirst.trans (mul_lt_mul_of_pos_left (mixedApprox_error_lower n L orders)
    (by exact_mod_cast hM))

#print axioms exists_prime_dvd_pred_factorial_gt_add_two
#print axioms clearing_two_rows_bound
#print axioms mixedApprox_termwise_scaled_error_gt_one

end GeometricClearingBarrier
