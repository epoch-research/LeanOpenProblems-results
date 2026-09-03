import Submission.RowGcdCriterion

/-!
# Exact eventual GCD identity under rationality

If the original sum is rational, its sublinear positive row remainder
is eventually exactly `gcd (rowFloor n) n!`. This is a necessary condition,
not a proof of irrationality.
-/

namespace RowGcdEquality

open Erdos68Development RowGcdCriterion Filter
open scoped Topology

lemma dvd_factorial_quotient (b d n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (hbn : b ≤ n) (hbd : b * d ≤ n) : d ∣ n.factorial / b := by
  apply (Nat.dvd_div_iff_mul_dvd (Nat.dvd_factorial hb hbn)).mpr
  exact Nat.dvd_factorial (Nat.mul_pos hb hd) hbd

lemma integer_rowTail (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (n : ℕ) (hn : q.den ≤ n) :
    ∃ t : ℕ, 0 < t ∧ (t : ℝ) = rowTail n ∧
      (t : ℤ) = q.num * (n.factorial / q.den : ℕ) - rowFloor n := by
  let c : ℕ := n.factorial / q.den
  let z : ℤ := q.num * (c : ℤ) - rowFloor n
  have hz : (z : ℝ) = rowTail n := by
    have hd : q.den ∣ n.factorial := Nat.dvd_factorial q.pos hn
    have hb : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    change ((q.num * (c : ℤ) - rowFloor n : ℤ) : ℝ) = rowTail n
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    change (q.num : ℝ) * ((n.factorial / q.den : ℕ) : ℝ) - (rowFloor n : ℝ) =
      (n.factorial : ℝ) * (∑' k : ℕ, term k) - rowFloor n
    rw [Nat.cast_div hd hb, hq, Rat.cast_def]
    ring
  have hzp : 0 < z := by
    have h : (0 : ℝ) < z := by rw [hz]; exact rowTail_pos n
    exact_mod_cast h
  refine ⟨z.toNat, by omega, ?_, Int.toNat_of_nonneg hzp.le⟩
  have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzp.le
  have hc : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hcast
  exact hc.trans hz

/-- Two smallness bounds turn the earlier one-sided GCD estimate into equality. -/
lemma rowGcd_eq_tail_of_bounds (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ) (hn : q.den ≤ n)
    (htb : (q.den : ℝ) * rowTail n ≤ n)
    (hgb : q.den * rowGcd n ≤ n) : (rowGcd n : ℝ) = rowTail n := by
  obtain ⟨t, htpos, ht, htz⟩ := integer_rowTail q hq n hn
  have hbt : q.den * t ≤ n := by
    have h : (q.den : ℝ) * (t : ℝ) ≤ n := by rwa [ht]
    exact_mod_cast h
  have htd := dvd_factorial_quotient q.den t n q.pos htpos hn hbt
  have hgd := dvd_factorial_quotient q.den (rowGcd n) n q.pos (rowGcd_pos n) hn hgb
  have htdiv : (t : ℤ) ∣ rowFloor n := by
    have hq : (t : ℤ) ∣ q.num * (n.factorial / q.den : ℕ) :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr htd) q.num
    have he : rowFloor n = q.num * (n.factorial / q.den : ℕ) - t := by omega
    rw [he]
    exact dvd_sub hq (dvd_refl _)
  have htN : t ∣ n.factorial := by
    have htn : t ≤ n := by
      have hb1 : 1 ≤ q.den := q.pos
      nlinarith
    exact Nat.dvd_factorial htpos htn
  have htg : t ∣ rowGcd n := Int.dvd_gcd htdiv (Int.natCast_dvd_natCast.mpr htN)
  have hgt : rowGcd n ∣ t := by
    apply Int.natCast_dvd_natCast.mp
    rw [htz]
    exact dvd_sub
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hgd) q.num)
      (Int.gcd_dvd_left (rowFloor n) (n.factorial : ℤ))
  have hge : rowGcd n = t := Nat.dvd_antisymm hgt htg
  rwa [hge]

/-- If the sum is rational, the integer GCD is eventually the exact row tail. -/
theorem rowGcd_eventually_eq_tail_of_rational (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) :
    ∀ᶠ n : ℕ in atTop, (rowGcd n : ℝ) = rowTail n := by
  have ht : Tendsto (fun n : ℕ => (q.den : ℝ) * (rowTail n / n)) atTop (𝓝 0) := by
    simpa using RowRemainderBounds.rowTail_div_self_tendsto.const_mul (q.den : ℝ)
  have hg : Tendsto (fun n : ℕ => (q.den : ℝ) * ((rowGcd n : ℝ) / n)) atTop (𝓝 0) := by
    simpa using (rowGcd_div_self_tendsto_zero_of_rational q hq).const_mul (q.den : ℝ)
  filter_upwards [eventually_ge_atTop (max q.den 1),
    ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    hg.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn htn hgn
  have hnq : q.den ≤ n := (le_max_left _ _).trans hn
  have hnp : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by have := (le_max_right q.den 1).trans hn; omega)
  have htb : (q.den : ℝ) * rowTail n < n :=
    (div_lt_one hnp).mp (by simpa only [mul_div_assoc] using htn)
  have hgb : (q.den : ℝ) * rowGcd n < n :=
    (div_lt_one hnp).mp (by simpa only [mul_div_assoc] using hgn)
  exact rowGcd_eq_tail_of_bounds q hq n hnq htb.le (by exact_mod_cast hgb.le)

def gcdCorrected (n : ℕ) : ℚ :=
  ((rowFloor n : ℚ) + rowGcd n) / n.factorial

/-- This new rational approximation must stabilize if the conjectured sum
is rational. No exclusion of that stabilization is proved here. -/
theorem gcdCorrected_eventually_eq_of_rational (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) :
    ∀ᶠ n : ℕ in atTop, gcdCorrected n = q := by
  filter_upwards [rowGcd_eventually_eq_tail_of_rational q hq] with n hn
  have he : (gcdCorrected n : ℝ) = (q : ℝ) := by
    simp only [gcdCorrected, Rat.cast_div, Rat.cast_add, Rat.cast_intCast, Rat.cast_natCast]
    rw [hn, rowTail, hq]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  exact_mod_cast he

lemma rowFloor_normalized_lt_sum (n : ℕ) :
    (rowFloor n : ℝ) / n.factorial < ∑' k : ℕ, term k := by
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mpr
  have ht := rowTail_pos n
  unfold rowTail at ht
  nlinarith

lemma normalized_gcd_le_form (a b : ℤ) (n : ℕ)
    (hne : (b : ℝ) * ((rowFloor n : ℝ) / n.factorial) - a ≠ 0) :
    (rowGcd n : ℝ) / n.factorial ≤
      |(b : ℝ) * ((rowFloor n : ℝ) / n.factorial) - a| := by
  let D : ℤ := b * rowFloor n - a * (n.factorial : ℤ)
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hD : (D : ℝ) = (n.factorial : ℝ) *
      ((b : ℝ) * ((rowFloor n : ℝ) / n.factorial) - a) := by
    dsimp [D]
    push_cast
    field_simp
  have hDn : D ≠ 0 := by
    intro h
    have hz : (D : ℝ) = 0 := by rw [h]; norm_num
    rw [hD] at hz
    exact hne ((mul_eq_zero.mp hz).resolve_left hf.ne')
  have hd : (rowGcd n : ℤ) ∣ D :=
    dvd_sub (dvd_mul_of_dvd_right (Int.gcd_dvd_left (rowFloor n) (n.factorial : ℤ)) b)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right (rowFloor n) (n.factorial : ℤ)) a)
  have hl := Int.le_of_dvd (abs_pos.mpr hDn) ((dvd_abs _ _).mpr hd)
  have hlr : (rowGcd n : ℝ) ≤ |(D : ℝ)| := by exact_mod_cast hl
  rw [hD, abs_mul, abs_of_pos hf] at hlr
  exact (div_le_iff₀ hf).mpr (by nlinarith)

/-- The GCD divided by the factorial tends to zero unconditionally.
The much stronger normalization by n still has only a conditional result. -/
theorem rowGcd_div_factorial_tendsto_zero :
    Tendsto (fun n : ℕ => (rowGcd n : ℝ) / n.factorial) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨a, b, hb, _, hab⟩ :=
    Real.exists_int_int_abs_mul_sub_le (∑' k : ℕ, term k) (Nat.succ_pos m)
  have hsmall : |(b : ℝ) * (∑' k : ℕ, term k) - a| < ε := by
    apply lt_of_le_of_lt hab
    apply lt_of_le_of_lt _ hm
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < m + 1)
    push_cast
    linarith
  have hlim : Tendsto (fun n : ℕ =>
      (b : ℝ) * ((rowFloor n : ℝ) / n.factorial) - a) atTop
      (𝓝 ((b : ℝ) * (∑' k : ℕ, term k) - a)) :=
    (rowFloor_tendsto.const_mul (b : ℝ)).sub_const (a : ℝ)
  have hne : ∀ᶠ n : ℕ in atTop,
      (b : ℝ) * ((rowFloor n : ℝ) / n.factorial) - a ≠ 0 := by
    by_cases hz : (b : ℝ) * (∑' k : ℕ, term k) - a = 0
    · apply Eventually.of_forall
      intro n
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have hlt := mul_lt_mul_of_pos_left (rowFloor_normalized_lt_sum n) hbR
      have hneg : (b : ℝ) * ((rowFloor n : ℝ) / n.factorial) - a < 0 := by linarith
      exact hneg.ne
    · exact hlim.eventually_ne hz
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlim.abs.eventually_lt_const hsmall).and hne)
  refine ⟨N, fun n hn => ?_⟩
  have h0 : (0 : ℝ) ≤ (rowGcd n : ℝ) / n.factorial := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact (normalized_gcd_le_form a b n (hN n hn).2).trans_lt (hN n hn).1

theorem gcdCorrected_tendsto :
    Tendsto (fun n : ℕ => (gcdCorrected n : ℝ)) atTop (𝓝 (∑' k : ℕ, term k)) := by
  have h := rowFloor_tendsto.add rowGcd_div_factorial_tendsto_zero
  simpa [gcdCorrected, add_div] using h

/-- Another exact finite-arithmetic reformulation. The non-stabilization
condition on the right is not proved in this file. -/
theorem irrational_iff_gcdCorrected_not_eventually_constant :
    Irrational (∑' k : ℕ, term k) ↔
      ¬ ∃ q : ℚ, ∀ᶠ n : ℕ in atTop, gcdCorrected n = q := by
  constructor
  · intro hi ⟨q, hq⟩
    have hc : Tendsto (fun n : ℕ => (gcdCorrected n : ℝ)) atTop (𝓝 (q : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hq] with n hn
      simp only [hn]
    exact hi.ne_rat q (tendsto_nhds_unique gcdCorrected_tendsto hc)
  · intro h ⟨q, hq⟩
    exact h ⟨q, gcdCorrected_eventually_eq_of_rational q hq.symm⟩

end RowGcdEquality

#print axioms RowGcdEquality.rowGcd_eventually_eq_tail_of_rational
#print axioms RowGcdEquality.gcdCorrected_eventually_eq_of_rational

#print axioms RowGcdEquality.rowGcd_div_factorial_tendsto_zero
#print axioms RowGcdEquality.irrational_iff_gcdCorrected_not_eventually_constant
