import Submission.LambertFixedOperatorNonvanishing
import Submission.LambertBoundaryClearing

/-!
Quantitative prime detection for Lambert shift operators whose leading
coefficient has a smooth factor and a bounded remaining factor. These
statements locate nonzero forms; they do not clear their boundaries and do
not settle the irrationality conjecture.
-/

namespace LambertQuantitativeNonvanishing

open Finset LambertFixedOperatorNonvanishing LambertBoundaryClearing

/-- A nonzero integer smaller than `(H+1)^r` cannot contain all the prime
factors supplied by `r` successive applications of Bertrand's postulate. -/
lemma prime_not_dvd_in_dyadic_window (H r a : ℕ) (hH : 0 < H)
    (ha : 0 < a) (hsmall : a < (H+1)^r) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ≤ 2^r*H ∧ ¬p ∣ a := by
  induction r generalizing a with
  | zero => simp only [pow_zero] at hsmall; omega
  | succ r ih =>
    have hpow : 1 ≤ 2^r := by
      have : 0 < 2^r := by positivity
      omega
    obtain ⟨p, hp, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul
      (2^r*H) (by positivity)
    have hHp : H < p := lt_of_le_of_lt (by nlinarith) hpgt
    have htop : p ≤ 2^(r+1)*H := by simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hple
    by_cases hpa : p ∣ a
    · obtain ⟨b, hab⟩ := hpa
      have hb : 0 < b := by nlinarith
      have hbsmall : b < (H+1)^r := by
        rw [pow_succ, hab] at hsmall
        by_contra hn
        have hbl : (H+1)^r ≤ b := by omega
        have hm := Nat.mul_le_mul (show H+1 ≤ p by omega) hbl
        nlinarith
      obtain ⟨q, hq, hHq, hqle, hqb⟩ := ih b hb hbsmall
      refine ⟨q, hq, hHq, hqle.trans ?_, ?_⟩
      · have ht : 2^r ≤ 2^(r+1) := Nat.pow_le_pow_right (by decide) (by omega)
        exact Nat.mul_le_mul_right H ht
      · intro hqa
        rw [hab] at hqa
        rcases hq.dvd_mul.mp hqa with hqp | hqb'
        · have he := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
          omega
        · exact hqb hqb'
    · exact ⟨p, hp, hHp, htop, hpa⟩

/-- Polynomial weight bounds give a constant-factor prime-index window
when the exponent is fixed. -/
lemma prime_not_dvd_of_power_bound (H r a : ℕ) (hH : 0 < H)
    (hr : 0 < r) (ha : 0 < a) (hsmall : a ≤ H^r) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ≤ 2^r*H ∧ ¬p ∣ a := by
  apply prime_not_dvd_in_dyadic_window H r a hH ha
  exact hsmall.trans_lt (Nat.pow_lt_pow_left (by omega) (by omega))

/-- The extra factor of the leading coefficient need not be small, provided
no prime above H divides it. -/
theorem coefficientForm_ne_zero_in_window (w : ℕ → ℤ) (D H r P : ℕ) (z : ℤ)
    (hH : 0 < H) (hD : D ≤ H) (hr : 0 < r)
    (hz : z ≠ 0) (hsize : z.natAbs ≤ H^r)
    (hlead : w D = (P : ℤ)*z)
    (hsmooth : ∀ p : ℕ, p.Prime → H < p → ¬p ∣ P) :
    ∃ n : ℕ, H-D < n ∧ n+D ≤ 2^r*H ∧ coefficientForm w D n ≠ 0 := by
  obtain ⟨p, hp, hHp, hple, hpz⟩ := prime_not_dvd_of_power_bound H r z.natAbs
    hH hr (Int.natAbs_pos.mpr hz) hsize
  refine ⟨p-D, by omega, by omega, ?_⟩
  apply coefficientForm_ne_zero_at_prime w D (p-D) p hp (by omega)
  rw [hlead, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast]
  exact hp.not_dvd_mul (hsmooth p hp hHp) hpz

/-- A nonzero coefficient form detects at least one of two adjacent tails,
with a bound uniform over operators satisfying the height hypotheses. -/
theorem tailForm_ne_zero_in_window (w : ℕ → ℤ) (D H r P : ℕ) (z : ℤ)
    (hH : 0 < H) (hD : D ≤ H) (hr : 0 < r)
    (hz : z ≠ 0) (hsize : z.natAbs ≤ H^r)
    (hlead : w D = (P : ℤ)*z)
    (hsmooth : ∀ p : ℕ, p.Prime → H < p → ¬p ∣ P) (x : ℝ) :
    ∃ n : ℕ, H-D ≤ n ∧ n+D ≤ 2^r*H ∧
      tailForm (fun i => (w i : ℚ)) D x n ≠ 0 := by
  obtain ⟨n, hn, hnle, hne⟩ := coefficientForm_ne_zero_in_window w D H r P z
    hH hD hr hz hsize hlead hsmooth
  have hn0 : 0 < n := by omega
  have hs := tailForm_sub_succ (fun i => (w i : ℚ)) D x (n-1)
  rw [show n-1+1 = n by omega] at hs
  by_cases he : tailForm (fun i => (w i : ℚ)) D x (n-1) = 0
  · refine ⟨n, by omega, hnle, ?_⟩
    intro hnext
    rw [he, hnext, sub_self] at hs
    apply hne
    unfold coefficientForm
    exact_mod_cast hs.symm
  · exact ⟨n-1, by omega, by omega, he⟩

/-- The factorial factor in a raw Lambert annihilator is smooth enough for
prime detection whenever the sum of its shifts is at most H. -/
lemma factorialProduct_smooth (ds : List ℕ) (H : ℕ) (hds : ds.sum ≤ H) :
    ∀ p : ℕ, p.Prime → H < p → ¬p ∣ factorialProduct ds := by
  intro p hp hHp hd
  have hfac : p ∣ H.factorial := hd.trans
    ((factorialProduct_dvd ds).trans (Nat.factorial_dvd_factorial hds))
  have := hp.dvd_factorial.mp hfac
  omega

/-- A specialization retaining the factorial product rather than bounding
its magnitude by the height of the final weight. -/
theorem factorial_leading_tail_ne_zero (w : ℕ → ℤ) (D H r : ℕ)
    (ds : List ℕ) (z : ℤ) (hH : 0 < H) (hD : D ≤ H) (hr : 0 < r)
    (hds : ds.sum ≤ H) (hz : z ≠ 0) (hsize : z.natAbs ≤ H^r)
    (hlead : w D = (factorialProduct ds : ℤ)*z) (x : ℝ) :
    ∃ n : ℕ, H-D ≤ n ∧ n+D ≤ 2^r*H ∧
      tailForm (fun i => (w i : ℚ)) D x n ≠ 0 :=
  tailForm_ne_zero_in_window w D H r (factorialProduct ds) z
    hH hD hr hz hsize hlead (factorialProduct_smooth ds H hds) x

/-- The prime test also detects nonintegrality, not just nonzero value. -/
lemma coefficientForm_integral_last_dvd (w : ℕ → ℤ) (D n p : ℕ)
    (hp : p.Prime) (hn : n+D = p) (v : ℤ)
    (he : coefficientForm w D n = v) : (p : ℤ) ∣ w D := by
  obtain ⟨z, hz⟩ := earlier_coefficients_integral w D n p hn hp.pos
  have hp0 := hp.pos
  have hfac : (p.factorial : ℚ) = p * ((p-1).factorial : ℚ) := by
    exact_mod_cast (by simpa [show p-1+1 = p by omega]
      using Nat.factorial_succ (p-1))
  rw [coefficientForm, sum_range_succ, hn, coefficient,
    Erdos68Development.lambertCoeff_prime hp, Nat.cast_one] at he
  have hm := congrArg (fun y : ℚ => (p.factorial : ℚ)*y) he
  have hh : (p : ℚ)*z + w D = (p.factorial : ℚ)*v := by
    calc
      _ = (p.factorial : ℚ) *
          ((∑ i ∈ range D, (w i : ℚ)*coefficient (n+i)) +
            (w D : ℚ)*(1/p.factorial)) := by
        rw [mul_add, hfac, ← hz]
        field_simp
      _ = _ := hm
  rw [hfac] at hh
  have hhZ : (p : ℤ)*z + w D =
      (p : ℤ)*((p-1).factorial : ℤ)*v := by exact_mod_cast hh
  exact ⟨((p-1).factorial : ℤ)*v-z, by linear_combination hhZ⟩

/-- Moving a nondivisible prime detector to two integral adjacent tails is
impossible: their difference would already force divisibility of the final
weight. This is why the quantitative index bound is not a clearing theorem. -/
lemma adjacent_tail_integrality_last_dvd (w : ℕ → ℤ) (D n p : ℕ)
    (hn0 : 0 < n) (hp : p.Prime) (hn : n+D = p) (x : ℝ) (u v : ℤ)
    (hu : tailForm (fun i => (w i : ℚ)) D x (n-1) = u)
    (hv : tailForm (fun i => (w i : ℚ)) D x n = v) :
    (p : ℤ) ∣ w D := by
  apply coefficientForm_integral_last_dvd w D n p hp hn (u-v)
  have hs := tailForm_sub_succ (fun i => (w i : ℚ)) D x (n-1)
  rw [show n-1+1 = n by omega, hu, hv] at hs
  unfold coefficientForm
  exact_mod_cast hs.symm

end LambertQuantitativeNonvanishing

#print axioms LambertQuantitativeNonvanishing.prime_not_dvd_in_dyadic_window
#print axioms LambertQuantitativeNonvanishing.coefficientForm_ne_zero_in_window
#print axioms LambertQuantitativeNonvanishing.tailForm_ne_zero_in_window

#print axioms LambertQuantitativeNonvanishing.factorial_leading_tail_ne_zero
#print axioms LambertQuantitativeNonvanishing.adjacent_tail_integrality_last_dvd
