import Submission.PrimeBlockExponential

/-!
Exact signed finite-prime Euler-product comparisons, with explicit error.
The error is not asserted to be uniform over expanding prime blocks. In
particular these lemmas do not yet give signed moving-center concentration.
-/
namespace Erdos1206.SignedPrimeBlockExponential
open Finset PrimeBlockVariance
open scoped Classical

lemma prime_prod_dvd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∏ p ∈ P, p) ∣ n ↔ ∀ p ∈ P, p ∣ n := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hpP : Nat.Coprime p (∏ q ∈ P, q) := Nat.Coprime.prod_right (fun q hq =>
      (Nat.coprime_primes (hP p (mem_insert_self _ _))
        (hP q (mem_insert_of_mem hq))).mpr (fun hh => hp (hh ▸ hq)))
    rw [prod_insert hp]
    constructor
    · intro h q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact (dvd_mul_right q _).trans h
      · exact (ih (fun q hq => hP q (mem_insert_of_mem hq))).mp
          ((dvd_mul_left _ p).trans h) q hq
    · intro h
      exact hpP.mul_dvd_of_dvd_of_dvd (h p (mem_insert_self _ _))
        ((ih (fun q hq => hP q (mem_insert_of_mem hq))).mpr
          (fun q hq => h q (mem_insert_of_mem hq)))

lemma prod_indicator (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∏ p ∈ P, indicator p n) = indicator (∏ p ∈ P, p) n := by
  by_cases h : ∀ p ∈ P, p ∣ n
  · have he (p : ℕ) (hp : p ∈ P) : indicator p n = 1 := by simp [indicator,h p hp]
    rw [prod_congr rfl he]
    simp only [prod_const_one,indicator,(prime_prod_dvd_iff P hP n).mpr h,if_true]
  · have hd := mt (prime_prod_dvd_iff P hP n).mp h
    push_neg at h
    obtain ⟨p,hp,hpn⟩ := h
    rw [show indicator (∏ q ∈ P, q) n = 0 by simp [indicator,hd]]
    exact prod_eq_zero hp (by simp [indicator,hpn])

/-- Signed expansion remains an exact identity; no independence assertion is
used for the arithmetic sample. -/
theorem product_moment_exact (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∏ p ∈ P, (1+v p*indicator p n)) =
      ∑ Q ∈ P.powerset, (∏ p ∈ Q, v p)*(N/(∏ p ∈ Q,p) : ℕ) := by
  simp_rw [prod_one_add]
  rw [sum_comm]
  apply sum_congr rfl
  intro Q hQ
  have hQprime : ∀ p ∈ Q, p.Prime := fun p hp => hP p (mem_powerset.mp hQ hp)
  simp_rw [prod_mul_distrib,prod_indicator Q hQprime]
  rw [←mul_sum,sum_indicator]

/-- The discrepancy of an arbitrary signed divisor polynomial is bounded by
its coefficient l1 norm. -/
theorem divisor_polynomial_discrepancy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (c : Finset ℕ → ℝ) (N : ℕ) :
    |(∑ Q ∈ P.powerset, c Q*(N/(∏ p ∈ Q,p) : ℕ))-
      (N:ℝ)*(∑ Q ∈ P.powerset, c Q/(∏ p ∈ Q,p : ℕ))| ≤
        ∑ Q ∈ P.powerset, |c Q| := by
  have he : (∑ Q ∈ P.powerset, c Q*(N/(∏ p ∈ Q,p) : ℕ))-
      (N:ℝ)*(∑ Q ∈ P.powerset, c Q/(∏ p ∈ Q,p : ℕ)) =
        ∑ Q ∈ P.powerset, c Q*((N/(∏ p ∈ Q,p) : ℕ)-(N:ℝ)/(∏ p ∈ Q,p : ℕ)) := by
    rw [mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intros
    ring
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro Q hQ
  have hprod : 0 < ∏ p ∈ Q,p := prod_pos (fun p hp => (hP p (mem_powerset.mp hQ hp)).pos)
  have hh := quotient_error hprod N
  rw [abs_mul]
  have hab : |(N/(∏ p ∈ Q,p) : ℕ)-(N:ℝ)/(∏ p ∈ Q,p : ℕ)| ≤ 1 :=
    abs_le.mpr ⟨hh.1,hh.2.trans (by norm_num)⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hab (abs_nonneg (c Q))

/-- Unlike the nonnegative case, the general signed product has a remainder.
No uniformity in the size of P is silently assumed. -/
theorem product_moment_discrepancy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℝ) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, ∏ p ∈ P, (1+v p*indicator p n))-
      (N:ℝ)*∏ p ∈ P, (1+v p/p)| ≤ ∏ p ∈ P, (1+|v p|) := by
  rw [product_moment_exact P hP,prod_one_add,prod_one_add]
  have he (Q : Finset ℕ) : (∏ p ∈ Q, v p/p)=(∏ p ∈ Q,v p)/(∏ p ∈ Q,p : ℕ) := by
    rw [prod_div_distrib]; push_cast; rfl
  simp_rw [he]
  have hh := divisor_polynomial_discrepancy P hP (fun Q => ∏ p ∈ Q,v p) N
  simpa only [abs_prod] using hh

/-- Signed exponential comparison with its exact Bernoulli Euler product.
The factor `prod (1+|exp(t*w_p)-1|)` is the explicit finite-prefix error. -/
theorem exponential_moment_discrepancy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w : ℕ → ℝ) (t : ℝ) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, Real.exp (t*primeSum P w n))-
      (N:ℝ)*∏ p ∈ P, (1+(Real.exp (t*w p)-1)/p)| ≤
        ∏ p ∈ P, (1+|Real.exp (t*w p)-1|) := by
  have he (n : ℕ) : Real.exp (t*primeSum P w n) =
      ∏ p ∈ P, (1+(Real.exp (t*w p)-1)*indicator p n) := by
    simp only [primeSum,mul_sum,Real.exp_sum]
    apply prod_congr rfl
    intro p hp
    by_cases hpn : p ∣ n <;> simp [indicator,hpn]
  simp_rw [he]
  exact product_moment_discrepancy P hP _ N

/-- The cumulant upper bound is valid for arbitrary signed real weights,
but retains the explicit remainder. -/
theorem signed_centered_exponential_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w : ℕ → ℝ) (t : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.exp (t*(primeSum P w n-mean P w))) ≤
      (N:ℝ)*Real.exp (∑ p ∈ P,(Real.exp (t*w p)-1-t*w p)/p)+
        Real.exp (-(t*mean P w))*∏ p ∈ P,(1+|Real.exp (t*w p)-1|) := by
  have hdis := (abs_le.mp (exponential_moment_discrepancy P hP w t N)).2
  have hprod : (∏ p ∈ P, (1+(Real.exp (t*w p)-1)/p)) ≤
      Real.exp (∑ p ∈ P,(Real.exp (t*w p)-1)/p) := by
    rw [Real.exp_sum]
    apply prod_le_prod
    · intro p hp
      have hpR : (1:ℝ) < p := by exact_mod_cast (hP p hp).one_lt
      have he := Real.exp_pos (t*w p)
      have heq : (1+(Real.exp (t*w p)-1)/(p:ℝ))=(p+Real.exp (t*w p)-1)/p := by
        field_simp; ring
      rw [heq]
      exact div_nonneg (by linarith) (Nat.cast_nonneg p)
    · intro p hp
      simpa only [add_comm] using Real.add_one_le_exp ((Real.exp (t*w p)-1)/p)
  have hex (n : ℕ) : Real.exp (t*(primeSum P w n-mean P w)) =
      Real.exp (-(t*mean P w))*Real.exp (t*primeSum P w n) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [hex]
  rw [←mul_sum]
  have hh := mul_le_mul_of_nonneg_left
    (show (∑ n ∈ Icc 1 N, Real.exp (t*primeSum P w n)) ≤
      (N:ℝ)*Real.exp (∑ p ∈ P,(Real.exp (t*w p)-1)/p)+
        ∏ p ∈ P,(1+|Real.exp (t*w p)-1|) by
      have hn := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg N)
      linarith)
    (Real.exp_pos (-(t*mean P w))).le
  apply hh.trans_eq
  rw [mul_add,mul_left_comm,←Real.exp_add]
  congr 2
  simp only [mean,mul_sum,←sum_neg_distrib,←sum_add_distrib]
  apply congrArg Real.exp
  apply sum_congr rfl
  intro p hp
  ring

#print axioms product_moment_discrepancy
#print axioms exponential_moment_discrepancy
#print axioms signed_centered_exponential_le
end Erdos1206.SignedPrimeBlockExponential
