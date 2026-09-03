import Submission.PrimeBlockVariance

/-!
Uniform exponential upper tails for nonnegative prime-divisor scores. The
Euler-product bound holds in every natural prefix, with no remainder term.
These are one-sided estimates with a fixed full-block center, not signed
moving-center bounds and not a settlement of the cube-Sidon conjecture.
-/
namespace Erdos1206.PrimeBlockExponential
open Finset PrimeBlockVariance
open scoped Classical

private lemma prime_prod_dvd_iff (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
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
      apply hpP.mul_dvd_of_dvd_of_dvd (h p (mem_insert_self _ _))
      exact (ih (fun q hq => hP q (mem_insert_of_mem hq))).mpr
        (fun q hq => h q (mem_insert_of_mem hq))

private lemma prod_indicator (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
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

/-- The elementary multiplicative moment bound. Nonnegative expansion
coefficients are essential: the floor error can then only lower the sum. -/
theorem product_moment_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℝ) (hv : ∀ p ∈ P, 0 ≤ v p) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∏ p ∈ P, (1+v p*indicator p n)) ≤
      (N:ℝ)*∏ p ∈ P, (1+v p/p) := by
  simp_rw [prod_one_add]
  rw [sum_comm,mul_sum]
  apply sum_le_sum
  intro Q hQ
  have hQP := mem_powerset.mp hQ
  have hQprime : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
  have he (n : ℕ) : (∏ p ∈ Q, v p*indicator p n) =
      (∏ p ∈ Q, v p)*indicator (∏ p ∈ Q, p) n := by
    rw [prod_mul_distrib,prod_indicator Q hQprime]
  simp_rw [he]
  rw [←mul_sum,sum_indicator]
  have hvQ : 0 ≤ ∏ p ∈ Q, v p := prod_nonneg (fun p hp => hv p (hQP hp))
  calc
    _ ≤ (∏ p ∈ Q, v p)*((N:ℝ)/(∏ p ∈ Q,p : ℕ)) :=
      mul_le_mul_of_nonneg_left Nat.cast_div_le hvQ
    _ = _ := by rw [prod_div_distrib]; push_cast; ring

/-- A Chernoff moment estimate, valid for arbitrary finite prime blocks and
nonnegative real weights, at every prefix length. -/
theorem exponential_moment_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.exp (t*primeSum P w n)) ≤
      (N:ℝ)*Real.exp (∑ p ∈ P, (Real.exp (t*w p)-1)/p) := by
  have hterm (p n : ℕ) : Real.exp (t*(w p*indicator p n)) =
      1+(Real.exp (t*w p)-1)*indicator p n := by
    by_cases hpn : p ∣ n <;> simp [indicator,hpn]
  have he (n : ℕ) : Real.exp (t*primeSum P w n) =
      ∏ p ∈ P, (1+(Real.exp (t*w p)-1)*indicator p n) := by
    simp only [primeSum,mul_sum,Real.exp_sum,hterm]
  simp_rw [he]
  have hv (p : ℕ) (hp : p ∈ P) : 0 ≤ Real.exp (t*w p)-1 := by
    have hh := Real.one_le_exp_iff.mpr (mul_nonneg ht (hw p hp))
    linarith
  apply (product_moment_le P hP _ hv N).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  rw [Real.exp_sum]
  apply prod_le_prod
  · intro p hp
    have : 0 ≤ (Real.exp (t*w p)-1)/(p:ℝ) := div_nonneg (hv p hp) (Nat.cast_nonneg p)
    linarith
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp ((Real.exp (t*w p)-1)/p)

/-- The full-block centered exponent has the usual cumulant
`sum_p (exp(t*w_p)-1-t*w_p)/p`. This is one-sided: `t` is nonnegative. -/
theorem centered_exponential_moment_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) {t : ℝ} (ht : 0 ≤ t) (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.exp (t*(primeSum P w n-mean P w))) ≤
      (N:ℝ)*Real.exp (∑ p ∈ P, (Real.exp (t*w p)-1-t*w p)/p) := by
  have he (n : ℕ) : Real.exp (t*(primeSum P w n-mean P w)) =
      Real.exp (-(t*mean P w))*Real.exp (t*primeSum P w n) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [←mul_sum]
  apply (mul_le_mul_of_nonneg_left (exponential_moment_le P hP w hw ht N)
    (Real.exp_pos _).le).trans_eq
  rw [mul_left_comm,←Real.exp_add]
  congr 2
  simp only [mean,mul_sum,←sum_neg_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  ring

/-- A remainder-free upper-tail bound, including the full prime block even
when some of its primes exceed the prefix cutoff. -/
theorem upper_tail_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) {t : ℝ} (ht : 0 ≤ t)
    (R : ℝ) (N : ℕ) :
    (((Icc 1 N).filter (fun n => R < primeSum P w n-mean P w)).card:ℝ) ≤
      (N:ℝ)*Real.exp ((∑ p ∈ P, (Real.exp (t*w p)-1-t*w p)/p)-t*R) := by
  let B := (Icc 1 N).filter (fun n => R < primeSum P w n-mean P w)
  have hb : (B.card:ℝ)*Real.exp (t*R) ≤
      (N:ℝ)*Real.exp (∑ p ∈ P, (Real.exp (t*w p)-1-t*w p)/p) := by
    calc
      _ = ∑ _n ∈ B, Real.exp (t*R) := by simp
      _ ≤ ∑ n ∈ B, Real.exp (t*(primeSum P w n-mean P w)) := by
        apply sum_le_sum
        intro n hn
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mem_filter.mp hn).2.le ht)
      _ ≤ ∑ n ∈ Icc 1 N, Real.exp (t*(primeSum P w n-mean P w)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => (Real.exp_pos _).le)
      _ ≤ _ := centered_exponential_moment_le P hP w hw ht N
  have hh := (le_div_iff₀ (Real.exp_pos (t*R))).mpr hb
  simpa only [Real.exp_sub,mul_div_assoc,B] using hh

#print axioms product_moment_le
#print axioms centered_exponential_moment_le
#print axioms upper_tail_le
end Erdos1206.PrimeBlockExponential
