import FormalConjecturesUtil

/-! An elementary explicit maximal-order upper bound for the divisor count.
No prime number theorem is used. -/
namespace Erdos322Research.DivisorMaximalOrder
open Finset
set_option maxHeartbeats 0
set_option Elab.async false

lemma exponent_factor_bound (a t : ℕ) (ht : 0 < t) :
    (a+1)^t ≤ t^t*2^a := by
  have hrem := Nat.mod_lt a ht
  have hdiv := Nat.mod_add_div a t
  have hlin : a+1 ≤ t*(a/t+1) := by nlinarith
  have hp : a/t+1 ≤ 2^(a/t) := Nat.lt_two_pow_self
  calc
    (a+1)^t ≤ (t*2^(a/t))^t := Nat.pow_le_pow_left (hlin.trans (Nat.mul_le_mul_left t hp)) t
    _ = t^t*2^((a/t)*t) := by rw [mul_pow,← pow_mul]
    _ ≤ t^t*2^a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self a t))

/-- A fully explicit family of divisor bounds, with a natural-number power. -/
theorem divisor_power_bound (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    n.divisors.card^t ≤ t^(t*2^t)*n := by
  classical
  have htone : 1 ≤ t := ht
  have hlocal (p a : ℕ) (hp : p.Prime) :
      (a+1)^t ≤ (if p < 2^t then t^t else 1)*p^a := by
    by_cases hh : p < 2^t
    · rw [if_pos hh]
      exact (exponent_factor_bound a t ht).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le a))
    · rw [if_neg hh,one_mul]
      calc
        (a+1)^t ≤ (2^a)^t := Nat.pow_le_pow_left Nat.lt_two_pow_self t
        _ = (2^t)^a := by rw [← pow_mul,← pow_mul]; congr 1; ring
        _ ≤ p^a := Nat.pow_le_pow_left (by omega) a
  have hconst : (∏ p ∈ n.primeFactors, if p < 2^t then t^t else 1) ≤ t^(t*2^t) := by
    rw [← prod_filter,prod_const,← pow_mul]
    apply Nat.pow_le_pow_right ht
    apply Nat.mul_le_mul_left
    have hs : n.primeFactors.filter (fun p ↦ p < 2^t) ⊆ range (2^t) := by
      intro p hp
      exact mem_range.mpr (mem_filter.mp hp).2
    simpa using card_le_card hs
  have hprod : (∏ p ∈ n.primeFactors, p^n.factorization p)=n := by
    simpa only [Finsupp.prod,Nat.support_factorization] using Nat.factorization_prod_pow_eq_self hn.ne'
  calc
    n.divisors.card^t = ∏ p ∈ n.primeFactors, (n.factorization p+1)^t := by
      rw [Nat.card_divisors hn.ne',Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors, (if p < 2^t then t^t else 1)*p^n.factorization p :=
      prod_le_prod' fun p hp ↦ hlocal p _ (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, if p < 2^t then t^t else 1)*n := by rw [prod_mul_distrib,hprod]
    _ ≤ t^(t*2^t)*n := Nat.mul_le_mul_right n hconst

lemma constant_le_double_power (t : ℕ) : t^(t*2^t) ≤ 2^(2^(4*t)) := by
  have ht : t ≤ 2^t := Nat.lt_two_pow_self.le
  calc
    t^(t*2^t) ≤ (2^t)^(t*2^t) := Nat.pow_le_pow_left ht _
    _ = 2^(t*t*2^t) := by rw [← pow_mul]; congr 1; ring
    _ ≤ 2^((2^t)*(2^t)*2^t) := by gcongr; norm_num
    _ = 2^(2^(3*t)) := by congr 1; rw [← pow_add,← pow_add]; congr 1; omega
    _ ≤ 2^(2^(4*t)) := by gcongr <;> norm_num

/-- Once n is in a suitable double-exponential block, a small power of its
divisor count is bounded by n squared. -/
theorem divisor_power_le_square (n t : ℕ) (ht : 0 < t)
    (hn : 2^(2^(4*t)) ≤ n) : n.divisors.card^t ≤ n^2 := by
  have hnpos : 0 < n := (pow_pos (by decide) _).trans_le hn
  calc
    n.divisors.card^t ≤ t^(t*2^t)*n := divisor_power_bound n t hnpos ht
    _ ≤ n*n := Nat.mul_le_mul_right _ ((constant_le_double_power t).trans hn)
    _ = n^2 := by ring

/-- Double-exponential blocks can be chosen using two integer logarithms. -/
lemma exists_double_power_block (n : ℕ) (hn : 65536 ≤ n) :
    ∃ t : ℕ, 0 < t ∧ 2^(2^(4*t)) ≤ n ∧ n < 2^(2^(4*(t+1))) := by
  let L := Nat.log 2 n
  let r := Nat.log 2 L
  let t := r/4
  have hL : 16 ≤ L := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hn)
  have hr : 4 ≤ r := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hL)
  have ht : 0 < t := by dsimp only [t]; omega
  have hn0 : n ≠ 0 := by omega
  have hL0 : L ≠ 0 := by omega
  have hrl : 2^r ≤ L := Nat.pow_log_le_self 2 hL0
  have hLn : 2^L ≤ n := Nat.pow_log_le_self 2 hn0
  have hLup : L < 2^(r+1) := Nat.lt_pow_succ_log_self (by decide) L
  have hnup : n < 2^(L+1) := Nat.lt_pow_succ_log_self (by decide) n
  refine ⟨t,ht,?_,?_⟩
  · exact (Nat.pow_le_pow_right (by decide)
      ((Nat.pow_le_pow_right (by decide) (by dsimp only [t]; omega)).trans hrl)).trans hLn
  · apply hnup.trans_le
    apply Nat.pow_le_pow_right (by decide)
    exact (show L+1 ≤ 2^(r+1) by omega).trans
      (Nat.pow_le_pow_right (by decide) (by dsimp only [t]; omega))

/-- Explicit maximal-order bound. The constant 16 is deliberately generous. -/
theorem divisor_count_upper_up_to (n q : ℕ) (hn : 65536 ≤ n)
    (hq : 0 < q) (hqn : q ≤ n) :
    (q.divisors.card : ℝ) ≤ Real.exp (16*Real.log (n : ℝ)/Real.log (Real.log (n : ℝ))) := by
  obtain ⟨t,ht,hlow,hup⟩ := exists_double_power_block n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogn : 1 < Real.log (n : ℝ) := by
    have h16 : (16 : ℝ) ≤ n := by exact_mod_cast (show 16 ≤ n by omega)
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16) h16
    have he : Real.log 16=4*Real.log 2 := by rw [show (16 : ℝ)=2^4 by norm_num,Real.log_pow]; norm_num
    rw [he] at hh
    linarith [Real.log_two_gt_d9]
  have hLLpos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlogn
  have hlogup : Real.log (n : ℝ) ≤ (2 : ℝ)^(4*(t+1)) := by
    have hcast : (n : ℝ) ≤ (2 : ℝ)^(2^(4*(t+1))) := by exact_mod_cast hup.le
    have hh := Real.log_le_log hnpos hcast
    rw [Real.log_pow] at hh
    have he : ((2^(4*(t+1)) : ℕ) : ℝ)=(2 : ℝ)^(4*(t+1)) := by norm_cast
    rw [he] at hh
    exact hh.trans (mul_le_of_le_one_right (by positivity) hlog2le)
  have hLL : Real.log (Real.log (n : ℝ)) ≤ 8*(t : ℝ) := by
    have hh := Real.log_le_log (by linarith : 0 < Real.log (n : ℝ)) hlogup
    rw [Real.log_pow] at hh
    push_cast at hh
    have htone : (1 : ℝ) ≤ t := by exact_mod_cast ht
    nlinarith
  have hdpos : 0 < q.divisors.card := card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hq.ne'⟩
  have hdr : (0 : ℝ) < q.divisors.card := by exact_mod_cast hdpos
  have hdlog : 0 ≤ Real.log (q.divisors.card : ℝ) := Real.log_nonneg (by exact_mod_cast hdpos)
  have hdp : (q.divisors.card : ℝ)^t ≤ (n : ℝ)^2 := by
    have hconst := (constant_le_double_power t).trans hlow
    have hh : q.divisors.card^t ≤ n^2 := by
      calc
        q.divisors.card^t ≤ t^(t*2^t)*q := divisor_power_bound q t hq ht
        _ ≤ n*n := Nat.mul_le_mul hconst hqn
        _ = n^2 := by ring
    exact_mod_cast hh
  have hlogs := Real.log_le_log (pow_pos hdr _) hdp
  rw [Real.log_pow,Real.log_pow] at hlogs
  norm_num only [Nat.cast_ofNat] at hlogs
  have hb : Real.log (q.divisors.card : ℝ) ≤ 16*Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)) := by
    apply (le_div_iff₀ hLLpos).mpr
    have hh := mul_le_mul_of_nonneg_left hLL hdlog
    nlinarith
  simpa only [Real.exp_log hdr] using Real.exp_le_exp.mpr hb

/-- The maximal-order upper bound at the integer itself. -/
theorem divisor_count_upper (n : ℕ) (hn : 65536 ≤ n) :
    (n.divisors.card : ℝ) ≤ Real.exp (16*Real.log (n : ℝ)/Real.log (Real.log (n : ℝ))) :=
  divisor_count_upper_up_to n n hn (by omega) le_rfl

end Erdos322Research.DivisorMaximalOrder
