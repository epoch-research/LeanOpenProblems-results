import Submission.DivisorMoments
import Submission.CompositeRoughProgressions

/-!
# Higher divisor weights for a cofactor sieve

The prime-weighted lower moment needed for Erdős 821 is not assumed or
proved here. These auxiliary estimates develop its upper-bound counterpart.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 2000000

noncomputable def tau (k n : ℕ) : ℕ := ((ζ : ArithmeticFunction ℕ)^k) n

@[simp] lemma tau_zero_input (k : ℕ) : tau k 0 = 0 := by simp [tau]

lemma tau_multiplicative (k : ℕ) : ((ζ : ArithmeticFunction ℕ)^k).IsMultiplicative := by
  induction k with
  | zero => simpa using (isMultiplicative_one (R := ℕ))
  | succ k ih => simpa only [pow_succ] using ih.mul isMultiplicative_zeta

lemma tau_mul_coprime (k : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    tau k (a*b) = tau k a * tau k b :=
  (tau_multiplicative k).map_mul_of_coprime hab

lemma tau_succ (k n : ℕ) : tau (k+1) n = ∑ d ∈ n.divisors, tau k d := by
  simp only [tau, _root_.pow_succ', zeta_mul_apply]

lemma tau_prime_pow (k e p : ℕ) (hp : p.Prime) :
    tau (k+1) (p^e) = (e+k).choose k := by
  induction k generalizing e with
  | zero => simp [tau, zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]
  | succ k ih =>
    rw [tau_succ, Nat.sum_divisors_prime_pow hp]
    simp_rw [ih]
    exact Nat.sum_range_add_choose e k

lemma tau_prime_pow_succ_le (k e p : ℕ) (hp : p.Prime) :
    tau (k+1) (p^(e+1)) ≤ (k+1)*tau (k+1) (p^e) := by
  rw [tau_prime_pow k (e+1) p hp, tau_prime_pow k e p hp]
  have he := Nat.choose_mul_succ_eq (e+k) k
  have he' : (e+k).choose k * (e+k+1) = (e+1+k).choose k * (e+1) := by
    simpa only [Nat.add_right_comm e k 1, Nat.add_sub_cancel] using he
  apply Nat.le_of_mul_le_mul_right (c := e+1) _ (by omega)
  nlinarith [Nat.zero_le (e*k*(e+k).choose k)]

lemma tau_prime_mul_le (k p n : ℕ) (hp : p.Prime) :
    tau (k+1) (p*n) ≤ (k+1)*tau (k+1) n := by
  by_cases hn : n = 0
  · simp [hn]
  let e := n.factorization p
  let a := n / p^e
  have heq : p^e*a = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hc : p.Coprime a := Nat.coprime_ordCompl hp hn
  have hpn : p*n = p^(e+1)*a := by rw [← heq, Nat.pow_succ']; ring
  rw [hpn, tau_mul_coprime (k+1) (hc.pow_left (e+1)), ← heq,
    tau_mul_coprime (k+1) (hc.pow_left e)]
  exact (Nat.mul_le_mul_right (tau (k+1) a) (tau_prime_pow_succ_le k e p hp)).trans_eq
    (by ring)

lemma tau_prime_product_mul_le (k : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (a : ℕ) :
    tau (k+1) ((∏ p ∈ S, p)*a) ≤ (k+1)^S.card * tau (k+1) a := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hpr : p.Prime := hS p (Finset.mem_insert_self _ _)
    have hrest : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp, Finset.card_insert_of_notMem hp, Nat.pow_succ]
    calc
      tau (k+1) ((p*(∏ q ∈ S, q))*a) =
          tau (k+1) (p*((∏ q ∈ S, q)*a)) := by rw [mul_assoc]
      _ ≤ (k+1)*tau (k+1) ((∏ q ∈ S, q)*a) := tau_prime_mul_le k p _ hpr
      _ ≤ (k+1)*((k+1)^S.card*tau (k+1) a) := Nat.mul_le_mul_left _ (ih hrest)
      _ = _ := by ring

noncomputable def harmonicMoment (k A : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 A, (tau k n : ℝ)/(n : ℝ)

lemma harmonicMoment_nonneg (k A : ℕ) : 0 ≤ harmonicMoment k A := by
  exact Finset.sum_nonneg (fun n _ => by positivity)

lemma harmonicMoment_mono (k : ℕ) {A B : ℕ} (hAB : A ≤ B) :
    harmonicMoment k A ≤ harmonicMoment k B := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hAB⟩
  · intro n _ _
    positivity

lemma sum_tau_inv_multiples_le (k A : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∑ n ∈ Finset.Icc 1 A with (∏ p ∈ S, p) ∣ n,
      (tau (k+1) n : ℝ)/(n : ℝ)) ≤
        (k+1 : ℝ)^S.card / ((∏ p ∈ S, p : ℕ) : ℝ) * harmonicMoment (k+1) A := by
  let d := ∏ p ∈ S, p
  let E := (Finset.Icc 1 A).filter (fun n => d ∣ n)
  have hd : 0 < d := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hinj : Set.InjOn (fun n : ℕ => n/d) (↑E : Set ℕ) := by
    intro n hn m hm he
    change n ∈ E at hn
    change m ∈ E at hm
    have hdn := (Finset.mem_filter.mp hn).2
    have hdm := (Finset.mem_filter.mp hm).2
    change n/d = m/d at he
    rw [← Nat.mul_div_cancel' hdn, ← Nat.mul_div_cancel' hdm, he]
  have hsub : E.image (fun n => n/d) ⊆ Finset.Icc 1 A := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hmI, hdm⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hmI).1 hdm) hd,
      (Nat.div_le_self m d).trans (Finset.mem_Icc.mp hmI).2⟩
  have hpoint (n : ℕ) (hn : n ∈ E) :
      (tau (k+1) n : ℝ)/(n : ℝ) ≤
        (k+1 : ℝ)^S.card / (d : ℝ) *
          ((tau (k+1) (n/d) : ℝ) / ((n/d : ℕ) : ℝ)) := by
    obtain ⟨hnI, hdn⟩ := Finset.mem_filter.mp hn
    have he : d*(n/d) = n := Nat.mul_div_cancel' hdn
    have hb := tau_prime_product_mul_le k S hS (n/d)
    change tau (k+1) (d*(n/d)) ≤ (k+1)^S.card*tau (k+1) (n/d) at hb
    rw [he] at hb
    have hbR : (tau (k+1) n : ℝ) ≤ (k+1 : ℝ)^S.card*(tau (k+1) (n/d) : ℝ) := by
      exact_mod_cast hb
    have hh := div_le_div_of_nonneg_right hbR (Nat.cast_nonneg n)
    apply hh.trans_eq
    have heR : (d : ℝ)*((n/d : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast he
    rw [← heR]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  calc
    _ ≤ ∑ n ∈ E, (k+1 : ℝ)^S.card / (d : ℝ) *
        ((tau (k+1) (n/d) : ℝ) / ((n/d : ℕ) : ℝ)) := Finset.sum_le_sum hpoint
    _ = (k+1 : ℝ)^S.card / (d : ℝ) *
        ∑ n ∈ E.image (fun n => n/d), (tau (k+1) n : ℝ)/(n : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)) (by positivity)

/-- A prime-factor weight costs one factor of the divisor order at each
selected prime, rather than exponentiating an averaged constant. -/
lemma harmonicMoment_prime_product_le (k A : ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ (A+1).primesBelow, 0 ≤ w p) :
    (∑ n ∈ Finset.Icc 1 A, (tau (k+1) n : ℝ) *
      (∏ p ∈ n.primeFactors, (1+w p)) / (n : ℝ)) ≤
        harmonicMoment (k+1) A *
          ∏ p ∈ (A+1).primesBelow, (1+(k+1 : ℝ)*w p/(p : ℝ)) := by
  let Q := (A+1).primesBelow
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime := (Nat.mem_primesBelow.mp hp).2
  have hsub (n : ℕ) (hn : n ∈ Finset.Icc 1 A) : n.primeFactors ⊆ Q := by
    intro p hp
    have hpn := Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.mem_primesBelow.mpr ⟨by have := (Finset.mem_Icc.mp hn).2; omega,
      Nat.prime_of_mem_primeFactors hp⟩
  have hexpand (n : ℕ) (hn : n ∈ Finset.Icc 1 A) :
      (∏ p ∈ n.primeFactors, (1+w p)) =
        ∑ S ∈ Q.powerset, if (∏ p ∈ S, p) ∣ n then ∏ p ∈ S, w p else 0 := by
    have hfilter : Q.powerset.filter (fun S => (∏ p ∈ S, p) ∣ n) = n.primeFactors.powerset := by
      ext S
      constructor
      · intro hS
        obtain ⟨hSQ, hd⟩ := Finset.mem_filter.mp hS
        apply Finset.mem_powerset.mpr
        intro p hp
        exact (hQ p (Finset.mem_powerset.mp hSQ hp)).mem_primeFactors
          ((Finset.dvd_prod_of_mem _root_.id hp).trans hd) (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
      · intro hS
        have hSn := Finset.mem_powerset.mp hS
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hSn.trans (hsub n hn)), ?_⟩
        exact (Sieve.prod_primes_dvd_iff S (fun p hp => Nat.prime_of_mem_primeFactors (hSn hp)) n).mpr
          (fun p hp => Nat.dvd_of_mem_primeFactors (hSn hp))
    rw [← Finset.sum_filter, hfilter, ← Finset.prod_one_add]
  have hwS (S : Finset ℕ) (hS : S ∈ Q.powerset) : 0 ≤ ∏ p ∈ S, w p :=
    Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp hS hp))
  calc
    _ = ∑ n ∈ Finset.Icc 1 A, ∑ S ∈ Q.powerset,
        (∏ p ∈ S, w p) *
          (if (∏ p ∈ S, p) ∣ n then (tau (k+1) n : ℝ)/(n : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hexpand n hn, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S hS
      split_ifs <;> ring
    _ = ∑ S ∈ Q.powerset, (∏ p ∈ S, w p) *
        ∑ n ∈ Finset.Icc 1 A with (∏ p ∈ S, p) ∣ n,
          (tau (k+1) n : ℝ)/(n : ℝ) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter, Finset.mul_sum]
    _ ≤ ∑ S ∈ Q.powerset, (∏ p ∈ S, w p) *
        ((k+1 : ℝ)^S.card / ((∏ p ∈ S, p : ℕ) : ℝ) * harmonicMoment (k+1) A) := by
      apply Finset.sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left (sum_tau_inv_multiples_le k A S
        (fun p hp => hQ p (Finset.mem_powerset.mp hS hp))) (hwS S hS)
    _ = harmonicMoment (k+1) A *
        ∑ S ∈ Q.powerset, ∏ p ∈ S, ((k+1 : ℝ)*w p/(p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Nat.cast_prod]
      ring
    _ = _ := by rw [← Finset.prod_one_add]

noncomputable def ratioExcess (p : ℕ) : ℝ := ((p : ℝ)/((p : ℝ)-1))^2-1

lemma ratioExcess_bounds (p : ℕ) (hp : p.Prime) :
    0 ≤ ratioExcess p ∧ ratioExcess p ≤ 8/(p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm1 : 0 < (p : ℝ)-1 := by linarith
  have hge : (1 : ℝ) ≤ (p : ℝ)/((p : ℝ)-1) := (one_le_div hpm1).mpr (by linarith)
  refine ⟨by dsimp [ratioExcess]; nlinarith, ?_⟩
  have he : ratioExcess p = (2*(p : ℝ)-1)/((p : ℝ)-1)^2 := by
    dsimp [ratioExcess]
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpm1) hp0).mpr
  nlinarith [sq_nonneg ((p : ℝ)-2)]

lemma harmonicMoment_totient_ratio_le_product (k A : ℕ) :
    (∑ n ∈ Finset.Icc 1 A, (tau (k+1) n : ℝ) *
      ((n : ℝ)/n.totient)^2 / (n : ℝ)) ≤
        harmonicMoment (k+1) A *
          ∏ p ∈ (A+1).primesBelow, (1+8*(k+1 : ℝ)*((p : ℝ)^2)⁻¹) := by
  have havg := harmonicMoment_prime_product_le k A ratioExcess
    (fun p hp => (ratioExcess_bounds p (Nat.mem_primesBelow.mp hp).2).1)
  have he (n : ℕ) (hn : n ∈ Finset.Icc 1 A) :
      ((n : ℝ)/n.totient)^2 = ∏ p ∈ n.primeFactors, (1+ratioExcess p) := by
    rw [Sieve.totient_ratio_eq_prime_product n (Finset.mem_Icc.mp hn).1, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [ratioExcess]
    ring
  calc
    _ = ∑ n ∈ Finset.Icc 1 A, (tau (k+1) n : ℝ) *
        (∏ p ∈ n.primeFactors, (1+ratioExcess p)) / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [he n hn]
    _ ≤ harmonicMoment (k+1) A *
        ∏ p ∈ (A+1).primesBelow, (1+(k+1 : ℝ)*ratioExcess p/(p : ℝ)) := havg
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (harmonicMoment_nonneg _ _)
      apply Finset.prod_le_prod
      · intro p hp
        have h := (ratioExcess_bounds p (Nat.mem_primesBelow.mp hp).2).1
        positivity
      · intro p hp
        have h := (ratioExcess_bounds p (Nat.mem_primesBelow.mp hp).2).2
        have hd := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ k+1)) (Nat.cast_nonneg p)
        convert _root_.add_le_add_left hd 1 using 1 <;> ring

end Erdos821.HigherDivisors
