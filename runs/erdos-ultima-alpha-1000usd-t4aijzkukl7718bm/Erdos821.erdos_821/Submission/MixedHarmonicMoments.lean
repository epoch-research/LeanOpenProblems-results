import Submission.HyperbolicCompositeGain

/-!
# Harmonic divisor weights with one excluded coordinate

These integer moments provide the denominator for a sieve with one root
at primes dividing the coefficient, and two roots at the other primes.
-/

open Nat Finset Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta
namespace Erdos821.HigherDivisors
set_option maxHeartbeats 3000000

noncomputable def avoidingZeta (P : Finset ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => if ∀ p ∈ P, ¬p ∣ n then ζ n else 0, by simp⟩

lemma avoidingZeta_multiplicative (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (avoidingZeta P).IsMultiplicative := by
  constructor
  · have h : ∀ p ∈ P, ¬p ∣ 1 := fun p hp => (hP p hp).not_dvd_one
    simp only [avoidingZeta, coe_mk, if_pos h, zeta_apply_ne (by decide : (1 : ℕ) ≠ 0)]
  · intro m n hcop
    by_cases hm : m = 0
    · subst m; simp
    by_cases hn : n = 0
    · subst n; simp
    have hmul : (∀ p ∈ P, ¬p ∣ m*n) ↔
        (∀ p ∈ P, ¬p ∣ m) ∧ (∀ p ∈ P, ¬p ∣ n) := by
      constructor
      · intro hh
        exact ⟨fun p hp hpm => hh p hp (dvd_mul_of_dvd_left hpm n),
          fun p hp hpn => hh p hp (dvd_mul_of_dvd_right hpn m)⟩
      · rintro ⟨hmP,hnP⟩ p hp hpmn
        rcases (hP p hp).dvd_mul.mp hpmn with hpm | hpn
        · exact hmP p hp hpm
        · exact hnP p hp hpn
    simp only [avoidingZeta, coe_mk, hmul, zeta_apply_ne hm,
      zeta_apply_ne hn, zeta_apply_ne (Nat.mul_ne_zero hm hn)]
    split_ifs <;> simp_all

lemma avoidingZeta_prime_pow (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (p e : ℕ) (hp : p.Prime) :
    avoidingZeta P (p^e) = if p ∈ P then (if e = 0 then 1 else 0) else 1 := by
  by_cases hpP : p ∈ P
  · rw [if_pos hpP]
    by_cases he : e = 0
    · subst e
      simp only [pow_zero]
      exact (avoidingZeta_multiplicative P hP).map_one
    · have hh : ¬∀ q ∈ P, ¬q ∣ p^e := fun h => h p hpP (dvd_pow_self p he)
      simp only [avoidingZeta, coe_mk, if_neg hh, if_neg he]
  · have hh : ∀ q ∈ P, ¬q ∣ p^e := by
      intro q hq hqd
      exact hpP ((Nat.prime_eq_prime_of_dvd_pow (hP q hq) hp hqd) ▸ hq)
    simp only [avoidingZeta, coe_mk, if_neg hpP, if_pos hh, zeta_apply_ne (pow_ne_zero _ hp.ne_zero)]

noncomputable def mixedDivisorWeight (P : Finset ℕ) : ArithmeticFunction ℕ :=
  ζ * avoidingZeta P

lemma mixedDivisorWeight_multiplicative (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (mixedDivisorWeight P).IsMultiplicative :=
  isMultiplicative_zeta.mul (avoidingZeta_multiplicative P hP)

lemma mixedDivisorWeight_prime_pow (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (p e : ℕ) (hp : p.Prime) :
    mixedDivisorWeight P (p^e) = if p ∈ P then 1 else e+1 := by
  rw [mixedDivisorWeight, zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [avoidingZeta_prime_pow P hP p _ hp]
  by_cases hpP : p ∈ P
  · simp [hpP]
  · simp [hpP]

noncomputable def mixedHarmonicMoment (P : Finset ℕ) (z : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 z, (mixedDivisorWeight P n : ℝ)/(n : ℝ)

lemma mixedHarmonicMoment_convolution (P : Finset ℕ) (z : ℕ) :
    mixedHarmonicMoment P z = ∑ m ∈ Icc 1 z, avoidingHarmonicMoment 1 (z/m) P/(m : ℝ) := by
  unfold mixedHarmonicMoment
  simp only [mixedDivisorWeight, ← natCoe_apply (R := ℝ), natCoe_mul,
    div_eq_mul_inv]
  rw [AnalyticSieve.sum_convolution_weighted _ _ _ (le_refl z)]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  have hset : (Icc 1 z).filter (fun n => m*n ≤ z) = Icc 1 (z/m) := by
    ext n
    simp only [mem_filter, mem_Icc]
    have hd := Nat.div_le_self z m
    have he : m*n ≤ z ↔ n ≤ z/m := by rw [Nat.le_div_iff_mul_le hm0, mul_comm]
    rw [he]
    omega
  rw [← Finset.sum_filter, hset]
  unfold avoidingHarmonicMoment
  rw [Finset.sum_filter, Finset.sum_mul]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp only [zeta_apply_ne hm0.ne', natCoe_apply, avoidingZeta, coe_mk,
    Nat.cast_ite, Nat.cast_zero, tau, pow_one, Nat.cast_mul, mul_inv]
  by_cases hnP : ∀ p ∈ P, ¬p ∣ n
  · simp only [if_pos hnP, div_eq_mul_inv]
    ring
  · simp [hnP]

lemma mixedHarmonicMoment_euler_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℕ) :
    (∏ p ∈ P, (1-(p : ℝ)⁻¹))*harmonicMoment 2 z ≤ mixedHarmonicMoment P z := by
  rw [mixedHarmonicMoment_convolution, harmonicMoment_succ 1 z, Finset.mul_sum]
  apply sum_le_sum
  intro m hm
  have hh := avoidingHarmonicMoment_euler_lower 0 (z/m) P hP
  simp only [zero_add, pow_one] at hh
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg m)

lemma mixedHarmonicMoment_totient_lower (M z : ℕ) (hM : 0 < M) :
    ((M.totient : ℝ)/(M : ℝ))*harmonicMoment 2 z ≤ mixedHarmonicMoment M.primeFactors z := by
  have hphi : (M.totient : ℝ)/(M : ℝ) = ∏ p ∈ M.primeFactors, (1-(p : ℝ)⁻¹) := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors M)
    push_cast at hh
    rw [hh]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hM.ne')
  rw [hphi]
  exact mixedHarmonicMoment_euler_lower M.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) z


lemma sum_exact_prime_support_multiplicative_le
    (f : ArithmeticFunction ℕ) (hf : f.IsMultiplicative) (z : ℕ) (S A : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (hA : ∀ n ∈ A, 0 < n ∧ n ≤ z ∧ n.primeFactors = S)
    (b : ℕ → ℝ)
    (hb : ∀ p ∈ S, (∑ e ∈ Icc 1 z, (f (p^e) : ℝ)/(p : ℝ)^e) ≤ b p) :
    (∑ n ∈ A, (f n : ℝ)/(n : ℝ)) ≤
      ∏ p ∈ S, b p := by
  have hfact (n : ℕ) (hn : n ≠ 0) : f n = ∏ p ∈ n.primeFactors, f (p^(n.factorization p)) := by
    simpa only [Finsupp.prod, Nat.support_factorization] using hf.multiplicative_factorization f hn
  let F : ℕ → (S → ℕ) := fun n p => n.factorization p
  let B := Fintype.piFinset (fun _ : S => Icc 1 z)
  let w : (S → ℕ) → ℝ := fun e => ∏ p : S,
    (f ((p : ℕ)^(e p)) : ℝ)/((p : ℕ) : ℝ)^(e p)
  have hrec (n : ℕ) (hn : n ∈ A) : ∏ p : S, (p : ℕ)^((F n) p) = n := by
    dsimp only [F]
    rw [Finset.prod_coe_sort S (fun p : ℕ => p^(n.factorization p))]
    change (∏ p ∈ S, p^(n.factorization p)) = n
    rw [← (hA n hn).2.2]
    simpa only [Finsupp.prod, Nat.support_factorization] using
      Nat.factorization_prod_pow_eq_self (hA n hn).1.ne'
  have hinj : Set.InjOn F (A : Set ℕ) := by
    intro n hn m hm he
    rw [← hrec n hn, ← hrec m hm, he]
  have hmap : A.image F ⊆ B := by
    intro e he
    obtain ⟨n, hn, rfl⟩ := mem_image.mp he
    apply Fintype.mem_piFinset.mpr
    intro p
    have hp := hS p p.property
    have hpN : (p : ℕ) ∈ n.primeFactors := (hA n hn).2.2.symm ▸ p.property
    apply mem_Icc.mpr
    refine ⟨hp.factorization_pos_of_dvd (hA n hn).1.ne'
      (Nat.dvd_of_mem_primeFactors hpN), ?_⟩
    apply Nat.factorization_le_of_le_pow
    exact (hA n hn).2.1.trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_left hp.two_le z))
  have he (n : ℕ) (hn : n ∈ A) : (f n : ℝ)/(n : ℝ) = w (F n) := by
    dsimp only [w]
    rw [Finset.prod_div_distrib]
    have hden : (∏ p : S, ((p : ℕ) : ℝ)^((F n) p)) = (n : ℝ) := by
      exact_mod_cast hrec n hn
    rw [hden]
    congr 1
    dsimp only [F]
    rw [hfact n (hA n hn).1.ne', (hA n hn).2.2,
      Nat.cast_prod, Finset.prod_coe_sort S (fun p : ℕ => (f (p^(n.factorization p)) : ℝ))]
  calc
    _ = ∑ e ∈ A.image F, w e := by
      rw [sum_image hinj]
      exact sum_congr rfl he
    _ ≤ ∑ e ∈ B, w e := sum_le_sum_of_subset_of_nonneg hmap
      (fun e _ _ => by dsimp [w]; positivity)
    _ = ∏ p : S, ∑ e ∈ Icc 1 z,
        (f ((p : ℕ)^e) : ℝ)/((p : ℕ) : ℝ)^e := by
      exact Finset.sum_prod_piFinset (Icc 1 z)
        (fun (p : S) (e : ℕ) => (f ((p : ℕ)^e) : ℝ)/((p : ℕ) : ℝ)^e)
    _ ≤ ∏ p : S, b (p : ℕ) := by
      apply Finset.prod_le_prod
      · intro p _; positivity
      · intro p _
        exact hb p p.property
    _ = _ := Finset.prod_coe_sort S
      (fun p : ℕ => b p)


end Erdos821.HigherDivisors
