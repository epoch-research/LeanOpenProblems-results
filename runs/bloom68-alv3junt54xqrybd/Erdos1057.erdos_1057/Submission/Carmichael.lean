import FormalConjecturesUtil

/-!
# The unit-exponent and Carmichael-function criteria for Carmichael numbers

These are unconditional equivalences for every natural number, including `0` and `1`.
They are elementary structural lemmas, not a proof of a Carmichael counting conjecture.
No declarations from `Submission.Spec` are imported.
-/

namespace Erdos1057

namespace CarmichaelLambdaCriterion

/-- For a positive base, the probable-prime condition is the corresponding power
identity in `ZMod n`. Positivity is essential because `Nat.ProbablePrime` uses
truncated natural-number subtraction. -/
theorem probablePrime_iff_zmod_pow_eq_one (n : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    n.ProbablePrime b ↔ (b : ZMod n) ^ (n - 1) = 1 := by
  rw [Nat.probablePrime_iff_modEq n hb,
    ← ZMod.natCast_eq_natCast_iff (b ^ (n - 1)) 1 n]
  simp only [Nat.cast_pow, Nat.cast_one]

/-- A natural number is Carmichael exactly when it is composite and the exponent
of the unit group of `ZMod n` divides `n - 1`. -/
theorem isCarmichael_iff_composite_exponent_dvd (n : ℕ) :
    IsCarmichael n ↔ n.Composite ∧ Monoid.exponent (ZMod n)ˣ ∣ n - 1 := by
  constructor
  · intro h
    have hOne : n.FermatPsp 1 := h 1 (by omega) (Nat.coprime_one_right n)
    have hcomp : n.Composite := ⟨hOne.2.2, hOne.2.1⟩
    haveI : NeZero n := ⟨by have := hcomp.1; omega⟩
    refine ⟨hcomp, Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
    intro u
    -- Adding the modulus gives a positive representative even if the residue is zero.
    let b : ℕ := (u : ZMod n).val + n
    have hb : 1 ≤ b := by
      dsimp [b]
      have := hcomp.1
      omega
    have hcoprime : n.Coprime b := by
      dsimp [b]
      exact Nat.coprime_add_self_right.mpr (ZMod.val_coe_unit_coprime u).symm
    have hpow : (b : ZMod n) ^ (n - 1) = 1 :=
      (probablePrime_iff_zmod_pow_eq_one n hb).mp (h b hb hcoprime).1
    have hrepr : (b : ZMod n) = (u : ZMod n) := by
      simp [b]
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, hrepr] using hpow
  · rintro ⟨hcomp, hexponent⟩ b hb hcoprime
    refine ⟨(probablePrime_iff_zmod_pow_eq_one n hb).mpr ?_, hcomp.2, hcomp.1⟩
    have hunit := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexponent
      (ZMod.unitOfCoprime b hcoprime.symm)
    have hval := congrArg (fun u : (ZMod n)ˣ => (u : ZMod n)) hunit
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime] using hval

/-- The standard unconditional Carmichael-function criterion. -/
theorem isCarmichael_iff_composite_carmichael_dvd (n : ℕ) :
    IsCarmichael n ↔ n.Composite ∧ ArithmeticFunction.Carmichael n ∣ n - 1 := by
  rw [isCarmichael_iff_composite_exponent_dvd n]
  by_cases hn : n = 0
  · subst n
    simp [Nat.Composite]
  · rw [ArithmeticFunction.carmichael_eq_exponent hn]

end CarmichaelLambdaCriterion


/-
# Korselt's criterion

For every natural number `n`, the Carmichael property is equivalent to
compositeness, squarefreeness, and `p - 1 ∣ n - 1` for every prime divisor `p`.
We also deduce that every Carmichael number is odd.
-/

namespace CarmichaelKorselt

/-- The Carmichael function of a prime is one less than that prime. -/
theorem carmichael_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.Carmichael p = p - 1 := by
  by_cases hp₂ : p = 2
  · subst p
    simpa using ArithmeticFunction.carmichael_two_pow_of_le_two (n := 1) (by decide)
  · simpa only [pow_one, Nat.totient_prime hp] using
      ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp hp₂

/-- Every prime divides the Carmichael function of its square, including `p = 2`. -/
theorem prime_dvd_carmichael_prime_sq {p : ℕ} (hp : p.Prime) :
    p ∣ ArithmeticFunction.Carmichael (p ^ 2) := by
  by_cases hp₂ : p = 2
  · subst p
    rw [ArithmeticFunction.carmichael_two_pow_of_le_two (by decide)]
    norm_num
  · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two 2 hp hp₂,
      Nat.totient_prime_pow hp (by decide)]
    simpa only [Nat.reduceSub, pow_one] using dvd_mul_right p (p - 1)

/-- For nonzero `n`, `λ(n) ∣ n - 1` forces squarefreeness. -/
theorem squarefree_of_carmichael_dvd {n : ℕ} (hn : n ≠ 0)
    (hLambda : ArithmeticFunction.Carmichael n ∣ n - 1) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hpp
  have hpn : p ∣ n := (dvd_mul_right p p).trans hpp
  have hpLambda : p ∣ ArithmeticFunction.Carmichael n :=
    (prime_dvd_carmichael_prime_sq hp).trans
      (ArithmeticFunction.carmichael_dvd (by simpa only [pow_two] using hpp))
  have hpred : p ∣ n - 1 := hpLambda.trans hLambda
  have hcoprime : n.Coprime (n - 1) :=
    (Nat.coprime_self_sub_right (Nat.one_le_iff_ne_zero.mpr hn)).mpr
      (Nat.coprime_one_right n)
  exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcoprime hpn hpred)

/-- On a squarefree natural number, `λ(n)` is the lcm of `p - 1` over its prime factors. -/
theorem carmichael_eq_lcm_primeFactors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ArithmeticFunction.Carmichael n = n.primeFactors.lcm (fun p => p - 1) := by
  classical
  haveI : NeZero n := ⟨hn.ne_zero⟩
  rw [ArithmeticFunction.carmichael_factorization n]
  apply Finset.lcm_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpDvd := Nat.dvd_of_mem_primeFactors hp
  rw [Nat.factorization_eq_one_of_squarefree hn hpPrime hpDvd, pow_one,
    carmichael_prime hpPrime]

/-- Divisibility by `λ(n)` for squarefree `n` is tested on the numbers `p - 1`. -/
theorem carmichael_dvd_iff_prime_sub_one_dvd_of_squarefree {n m : ℕ}
    (hn : Squarefree n) :
    ArithmeticFunction.Carmichael n ∣ m ↔
      ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ m := by
  constructor
  · intro hLambda p hp hpn
    rw [← carmichael_prime hp]
    exact (ArithmeticFunction.carmichael_dvd hpn).trans hLambda
  · intro h
    rw [carmichael_eq_lcm_primeFactors_of_squarefree hn]
    apply Finset.lcm_dvd
    intro p hp
    exact h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- Korselt's criterion, without any positivity assumption on `n`. -/
theorem isCarmichael_iff_korselt (n : ℕ) :
    IsCarmichael n ↔ n.Composite ∧ Squarefree n ∧
      ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
  rw [CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n]
  constructor
  · rintro ⟨hcomp, hLambda⟩
    have hn : n ≠ 0 := by
      have := hcomp.1
      omega
    have hsq := squarefree_of_carmichael_dvd hn hLambda
    exact ⟨hcomp, hsq, (carmichael_dvd_iff_prime_sub_one_dvd_of_squarefree hsq).mp hLambda⟩
  · rintro ⟨hcomp, hsq, hprime⟩
    exact ⟨hcomp, (carmichael_dvd_iff_prime_sub_one_dvd_of_squarefree hsq).mpr hprime⟩

/-- Every Carmichael number is odd. -/
theorem isCarmichael_odd {n : ℕ} (hn : IsCarmichael n) : Odd n := by
  obtain ⟨hcomp, hsq, hdiv⟩ := (isCarmichael_iff_korselt n).mp hn
  have hnTwo : n ≠ 2 := by
    rintro rfl
    exact hcomp.2 Nat.prime_two
  have hTwo : 2 < n := by
    have := hcomp.1
    omega
  obtain hFour | ⟨p, hp, hpn, hodd⟩ :=
    Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hTwo
  · exact False.elim ((Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two
      (by simpa using hFour))
  · have hpTwo : p ≠ 2 := by
      rintro rfl
      norm_num at hodd
    have hEven : 2 ∣ n - 1 := (hp.even_sub_one hpTwo).two_dvd.trans (hdiv p hp hpn)
    rw [Nat.dvd_iff_mod_eq_zero] at hEven
    apply Nat.odd_iff.mpr
    omega

end CarmichaelKorselt


namespace CarmichaelKorselt

/-- A finite prime-factor version of Korselt's criterion. -/
theorem isCarmichael_iff_primeFactors (n : ℕ) :
    IsCarmichael n ↔ n.Composite ∧ Squarefree n ∧
      ∀ p ∈ n.primeFactors, p - 1 ∣ n - 1 := by
  rw [isCarmichael_iff_korselt n]
  constructor
  · rintro ⟨hcomp, hsq, hprime⟩
    exact ⟨hcomp, hsq, fun p hp => hprime p
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)⟩
  · rintro ⟨hcomp, hsq, hprime⟩
    refine ⟨hcomp, hsq, ?_⟩
    intro p hp hpn
    exact hprime p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hsq.ne_zero⟩)

/-- The smallest standard example establishes eventual positivity of the count. -/
theorem isCarmichael_561 : IsCarmichael 561 := by
  apply (isCarmichael_iff_korselt 561).mpr
  refine ⟨by norm_num [Nat.Composite], ?_, ?_⟩
  · rw [Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)]
    norm_num [Nat.primeFactorsList]
  · intro p hp hpn
    have hd : p ∣ 3 * (11 * 17) := by simpa using hpn
    rcases hp.dvd_mul.mp hd with hThree | hRest
    · have heq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hThree
      subst p
      norm_num
    · rcases hp.dvd_mul.mp hRest with hEleven | hSeventeen
      · have heq : p = 11 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hEleven
        subst p
        norm_num
      · have heq : p = 17 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hSeventeen
        subst p
        norm_num

end CarmichaelKorselt

end Erdos1057
