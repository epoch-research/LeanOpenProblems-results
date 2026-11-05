import Submission.Carmichael

/-!
# Elementary prime extensions of Carmichael numbers

For a Carmichael number `n` and a prime `p`, the product `n * p` is Carmichael
exactly when `p` does not divide `n`, `λ(n)` divides `p - 1`, and `p - 1`
divides `n - 1`. In that case `λ(n * p) = p - 1`, and `p` is strictly larger
than every prime divisor of `n`. The extension primes are also parametrized
by the positive divisors of `(n - 1) / λ(n)`. An exact two-prime completion
criterion is included without assuming either intermediate is Carmichael.

These are unconditional structural results, not a density or counting theorem.
Only `Submission.Carmichael` is imported; no admitted counting target is used.
-/

namespace Erdos1057.CarmichaelExtensions

/-- If `a` is one modulo `L`, adjoining a positive factor `b` reduces the
condition `L ∣ a * b - 1` to `L ∣ b - 1`. -/
private theorem dvd_mul_sub_one_iff {a b L : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hLa : L ∣ a - 1) : L ∣ a * b - 1 ↔ L ∣ b - 1 := by
  have heq : a * b - 1 = (a - 1) * b + (b - 1) := by
    calc
      a * b - 1 = ((a - 1 + 1) * b) - 1 := by rw [Nat.sub_add_cancel ha]
      _ = ((a - 1) * b + b) - 1 := by rw [add_mul, one_mul]
      _ = (a - 1) * b + (b - 1) := Nat.add_sub_assoc hb _
  rw [heq, ← Nat.dvd_add_iff_right (dvd_mul_of_dvd_left hLa b)]

/-- The Carmichael function is positive at every nonzero natural number,
since it is the exponent of a finite group. -/
theorem carmichael_pos {n : ℕ} (hn : n ≠ 0) :
    0 < ArithmeticFunction.Carmichael n := by
  haveI : NeZero n := ⟨hn⟩
  rw [ArithmeticFunction.carmichael_eq_exponent hn]
  exact Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite

/-- The coprime-product lcm formula simplifies whenever the old Carmichael
function divides the new prime minus one. -/
theorem carmichael_mul_prime_eq_of_dvd {n p : ℕ} (hp : p.Prime)
    (hpn : ¬ p ∣ n) (hL : ArithmeticFunction.Carmichael n ∣ p - 1) :
    ArithmeticFunction.Carmichael (n * p) = p - 1 := by
  rw [ArithmeticFunction.carmichael_mul (hp.coprime_iff_not_dvd.mpr hpn).symm,
    CarmichaelKorselt.carmichael_prime hp, Nat.lcm_eq_right hL]

/-- The exact unconditional criterion for adjoining one prime to a
Carmichael number. -/
theorem isCarmichael_mul_prime_iff {n p : ℕ} (hn : IsCarmichael n) (hp : p.Prime) :
    IsCarmichael (n * p) ↔ ¬ p ∣ n ∧
      ArithmeticFunction.Carmichael n ∣ p - 1 ∧ p - 1 ∣ n - 1 := by
  obtain ⟨hncomp, hnL⟩ :=
    (CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn
  have hn1 : 1 ≤ n := by have := hncomp.1; omega
  have hp1 : 1 ≤ p := by have := hp.two_le; omega
  constructor
  · intro hnp
    obtain ⟨hnpcomp, hnpL⟩ :=
      (CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd (n * p)).mp hnp
    have hsq := CarmichaelKorselt.squarefree_of_carmichael_dvd
      (by have := hnpcomp.1; omega) hnpL
    have hnot : ¬ p ∣ n := hp.coprime_iff_not_dvd.mp
      (Nat.coprime_of_squarefree_mul hsq).symm
    have hL : ArithmeticFunction.Carmichael n ∣ n * p - 1 :=
      (ArithmeticFunction.carmichael_dvd (dvd_mul_right n p)).trans hnpL
    have hpL : p - 1 ∣ n * p - 1 := by
      rw [← CarmichaelKorselt.carmichael_prime hp]
      exact (ArithmeticFunction.carmichael_dvd (dvd_mul_left p n)).trans hnpL
    refine ⟨hnot, (dvd_mul_sub_one_iff hn1 hp1 hnL).mp hL, ?_⟩
    apply (dvd_mul_sub_one_iff hp1 hn1 (dvd_refl (p - 1))).mp
    simpa only [mul_comm] using hpL
  · rintro ⟨hnot, hL, hpL⟩
    apply (CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd (n * p)).mpr
    refine ⟨⟨?_, Nat.not_prime_mul (by have := hncomp.1; omega) hp.ne_one⟩, ?_⟩
    · have := hncomp.1
      have := hp.two_le
      nlinarith
    · rw [carmichael_mul_prime_eq_of_dvd hp hnot hL]
      simpa only [mul_comm] using
        (dvd_mul_sub_one_iff hp1 hn1 (dvd_refl (p - 1))).mpr hpL

/-- A successful one-prime extension has Carmichael function exactly `p - 1`. -/
theorem carmichael_mul_prime_eq_sub_one {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hnp : IsCarmichael (n * p)) :
    ArithmeticFunction.Carmichael (n * p) = p - 1 := by
  obtain ⟨hnot, hL, _⟩ := (isCarmichael_mul_prime_iff hn hp).mp hnp
  exact carmichael_mul_prime_eq_of_dvd hp hnot hL

/-- Every old prime factor is strictly smaller than a successful extension prime. -/
theorem prime_dvd_lt_extension_prime {n p q : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hnp : IsCarmichael (n * p)) (hq : q.Prime) (hqn : q ∣ n) :
    q < p := by
  obtain ⟨hnot, hL, _⟩ := (isCarmichael_mul_prime_iff hn hp).mp hnp
  have hqL : q - 1 ∣ ArithmeticFunction.Carmichael n := by
    rw [← CarmichaelKorselt.carmichael_prime hq]
    exact ArithmeticFunction.carmichael_dvd hqn
  have hle : q - 1 ≤ p - 1 :=
    Nat.le_of_dvd (by have := hp.two_le; omega) (hqL.trans hL)
  have hne : q ≠ p := by
    rintro rfl
    exact hnot hqn
  have := hq.two_le
  have := hp.two_le
  omega

/-- The adjoined prime is the largest prime divisor of the extended number. -/
theorem extension_prime_isGreatest {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hnp : IsCarmichael (n * p)) :
    IsGreatest {q : ℕ | q.Prime ∧ q ∣ n * p} p := by
  refine ⟨⟨hp, dvd_mul_left p n⟩, ?_⟩
  rintro q ⟨hq, hqnp⟩
  rcases hq.dvd_mul.mp hqnp with hqn | hqp
  · exact (prime_dvd_lt_extension_prime hn hp hnp hq hqn).le
  · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).le

/-- The quotient indexing possible extensions is a positive natural number. -/
theorem carmichael_quotient_pos {n : ℕ} (hn : IsCarmichael n) :
    0 < (n - 1) / ArithmeticFunction.Carmichael n := by
  obtain ⟨hncomp, hnL⟩ :=
    (CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn
  have hn0 : n ≠ 0 := by have := hncomp.1; omega
  have hpred : 0 < n - 1 := by have := hncomp.1; omega
  exact Nat.div_pos (Nat.le_of_dvd hpred hnL) (carmichael_pos hn0)

/-- Exact positive-divisor parametrization of extension primes. The prime
hypothesis is retained: a divisor only gives an extension if `1 + λ(n) * d`
is prime and does not already divide `n`. -/
theorem isCarmichael_mul_prime_iff_parametrized {n p : ℕ}
    (hn : IsCarmichael n) (hp : p.Prime) :
    IsCarmichael (n * p) ↔ ¬ p ∣ n ∧ ∃ d : ℕ,
      0 < d ∧ d ∣ (n - 1) / ArithmeticFunction.Carmichael n ∧
        p = 1 + ArithmeticFunction.Carmichael n * d := by
  have hnL :=
    ((CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn).2
  constructor
  · intro hnp
    obtain ⟨hnot, hL, hpL⟩ := (isCarmichael_mul_prime_iff hn hp).mp hnp
    obtain ⟨d, hd⟩ := hL
    refine ⟨hnot, d, ?_, ?_, ?_⟩
    · have := hp.two_le
      by_contra hpos
      have hd0 : d = 0 := by omega
      simp only [hd0, mul_zero] at hd
      omega
    · apply (Nat.dvd_div_iff_mul_dvd hnL).mpr
      rwa [← hd]
    · have := hp.two_le
      omega
  · rintro ⟨hnot, d, _, hdK, hpd⟩
    apply (isCarmichael_mul_prime_iff hn hp).mpr
    have hd : p - 1 = ArithmeticFunction.Carmichael n * d := by omega
    refine ⟨hnot, ?_, ?_⟩
    · rw [hd]
      exact dvd_mul_right _ _
    · rw [hd]
      exact (Nat.dvd_div_iff_mul_dvd hnL).mp hdK

/-- Exact two-prime completion of a Carmichael seed. Neither intermediate
`n * p` nor `n * q` is assumed to be Carmichael. -/
theorem isCarmichael_mul_two_primes_iff {n p q : ℕ}
    (hn : IsCarmichael n) (hp : p.Prime) (hq : q.Prime) :
    IsCarmichael (n * p * q) ↔ ¬ p ∣ n ∧ ¬ q ∣ n ∧ p ≠ q ∧
      ArithmeticFunction.Carmichael n ∣ p * q - 1 ∧
      p - 1 ∣ n * q - 1 ∧ q - 1 ∣ n * p - 1 := by
  obtain ⟨hncomp, hnL⟩ :=
    (CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn
  have hn0 : n ≠ 0 := by have := hncomp.1; omega
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp.ne_zero
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq.ne_zero
  have hnp1 : 1 ≤ n * p := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hn0 hp.ne_zero)
  have hnq1 : 1 ≤ n * q := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hn0 hq.ne_zero)
  have hpq1 : 1 ≤ p * q := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero hq.ne_zero)
  constructor
  · intro hnpq
    obtain ⟨hnpqcomp, hnpqL⟩ :=
      (CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd
        (n * p * q)).mp hnpq
    have hsq := CarmichaelKorselt.squarefree_of_carmichael_dvd
      (by have := hnpqcomp.1; omega) hnpqL
    have hnotp : ¬ p ∣ n := hp.coprime_iff_not_dvd.mp
      (Nat.coprime_of_squarefree_mul hsq.of_mul_left).symm
    have hnotqnp : ¬ q ∣ n * p := hq.coprime_iff_not_dvd.mp
      (Nat.coprime_of_squarefree_mul hsq).symm
    have hnotq : ¬ q ∣ n := fun hqn => hnotqnp (dvd_mul_of_dvd_left hqn p)
    have hne : p ≠ q := by
      rintro rfl
      exact hnotqnp (dvd_mul_left p n)
    have hL : ArithmeticFunction.Carmichael n ∣ n * p * q - 1 :=
      (ArithmeticFunction.carmichael_dvd
        ((dvd_mul_right n p).trans (dvd_mul_right (n * p) q))).trans hnpqL
    have hpL : p - 1 ∣ n * p * q - 1 := by
      rw [← CarmichaelKorselt.carmichael_prime hp]
      exact (ArithmeticFunction.carmichael_dvd
        ((dvd_mul_left p n).trans (dvd_mul_right (n * p) q))).trans hnpqL
    have hqL : q - 1 ∣ n * p * q - 1 := by
      rw [← CarmichaelKorselt.carmichael_prime hq]
      exact (ArithmeticFunction.carmichael_dvd (dvd_mul_left q (n * p))).trans hnpqL
    refine ⟨hnotp, hnotq, hne, ?_, ?_, ?_⟩
    · apply (dvd_mul_sub_one_iff hn1 hpq1 hnL).mp
      simpa only [mul_assoc] using hL
    · apply (dvd_mul_sub_one_iff hp1 hnq1 (dvd_refl (p - 1))).mp
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hpL
    · apply (dvd_mul_sub_one_iff hq1 hnp1 (dvd_refl (q - 1))).mp
      simpa only [mul_comm] using hqL
  · rintro ⟨hnotp, hnotq, hne, hL, hpL, hqL⟩
    have hcopnp : n.Coprime p := (hp.coprime_iff_not_dvd.mpr hnotp).symm
    have hcopnq : n.Coprime q := (hq.coprime_iff_not_dvd.mpr hnotq).symm
    have hcoppq : p.Coprime q := (Nat.coprime_primes hp hq).mpr hne
    have hLambda : ArithmeticFunction.Carmichael (n * p * q) =
        Nat.lcm (Nat.lcm (ArithmeticFunction.Carmichael n) (p - 1)) (q - 1) := by
      rw [ArithmeticFunction.carmichael_mul (hcopnq.mul_left hcoppq),
        ArithmeticFunction.carmichael_mul hcopnp,
        CarmichaelKorselt.carmichael_prime hp, CarmichaelKorselt.carmichael_prime hq]
    apply (CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd
      (n * p * q)).mpr
    have hnpTwo : 1 < n * p := by
      have := hncomp.1
      have := hp.two_le
      nlinarith
    refine ⟨⟨?_, Nat.not_prime_mul (by omega) hq.ne_one⟩, ?_⟩
    · have hle : n * p ≤ n * p * q := by
        simpa only [mul_one] using Nat.mul_le_mul_left (n * p) hq1
      exact hnpTwo.trans_le hle
    · rw [hLambda]
      apply Nat.lcm_dvd (Nat.lcm_dvd ?_ ?_) ?_
      · simpa only [mul_assoc] using (dvd_mul_sub_one_iff hn1 hpq1 hnL).mpr hL
      · simpa only [mul_assoc, mul_comm, mul_left_comm] using
          (dvd_mul_sub_one_iff hp1 hnq1 (dvd_refl (p - 1))).mpr hpL
      · simpa only [mul_comm] using
          (dvd_mul_sub_one_iff hq1 hnp1 (dvd_refl (q - 1))).mpr hqL

end Erdos1057.CarmichaelExtensions
