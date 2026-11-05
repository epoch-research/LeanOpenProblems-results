import Submission.Carmichael
import Submission.Extensions

/-!
# Elementary divisor certificates for Carmichael numbers

A divisor `d` of a Carmichael number `n` is positive, and its Carmichael
function `λ(d)` divides `n - 1` and is coprime to `d`. Consequently the
cofactor `n / d` is an inverse of `d` modulo `λ(d)`. Cofactors of two
Carmichael multiples of the same `d` are congruent modulo `λ(d)`, so
unequal cofactors are separated by at least `λ(d)`.

For a prime factor `p`, the cofactor is greater than one and is one
modulo `p - 1`. The canonical positive index `j = (n / p - 1) / (p - 1)`
reconstructs `n = p * (1 + j * (p - 1))`. Injecting into the positive
indices gives the finite bound `#{n ≤ X : IsCarmichael n ∧ p ∣ n} ≤
X / (p * (p - 1))`.

These are unconditional arithmetic certificates, not an asymptotic density
proof. Only the Carmichael core and extension modules are imported; no
counting or density target is used.
-/

namespace Erdos1057.CarmichaelCertificates

/-- Every divisor of a Carmichael number is positive. -/
theorem divisor_pos {n d : ℕ} (hn : IsCarmichael n) (hd : d ∣ n) : 0 < d := by
  have hcomp :=
    ((CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn).1
  exact Nat.pos_of_dvd_of_pos hd (by have := hcomp.1; omega)

/-- The Carmichael function of a divisor of a Carmichael number is positive. -/
theorem carmichael_divisor_pos {n d : ℕ} (hn : IsCarmichael n) (hd : d ∣ n) :
    0 < ArithmeticFunction.Carmichael d :=
  CarmichaelExtensions.carmichael_pos (Nat.ne_of_gt (divisor_pos hn hd))

/-- Divisor monotonicity of `λ` gives the elementary divisor certificate. -/
theorem carmichael_divisor_dvd_sub_one {n d : ℕ}
    (hn : IsCarmichael n) (hd : d ∣ n) :
    ArithmeticFunction.Carmichael d ∣ n - 1 := by
  exact (ArithmeticFunction.carmichael_dvd hd).trans
    ((CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn).2

/-- Since `d ∣ n` and `λ(d) ∣ n - 1`, these two numbers are coprime. -/
theorem divisor_coprime_carmichael {n d : ℕ}
    (hn : IsCarmichael n) (hd : d ∣ n) :
    d.Coprime (ArithmeticFunction.Carmichael d) := by
  have hcomp :=
    ((CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn).1
  have hconsecutive : n.Coprime (n - 1) :=
    (Nat.coprime_self_sub_right (by have := hcomp.1; omega)).mpr
      (Nat.coprime_one_right n)
  exact (hconsecutive.of_dvd_left hd).of_dvd_right
    (carmichael_divisor_dvd_sub_one hn hd)

/-- The same coprimality certificate in gcd form. -/
theorem divisor_gcd_carmichael_eq_one {n d : ℕ}
    (hn : IsCarmichael n) (hd : d ∣ n) :
    Nat.gcd d (ArithmeticFunction.Carmichael d) = 1 :=
  Nat.coprime_iff_gcd_eq_one.mp (divisor_coprime_carmichael hn hd)

/-- A Carmichael number is one modulo the Carmichael function of any divisor. -/
theorem divisor_modEq_one {n d : ℕ} (hn : IsCarmichael n) (hd : d ∣ n) :
    Nat.ModEq (ArithmeticFunction.Carmichael d) n 1 := by
  have hcomp :=
    ((CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn).1
  exact ((Nat.modEq_iff_dvd' (by have := hcomp.1; omega)).mpr
    (carmichael_divisor_dvd_sub_one hn hd)).symm

/-- The exact divisibility certificate after splitting off `d`. -/
theorem carmichael_divisor_dvd_mul_cofactor_sub_one {n d : ℕ}
    (hn : IsCarmichael n) (hd : d ∣ n) :
    ArithmeticFunction.Carmichael d ∣ d * (n / d) - 1 := by
  rw [Nat.mul_div_cancel' hd]
  exact carmichael_divisor_dvd_sub_one hn hd

/-- The cofactor is an inverse of `d` modulo `λ(d)`. -/
theorem divisor_mul_cofactor_modEq_one {n d : ℕ}
    (hn : IsCarmichael n) (hd : d ∣ n) :
    Nat.ModEq (ArithmeticFunction.Carmichael d) (d * (n / d)) 1 := by
  rw [Nat.mul_div_cancel' hd]
  exact divisor_modEq_one hn hd

/-- A bundled version of the elementary divisor certificates. -/
theorem divisor_certificate {n d : ℕ} (hn : IsCarmichael n) (hd : d ∣ n) :
    0 < d ∧ ArithmeticFunction.Carmichael d ∣ n - 1 ∧
      Nat.gcd d (ArithmeticFunction.Carmichael d) = 1 ∧
      ArithmeticFunction.Carmichael d ∣ d * (n / d) - 1 ∧
      Nat.ModEq (ArithmeticFunction.Carmichael d) (d * (n / d)) 1 :=
  ⟨divisor_pos hn hd, carmichael_divisor_dvd_sub_one hn hd,
    divisor_gcd_carmichael_eq_one hn hd,
    carmichael_divisor_dvd_mul_cofactor_sub_one hn hd,
    divisor_mul_cofactor_modEq_one hn hd⟩

/-- The inverse certificate expressed using the canonical unit in `ZMod (λ(d))`. -/
theorem cofactor_zmod_eq_unit_inv {n d : ℕ} (hn : IsCarmichael n) (hd : d ∣ n) :
    (n / d : ZMod (ArithmeticFunction.Carmichael d)) =
      ↑((ZMod.unitOfCoprime d (divisor_coprime_carmichael hn hd))⁻¹) := by
  apply Units.mul_eq_one_iff_eq_inv.mp
  simpa only [ZMod.coe_unitOfCoprime, Nat.cast_mul, Nat.cast_one, mul_comm] using
    (ZMod.natCast_eq_natCast_iff (d * (n / d)) 1
      (ArithmeticFunction.Carmichael d)).mpr (divisor_mul_cofactor_modEq_one hn hd)

/-- Cofactors obtained by division by a common divisor are congruent. -/
theorem cofactor_modEq {n₁ n₂ d : ℕ} (h₁ : IsCarmichael n₁) (h₂ : IsCarmichael n₂)
    (hd₁ : d ∣ n₁) (hd₂ : d ∣ n₂) :
    Nat.ModEq (ArithmeticFunction.Carmichael d) (n₁ / d) (n₂ / d) := by
  exact Nat.ModEq.cancel_left_of_coprime (divisor_coprime_carmichael h₁ hd₁).symm
    ((divisor_mul_cofactor_modEq_one h₁ hd₁).trans
      (divisor_mul_cofactor_modEq_one h₂ hd₂).symm)

/-- Two Carmichael multiples of `d` have the same cofactor residue modulo `λ(d)`. -/
theorem cofactors_modEq {d m₁ m₂ : ℕ}
    (h₁ : IsCarmichael (d * m₁)) (h₂ : IsCarmichael (d * m₂)) :
    Nat.ModEq (ArithmeticFunction.Carmichael d) m₁ m₂ := by
  exact Nat.ModEq.cancel_left_of_coprime
    (divisor_coprime_carmichael h₁ (dvd_mul_right d m₁)).symm
    ((divisor_modEq_one h₁ (dvd_mul_right d m₁)).trans
      (divisor_modEq_one h₂ (dvd_mul_right d m₂)).symm)

/-- A version with explicit factorizations of two Carmichael numbers. -/
theorem cofactors_modEq_of_eq_mul {n₁ n₂ d m₁ m₂ : ℕ}
    (h₁ : IsCarmichael n₁) (h₂ : IsCarmichael n₂)
    (heq₁ : n₁ = d * m₁) (heq₂ : n₂ = d * m₂) :
    Nat.ModEq (ArithmeticFunction.Carmichael d) m₁ m₂ :=
  cofactors_modEq (heq₁ ▸ h₁) (heq₂ ▸ h₂)

/-- Distinct congruent natural numbers differ by at least the modulus.
The difference is taken in `ℤ` to avoid truncated subtraction. -/
theorem modEq_natAbs_sub_ge {L a b : ℕ} (h : Nat.ModEq L a b) (hne : a ≠ b) :
    L ≤ ((a : ℤ) - b).natAbs := by
  have hdiff : (a : ℤ) - b ≠ 0 := by
    intro heq
    exact hne (Int.ofNat.inj (sub_eq_zero.mp heq))
  simpa only [Int.natAbs_natCast] using
    Int.natAbs_le_of_dvd_ne_zero h.symm.dvd hdiff

/-- Unequal cofactors of Carmichael multiples are separated by at least `λ(d)`.
No upper bound on the cofactors is needed for this stronger statement. -/
theorem cofactors_natAbs_sub_ge {d m₁ m₂ : ℕ}
    (h₁ : IsCarmichael (d * m₁)) (h₂ : IsCarmichael (d * m₂)) (hne : m₁ ≠ m₂) :
    ArithmeticFunction.Carmichael d ≤ ((m₁ : ℤ) - m₂).natAbs :=
  modEq_natAbs_sub_ge (cofactors_modEq h₁ h₂) hne

/-- The separation certificate with the usual integer absolute value. -/
theorem cofactors_abs_sub_ge {d m₁ m₂ : ℕ}
    (h₁ : IsCarmichael (d * m₁)) (h₂ : IsCarmichael (d * m₂)) (hne : m₁ ≠ m₂) :
    (ArithmeticFunction.Carmichael d : ℤ) ≤ |(m₁ : ℤ) - m₂| := by
  have h : (ArithmeticFunction.Carmichael d : ℤ) ≤
      (((m₁ : ℤ) - m₂).natAbs : ℤ) := by
    exact_mod_cast cofactors_natAbs_sub_ge h₁ h₂ hne
  simpa only [Int.natCast_natAbs] using h

/-- Distinct cofactors in `[0, M]` force `λ(d) ≤ M`. -/
theorem carmichael_le_bound_of_distinct_cofactors {d m₁ m₂ M : ℕ}
    (h₁ : IsCarmichael (d * m₁)) (h₂ : IsCarmichael (d * m₂))
    (hm₁ : m₁ ≤ M) (hm₂ : m₂ ≤ M) (hne : m₁ ≠ m₂) :
    ArithmeticFunction.Carmichael d ≤ M :=
  (cofactors_natAbs_sub_ge h₁ h₂ hne).trans
    (Int.natAbs_coe_sub_coe_le_of_le hm₁ hm₂)

/-- Below `λ(d)` there can be at most one cofactor of a Carmichael multiple of `d`. -/
theorem cofactors_eq_of_bound_lt {d m₁ m₂ M : ℕ}
    (h₁ : IsCarmichael (d * m₁)) (h₂ : IsCarmichael (d * m₂))
    (hm₁ : m₁ ≤ M) (hm₂ : m₂ ≤ M) (hM : M < ArithmeticFunction.Carmichael d) :
    m₁ = m₂ := by
  by_contra hne
  exact (Nat.not_le_of_gt hM)
    (carmichael_le_bound_of_distinct_cofactors h₁ h₂ hm₁ hm₂ hne)

/-- The cofactor of a prime factor of a Carmichael number is greater than one.
A cofactor of one would make the Carmichael number itself prime. -/
theorem prime_cofactor_one_lt {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) : 1 < n / p := by
  have hcomp :=
    ((CarmichaelLambdaCriterion.isCarmichael_iff_composite_carmichael_dvd n).mp hn).1
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
  have hzero : n / p ≠ 0 := by
    intro hq
    rw [hq, mul_zero] at hmul
    have := hcomp.1
    omega
  have hone : n / p ≠ 1 := by
    intro hq
    have hnp : n = p := by simpa only [hq, mul_one] using hmul.symm
    exact hcomp.2 (by simpa only [hnp] using hp)
  exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hzero) hone.symm

/-- Removing a prime factor leaves a cofactor that is one modulo `p - 1`. -/
theorem prime_cofactor_modEq_one {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) : Nat.ModEq (p - 1) (n / p) 1 := by
  have hpMod : Nat.ModEq (p - 1) p 1 :=
    Nat.modEq_sub (by have := hp.two_le; omega)
  have hprod : Nat.ModEq (p - 1) (p * (n / p)) 1 := by
    simpa only [CarmichaelKorselt.carmichael_prime hp] using
      divisor_mul_cofactor_modEq_one hn hpn
  simpa only [one_mul] using (hpMod.mul_right (n / p)).symm.trans hprod

/-- The prime-factor cofactor divisibility criterion. -/
theorem prime_sub_one_dvd_cofactor_sub_one {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) : p - 1 ∣ n / p - 1 :=
  (Nat.modEq_iff_dvd' (prime_cofactor_one_lt hn hp hpn).le).mp
    (prime_cofactor_modEq_one hn hp hpn).symm

/-- The canonical progression index for a number with prime factor `p`.
For Carmichael numbers divisible by `p`, this index is strictly positive. -/
def primeCofactorIndex (p n : ℕ) : ℕ := (n / p - 1) / (p - 1)

/-- The canonical index is positive and reconstructs the Carmichael number exactly. -/
theorem prime_cofactor_index_spec {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) :
    1 ≤ primeCofactorIndex p n ∧
      n = p * (1 + primeCofactorIndex p n * (p - 1)) := by
  have hq : 1 < n / p := prime_cofactor_one_lt hn hp hpn
  have hdiv : p - 1 ∣ n / p - 1 := prime_sub_one_dvd_cofactor_sub_one hn hp hpn
  have hpos : 0 < primeCofactorIndex p n := by
    apply Nat.div_pos (Nat.le_of_dvd (by omega) hdiv)
    have := hp.two_le
    omega
  have hmul : primeCofactorIndex p n * (p - 1) = n / p - 1 :=
    Nat.div_mul_cancel hdiv
  have hrepr : n / p = 1 + primeCofactorIndex p n * (p - 1) := by omega
  refine ⟨by omega, ?_⟩
  calc
    n = p * (n / p) := (Nat.mul_div_cancel' hpn).symm
    _ = p * (1 + primeCofactorIndex p n * (p - 1)) := by rw [hrepr]

/-- Every prime factor gives a positive progression parameter. -/
theorem exists_prime_cofactor_parameter {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) :
    ∃ j : ℕ, 1 ≤ j ∧ n = p * (1 + j * (p - 1)) :=
  ⟨primeCofactorIndex p n, prime_cofactor_index_spec hn hp hpn⟩

/-- For a fixed prime, the canonical index is injective on its Carmichael multiples. -/
theorem prime_cofactor_index_inj {p n₁ n₂ : ℕ} (hp : p.Prime)
    (h₁ : IsCarmichael n₁) (h₂ : IsCarmichael n₂) (hp₁ : p ∣ n₁) (hp₂ : p ∣ n₂)
    (hindex : primeCofactorIndex p n₁ = primeCofactorIndex p n₂) : n₁ = n₂ := by
  calc
    n₁ = p * (1 + primeCofactorIndex p n₁ * (p - 1)) :=
      (prime_cofactor_index_spec h₁ hp hp₁).2
    _ = p * (1 + primeCofactorIndex p n₂ * (p - 1)) := by rw [hindex]
    _ = n₂ := (prime_cofactor_index_spec h₂ hp hp₂).2.symm

/-- An upper bound on the number gives the required upper bound on its positive index. -/
theorem prime_cofactor_index_le {n p X : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) (hnX : n ≤ X) :
    primeCofactorIndex p n ≤ X / (p * (p - 1)) := by
  have hdenom : 0 < p * (p - 1) := Nat.mul_pos hp.pos (by have := hp.two_le; omega)
  apply (Nat.le_div_iff_mul_le hdenom).mpr
  calc
    primeCofactorIndex p n * (p * (p - 1)) =
        p * (primeCofactorIndex p n * (p - 1)) := by ring
    _ ≤ p + p * (primeCofactorIndex p n * (p - 1)) := Nat.le_add_left _ _
    _ = p * (1 + primeCofactorIndex p n * (p - 1)) := by ring
    _ = n := (prime_cofactor_index_spec hn hp hpn).2.symm
    _ ≤ X := hnX

/-- The finite set of Carmichael numbers at most `X` divisible by `p`. -/
noncomputable def carmichaelsWithPrimeFactorUpTo (p X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter (fun n => IsCarmichael n ∧ p ∣ n)

@[simp]
theorem mem_carmichaelsWithPrimeFactorUpTo {p X n : ℕ} :
    n ∈ carmichaelsWithPrimeFactorUpTo p X ↔ n ≤ X ∧ IsCarmichael n ∧ p ∣ n := by
  classical
  simp only [carmichaelsWithPrimeFactorUpTo, Finset.mem_filter,
    Finset.mem_range_succ_iff]

/-- The finite set agrees exactly with the bounded set in the counting statement. -/
theorem coe_carmichaelsWithPrimeFactorUpTo (p X : ℕ) :
    (carmichaelsWithPrimeFactorUpTo p X : Set ℕ) =
      {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ p ∣ n} := by
  ext n
  exact mem_carmichaelsWithPrimeFactorUpTo

/-- Finiteness of the bounded set, independently of any primality hypothesis. -/
theorem carmichaels_with_prime_factor_finite (p X : ℕ) :
    {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ p ∣ n}.Finite := by
  rw [← coe_carmichaelsWithPrimeFactorUpTo p X]
  exact Finset.finite_toSet _

/-- A finite fixed-prime bound. The injection lands in `[1, X / (p * (p - 1))]`,
not an interval containing zero; hence there is no extra `+ 1` in the bound. -/
theorem card_carmichaelsWithPrimeFactorUpTo_le {p : ℕ} (hp : p.Prime) (X : ℕ) :
    (carmichaelsWithPrimeFactorUpTo p X).card ≤ X / (p * (p - 1)) := by
  classical
  have hcard : (carmichaelsWithPrimeFactorUpTo p X).card ≤
      (Finset.Icc 1 (X / (p * (p - 1)))).card := by
    apply Finset.card_le_card_of_injOn (primeCofactorIndex p)
    · intro n hnmem
      obtain ⟨hnX, hn, hpn⟩ := mem_carmichaelsWithPrimeFactorUpTo.mp hnmem
      exact Finset.mem_Icc.mpr
        ⟨(prime_cofactor_index_spec hn hp hpn).1, prime_cofactor_index_le hn hp hpn hnX⟩
    · intro n₁ hn₁ n₂ hn₂ hindex
      obtain ⟨_, h₁, hp₁⟩ := mem_carmichaelsWithPrimeFactorUpTo.mp hn₁
      obtain ⟨_, h₂, hp₂⟩ := mem_carmichaelsWithPrimeFactorUpTo.mp hn₂
      exact prime_cofactor_index_inj hp h₁ h₂ hp₁ hp₂ hindex
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hcard

/-- The same exact fixed-prime cardinal bound stated directly for a set of naturals. -/
theorem ncard_carmichaels_with_prime_factor_le {p : ℕ} (hp : p.Prime) (X : ℕ) :
    {n : ℕ | n ≤ X ∧ IsCarmichael n ∧ p ∣ n}.ncard ≤ X / (p * (p - 1)) := by
  rw [← coe_carmichaelsWithPrimeFactorUpTo p X, Set.ncard_coe_finset]
  exact card_carmichaelsWithPrimeFactorUpTo_le hp X

end Erdos1057.CarmichaelCertificates
