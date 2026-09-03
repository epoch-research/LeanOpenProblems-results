import Submission.Richness

/-!
# Equality in the 384-divisor necessary condition

A witness `P n` above 24 with exactly 384 divisors must be `360360 * q`,
where `q` is prime and `13 < q`. This is only an auxiliary necessary condition;
it does not settle either theorem in `Submission.Spec`.

Every proper divisor of the multiplier divides the core. A minimal nondivisor
of a positive integer is a prime power, with exponent one larger than its
exponent in that integer. For the core, the composite possibilities are
`16, 27, 25, 49, 121, 169`; six short divisor certificates exclude them.
-/

namespace Erdos647

open scoped ArithmeticFunction.sigma

/-- Divisor counts strictly increase along proper divisibility. -/
theorem card_divisors_lt_of_dvd {d m : ℕ} (hd : d ∣ m) (hlt : d < m) :
    d.divisors.card < m.divisors.card := by
  have hm0 : m ≠ 0 := by omega
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Nat.divisors_subset_of_dvd hm0 hd, ?_⟩
  intro he
  have hm : m ∈ d.divisors := by
    rw [he]
    exact Nat.mem_divisors.mpr ⟨dvd_refl m, hm0⟩
  have hl := Nat.divisor_le hm
  omega

/-- A nondivisor whose proper divisors all divide `c` is a minimal prime power
not dividing `c`. The prime need not divide `c`, in which case the exponent is one. -/
private theorem eq_prime_power_of_proper_divisors_dvd {q c : ℕ}
    (hq : q ≠ 0) (hc : c ≠ 0) (hnd : ¬ q ∣ c)
    (hproper : ∀ a < q, a ∣ q → a ∣ c) :
    ∃ p, Nat.Prime p ∧ q = p ^ (c.factorization p + 1) := by
  have hfac : ¬ ∀ p : ℕ, Nat.Prime p → q.factorization p ≤ c.factorization p := by
    intro hf
    exact hnd ((Nat.factorization_prime_le_iff_dvd hq hc).mp hf)
  push_neg at hfac
  obtain ⟨p, hp, hlt⟩ := hfac
  have hd : p ^ (c.factorization p + 1) ∣ q :=
    (hp.pow_dvd_iff_le_factorization hq).mpr hlt
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hd
  refine ⟨p, hp, ?_⟩
  by_contra heq
  exact Nat.pow_succ_factorization_not_dvd hc hp
    (hproper _ (lt_of_le_of_ne hle (Ne.symm heq)) hd)

private theorem prime_dvd_core {p : ℕ} (hp : Nat.Prime p) (hd : p ∣ 360360) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  have hc : (360360 : ℕ) = 2 ^ 3 * (3 ^ 2 * (5 * (7 * (11 * 13)))) := by norm_num
  rw [hc] at hd
  simpa only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : (3 : ℕ) ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)] using hd

private theorem factorization_eq_of_dvd_not_dvd {n p k : ℕ} (hn : n ≠ 0)
    (hp : Nat.Prime p) (hd : p ^ k ∣ n) (hnd : ¬ p ^ (k + 1) ∣ n) :
    n.factorization p = k := by
  rw [hp.pow_dvd_iff_le_factorization hn] at hd hnd
  omega

/-- For each prime in the core, its first power not dividing the core gives
an excluded multiplier. Each certificate exhibits four divisors at offset one. -/
private theorem not_P_core_mul_minimal_prime_power {p : ℕ}
    (hp : Nat.Prime p) (hd : p ∣ 360360) :
    ¬ P (360360 * p ^ ((360360 : ℕ).factorization p + 1)) := by
  rcases prime_dvd_core hp hd with rfl | rfl | rfl | rfl | rfl | rfl
  · have hf : (360360 : ℕ).factorization 2 = 3 :=
      factorization_eq_of_dvd_not_dvd (by decide) (by decide) (by decide) (by decide)
    rw [hf]
    exact not_P_of_divisor_certificate (j := 1) (s := {1, 19, 73, 1387}) (by decide)
  · have hf : (360360 : ℕ).factorization 3 = 2 :=
      factorization_eq_of_dvd_not_dvd (by decide) (by decide) (by decide) (by decide)
    rw [hf]
    exact not_P_of_divisor_certificate (j := 1) (s := {1, 79, 1559, 6241}) (by decide)
  · have hf : (360360 : ℕ).factorization 5 = 1 :=
      factorization_eq_of_dvd_not_dvd (by decide) (by decide) (by decide) (by decide)
    rw [hf]
    exact not_P_of_divisor_certificate (j := 1) (s := {1, 127, 70937, 9008999}) (by decide)
  · have hf : (360360 : ℕ).factorization 7 = 1 :=
      factorization_eq_of_dvd_not_dvd (by decide) (by decide) (by decide) (by decide)
    rw [hf]
    exact not_P_of_divisor_certificate (j := 1) (s := {1, 53, 431, 773}) (by decide)
  · have hf : (360360 : ℕ).factorization 11 = 1 :=
      factorization_eq_of_dvd_not_dvd (by decide) (by decide) (by decide) (by decide)
    rw [hf]
    exact not_P_of_divisor_certificate (j := 1) (s := {1, 29, 263, 5717}) (by decide)
  · have hf : (360360 : ℕ).factorization 13 = 1 :=
      factorization_eq_of_dvd_not_dvd (by decide) (by decide) (by decide) (by decide)
    rw [hf]
    exact not_P_of_divisor_certificate (j := 1) (s := {1, 5101, 11939, 60900839}) (by decide)

/-- Equality in the divisor-count lower bound forces a prime multiplier of the core. -/
theorem P.eq_core_mul_prime_of_sigma_eq_384 {n : ℕ} (h : P n) (hn : 24 < n)
    (hc : σ 0 n = 384) : ∃ q, Nat.Prime q ∧ n = 360360 * q := by
  obtain ⟨q, rfl⟩ := h.dvd_360360 hn
  have hq0 : q ≠ 0 := by omega
  have hnd : ¬ q ∣ 360360 := fun hd => not_P_core_mul_divisor hd h
  have hfactor : ∀ a < q, a ∣ q → a ∣ 360360 := by
    intro a haq ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp only [zero_dvd_iff] at ha
      exact hq0 ha
    have hlt : 360360 * a < 360360 * q := Nat.mul_lt_mul_of_pos_left haq (by decide)
    have hda : 360360 * a ∣ 360360 * q := Nat.mul_dvd_mul_left 360360 ha
    have hcalt := card_divisors_lt_of_dvd hda hlt
    rw [← ArithmeticFunction.sigma_zero_apply (360360 * q), hc] at hcalt
    have haC : 360360 * a ∣ 360360 * 360360 := by
      by_contra hnot
      have hl := two_mul_card_divisors_le_of_not_dvd_sq
        (Nat.mul_ne_zero (by decide : (360360 : ℕ) ≠ 0) ha0)
        (dvd_mul_right 360360 a) hnot
      rw [card_divisors_core] at hl
      omega
    exact Nat.dvd_of_mul_dvd_mul_left (by decide) haC
  obtain ⟨p, hp, hqp⟩ :=
    eq_prime_power_of_proper_divisors_dvd hq0 (by decide) hnd hfactor
  have hpc : ¬ p ∣ 360360 := by
    intro hpd
    rw [hqp] at h
    exact not_P_core_mul_minimal_prime_power hp hpd h
  rw [Nat.factorization_eq_zero_of_not_dvd hpc] at hqp
  simp only [zero_add, pow_one] at hqp
  subst q
  exact ⟨p, hp, rfl⟩

/-- The prime multiplier in the equality case is larger than every prime in the core. -/
theorem P.eq_core_mul_prime_gt_13_of_sigma_eq_384 {n : ℕ} (h : P n) (hn : 24 < n)
    (hc : σ 0 n = 384) : ∃ q, Nat.Prime q ∧ 13 < q ∧ n = 360360 * q := by
  obtain ⟨q, hq, rfl⟩ := h.eq_core_mul_prime_of_sigma_eq_384 hn hc
  have hgt : 13 < q := by
    by_contra hle
    have hsmall : ∀ p ≤ 13, Nat.Prime p → p ∣ 360360 := by decide
    exact not_P_core_mul_divisor (hsmall q (by omega) hq) h
  exact ⟨q, hq, hgt, rfl⟩

end Erdos647

#print axioms Erdos647.P.eq_core_mul_prime_of_sigma_eq_384
#print axioms Erdos647.P.eq_core_mul_prime_gt_13_of_sigma_eq_384
