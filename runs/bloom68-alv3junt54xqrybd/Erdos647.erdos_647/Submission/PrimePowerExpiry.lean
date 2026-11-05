import Submission.Structural
import Mathlib.NumberTheory.PowModTotient
import Mathlib.FieldTheory.Finite.Basic

/-!
Actual exclusion of prime-power exponents in prime-power expiry endpoints.
This is an infinite-subfamily result, not a settlement for arbitrary endpoints.
Only the elementary dependencies and the proved exclusion are included.
-/

namespace Erdos647Expiry

open scoped ArithmeticFunction.sigma
set_option maxHeartbeats 2000000

def expiry (p e : ℕ) : ℕ := p^e+e-1

lemma exponent_lt_power {p : ℕ} (hp : 2 ≤ p) (e : ℕ) : e < p^e := by
  induction e with
  | zero => norm_num
  | succ e ih => rw [pow_succ]; nlinarith

lemma square_mod_eight_of_odd {p : ℕ} (hp : p % 2 = 1) : p^2 % 8 = 1 := by
  have h := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 8)
  have hb : p % 8 < 8 := Nat.mod_lt _ (by decide)
  interval_cases hr : p % 8 <;> norm_num [hr, hp] at h <;>
    norm_num [Nat.pow_mod, hr]

lemma pow_one_mod_of_totient_dvd {p e q : ℕ} (hq : 1 < q)
    (hcop : p.Coprime q) (he : q.totient ∣ e) : p^e % q = 1 := by
  obtain ⟨a, rfl⟩ := he
  rw [pow_mul, Nat.pow_mod, Nat.pow_totient_mod_eq_one hq hcop, one_pow]
  exact Nat.mod_eq_of_lt hq

lemma modulus_dvd_exponent_of_power_one {p e q : ℕ} (he : 2 ≤ e)
    (hn : q ∣ expiry p e) (hpw : p^e % q = 1) : q ∣ e := by
  have hn' := Nat.mod_eq_zero_of_dvd hn
  dsimp [expiry] at hn'
  have hr : p^e+e-1+1 = p^e+e := by omega
  have hb := congrArg (fun t : ℕ => t % q) hr
  dsimp only at hb
  rw [Nat.add_mod, hn', zero_add, Nat.add_mod, hpw] at hb
  have hemod : e % q = 0 := by
    have hpos : 1 < q := by
      have : 1 < q ∨ q ≤ 1 := lt_or_ge 1 q
      rcases this with h | h
      · exact h
      · interval_cases q <;> simp_all <;> omega
    have heq : (1 + e % q) % q = 1 := by simpa [Nat.mod_eq_of_lt hpos] using hb.symm
    have hsmall := Nat.mod_lt e (by omega : 0 < q)
    by_cases hh : 1+e%q < q
    · rw [Nat.mod_eq_of_lt hh] at heq
      omega
    · have hheq : 1+e%q=q := by omega
      rw [hheq, Nat.mod_self] at heq
      omega
  exact Nat.dvd_iff_mod_eq_zero.mpr hemod

/-- Any nontrivial divisor of the binary exponent at which Frobenius fixes 2
makes the mandatory prime n-1 composite.  Composite moduli are permitted. -/
theorem binary_residue_factor_notP {e q : ℕ} (he : 2 ≤ e)
    (hn : 24 < expiry 2 e) (hq : 1 < q) (hqe : q ∣ e)
    (hroot : Nat.ModEq q (2^e) 2) : ¬ Structural.P (expiry 2 e) := by
  intro hP
  have hprime := Structural.prime_sub_one_of_P hP hn
  have hqle : q ≤ e := Nat.le_of_dvd (by omega : 0 < e) hqe
  have hpow := exponent_lt_power (by decide : 2 ≤ 2) e
  have hsum : 2 ≤ 2^e+e := by omega
  have hmod : Nat.ModEq q (2^e+e) 2 := by
    change (2^e+e)%q=2%q
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hqe, add_zero, Nat.mod_mod]
    exact hroot
  have hdiv : q ∣ 2^e+e-2 := (Nat.modEq_iff_dvd' hsum).mp hmod.symm
  have hhead : expiry 2 e-1=2^e+e-2 := by dsimp [expiry]; omega
  rw [← hhead] at hdiv
  rcases (Nat.dvd_prime hprime).mp hdiv with h1 | hqhead
  · omega
  · dsimp [expiry] at hqhead
    omega

/-- In particular the entire binary prime-power-exponent family is excluded.
ZMod.pow_card_pow is the iterated Frobenius identity in the actual field F_q. -/
theorem binary_primepower_exponent_notP {e q b : ℕ} (he : 2 ≤ e)
    (hn : 24 < expiry 2 e) (hq : q.Prime) (hb : 0 < b)
    (hexp : e=q^b) : ¬ Structural.P (expiry 2 e) := by
  letI : Fact q.Prime := ⟨hq⟩
  have hroot : Nat.ModEq q (2^e) 2 := by
    apply (ZMod.natCast_eq_natCast_iff (2^e) 2 q).mp
    simpa only [hexp, Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.pow_card_pow (n:=b) (2 : ZMod q))
  have hqe : q ∣ e := by rw [hexp]; exact dvd_pow_self q (by omega : b ≠ 0)
  exact binary_residue_factor_notP he hn hq.one_lt hqe hroot

/-- Odd prime bases force TWO DISTINCT prime divisors of the exponent,
already using only the moduli 8 and (3 or 5). -/
theorem odd_base_exponent_constraints {p e : ℕ} (hp : p.Prime)
    (hpodd : p%2=1) (he : 2 ≤ e)
    (hP : Structural.P (expiry p e)) (hn : 24 < expiry p e) :
    8 ∣ e ∧ (3 ∣ e ∨ 5 ∣ e) := by
  have hM := Structural.base_dvd_of_P hP hn
  have hnd : ∀ d : ℕ, d ∣ 360360 → d ∣ expiry p e := fun d hd => hd.trans hM
  have he2 : 2 ∣ e := modulus_dvd_exponent_of_power_one he
    (hnd 2 (by decide)) (by simp [Nat.pow_mod, hpodd])
  have hp8 : p^e%8=1 := by
    obtain ⟨a, rfl⟩ := he2
    rw [pow_mul, Nat.pow_mod, square_mod_eight_of_odd hpodd, one_pow]
    norm_num
  have he8 : 8 ∣ e := modulus_dvd_exponent_of_power_one he (hnd 8 (by decide)) hp8
  refine ⟨he8, ?_⟩
  by_cases hp3 : p=3
  · right
    have he4 : 4 ∣ e := (by decide : 4 ∣ 8).trans he8
    exact modulus_dvd_exponent_of_power_one he (hnd 5 (by decide))
      (pow_one_mod_of_totient_dvd (by decide) (by rw [hp3]; decide)
        (by simpa using he4))
  · left
    have hcop : p.Coprime 3 := (Nat.coprime_primes hp Nat.prime_three).mpr hp3
    exact modulus_dvd_exponent_of_power_one he (hnd 3 (by decide))
      (pow_one_mod_of_totient_dvd (by decide) hcop (by simpa using he2))

/-- GLOBAL actual expiry exclusion when the EXPONENT, not just the job,
is a prime power.  This covers every prime base and every positive power. -/
theorem primepower_exponent_notP {p e q b : ℕ} (hp : p.Prime)
    (he : 2 ≤ e) (hn : 24 < expiry p e) (hq : q.Prime)
    (hb : 0 < b) (hexp : e=q^b) : ¬ Structural.P (expiry p e) := by
  rcases hp.eq_two_or_odd with hp2 | hpodd
  · subst p
    exact binary_primepower_exponent_notP he hn hq hb hexp
  · intro hP
    obtain ⟨he8, he35⟩ := odd_base_exponent_constraints hp hpodd he hP hn
    have he2 : 2 ∣ e := (by decide : 2 ∣ 8).trans he8
    rw [hexp] at he2 he35
    have hq2 : q=2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
      (Nat.prime_two.dvd_of_dvd_pow he2) |>.symm
    rcases he35 with h3 | h5
    · have hh := Nat.prime_three.dvd_of_dvd_pow h3
      rw [hq2] at hh
      norm_num at hh
    · have hh := (by decide : Nat.Prime 5).dvd_of_dvd_pow h5
      rw [hq2] at hh
      norm_num at hh

/-- Logical witness extraction from the original definition, not a record inference. -/
theorem exists_improving_job_of_notP {n : ℕ} (h : ¬ Structural.P n) :
    ∃ m : ℕ, m < n ∧ n + 2 < m + ArithmeticFunction.sigma 0 m := by
  simp only [Structural.P, not_forall, not_le] at h
  obtain ⟨m, hm, hlt⟩ := h
  exact ⟨m, hm, hlt⟩

/-- Explicit all-size witness conclusion for prime-power exponents. -/
theorem primepower_exponent_witness {p e q b : ℕ} (hp : p.Prime)
    (he : 2 ≤ e) (hn : 24 < expiry p e) (hq : q.Prime)
    (hb : 0 < b) (hexp : e=q^b) :
    ∃ m : ℕ, m < expiry p e ∧ expiry p e + 2 < m + ArithmeticFunction.sigma 0 m :=
  exists_improving_job_of_notP (primepower_exponent_notP hp he hn hq hb hexp)

/-- The original finite-supremum inequality fails throughout this subfamily. -/
theorem primepower_exponent_iSup_not_le {p e q b : ℕ} (hp : p.Prime)
    (he : 2 ≤ e) (hn : 24 < expiry p e) (hq : q.Prime)
    (hb : 0 < b) (hexp : e = q ^ b) :
    ¬ ((⨆ m : Fin (expiry p e), (m : ℕ) + σ 0 (m : ℕ)) ≤ expiry p e + 2) := by
  intro hsup
  exact primepower_exponent_notP hp he hn hq hb hexp
    ((Structural.P_iff_iSup_le _).mpr hsup)

/-- Binary expiry endpoints are also excluded for every exponent satisfying
 the base-two Fermat congruence, without requiring a prime-power exponent. -/
theorem binary_fermat_exponent_notP {e : ℕ} (he : 2 ≤ e)
    (hn : 24 < expiry 2 e) (hroot : Nat.ModEq e (2 ^ e) 2) :
    ¬ Structural.P (expiry 2 e) :=
  binary_residue_factor_notP he hn (by omega) (dvd_refl e) hroot

end Erdos647Expiry
