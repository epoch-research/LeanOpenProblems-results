import FormalConjecturesUtil
/-! Primitive structural lemmas for Carmichael numbers. -/
open Nat

namespace Erdos1057
theorem isCarmichael_lambda_dvd_sub_one {n : ℕ} (hn : IsCarmichael n) :
    ArithmeticFunction.Carmichael n ∣ n - 1 := by
  have hn1 : 1 < n := (hn 1 (by omega) (by simp)).2.2
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  haveI : Fact (1 < n) := ⟨hn1⟩
  rw [ArithmeticFunction.carmichael_eq_exponent hn0]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro u
  let b : ℕ := (u : ZMod n).val
  have hbpos : 1 ≤ b := by
    have hbu : (u : ZMod n) ≠ 0 := (Units.ne_zero u)
    have hbne : b ≠ 0 := by
      intro hzero
      have hcast : (b : ZMod n) = u := ZMod.natCast_zmod_val (u : ZMod n)
      simp [hzero] at hcast
      exact hbu hcast.symm
    omega
  have hcop : n.Coprime b := by
    have hu : IsUnit (u : ZMod n) := Units.isUnit u
    have hcast : (b : ZMod n) = (u : ZMod n) := ZMod.natCast_zmod_val _
    have hbunit : IsUnit (b : ZMod n) := hcast ▸ hu
    exact ((ZMod.isUnit_iff_coprime b n).mp hbunit).symm
  have hpsp : n.FermatPsp b := hn b hbpos hcop
  have hmod : b ^ (n - 1) ≡ 1 [MOD n] := (Nat.probablePrime_iff_modEq n hbpos).mp hpsp.1
  have hz : (b : ZMod n) ^ (n - 1) = 1 :=
    by simpa using (ZMod.natCast_eq_natCast_iff (b ^ (n - 1)) 1 n).mpr hmod
  apply Units.ext
  simpa [b, ZMod.natCast_zmod_val] using hz

theorem carmichael_at_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.Carmichael p = p - 1 := by
  by_cases htwo : p = 2
  · subst p
    simpa using (ArithmeticFunction.carmichael_two_pow_of_le_two (n := 1) (by omega))
  · simpa [Nat.totient_prime hp] using
      (ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp htwo)

theorem carmichael_prime_sub_one_dvd {n p : ℕ}
    (hn : IsCarmichael n) (hp : p.Prime) (hdvd : p ∣ n) : p - 1 ∣ n - 1 := by
  rw [← carmichael_at_prime hp]
  exact (ArithmeticFunction.carmichael_dvd hdvd).trans (isCarmichael_lambda_dvd_sub_one hn)

theorem cofactor_sub_one_dvd {p m : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (h : p - 1 ∣ p * m - 1) : p - 1 ∣ m - 1 := by
  have hInt : ((p : ℤ) - 1) ∣ (p : ℤ) * m - 1 := by
    have hh : ((p - 1 : ℕ) : ℤ) ∣ ((p * m - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    have hpm : 1 ≤ p * m := by nlinarith
    simpa only [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub hpm, Nat.cast_mul, Nat.cast_one] using hh
  have hresult : ((p : ℤ) - 1) ∣ (m : ℤ) - 1 := by
    have hmult : ((p : ℤ) - 1) ∣ ((p : ℤ) - 1) * (m : ℤ) := dvd_mul_right _ _
    convert dvd_sub hInt hmult using 1; ring
  have hnat : ((p - 1 : ℕ) : ℤ) ∣ ((m - 1 : ℕ) : ℤ) := by
    convert hresult using 1 <;> omega
  exact Int.natCast_dvd_natCast.mp hnat

/-- Korselt's necessary congruence after separating a prime factor. -/
theorem isCarmichael_cofactor_constraint {n p m : ℕ}
    (hn : IsCarmichael n) (hp : p.Prime) (hnfac : n = p * m) : p - 1 ∣ m - 1 := by
  have hnm : 1 < n := (hn 1 (by omega) (by simp)).2.2
  have hnp : ¬n.Prime := (hn 1 (by omega) (by simp)).2.1
  have hmpos : 1 ≤ m := by
    by_contra h
    have hzero : m = 0 := by omega
    simp [hzero] at hnfac
    omega
  have hdiv : p - 1 ∣ p * m - 1 := by
    simpa only [← hnfac] using carmichael_prime_sub_one_dvd hn hp (hnfac ▸ dvd_mul_right p m)
  exact cofactor_sub_one_dvd hp.two_le hmpos hdiv

/-- Each prime factor of a Carmichael number is at most its cofactor. -/
theorem isCarmichael_prime_le_cofactor {n p m : ℕ}
    (hn : IsCarmichael n) (hp : p.Prime) (hnfac : n = p * m) : p ≤ m := by
  have hnm : 1 < n := (hn 1 (by omega) (by simp)).2.2
  have hnp : ¬n.Prime := (hn 1 (by omega) (by simp)).2.1
  have hm : 2 ≤ m := by
    by_contra h
    have hcases : m = 0 ∨ m = 1 := by omega
    rcases hcases with hzero | hone
    · simp [hzero] at hnfac; omega
    · have : n = p := by simpa [hone] using hnfac
      exact hnp (this ▸ hp)
  have hdiv : p - 1 ∣ m - 1 := isCarmichael_cofactor_constraint hn hp hnfac
  have hle : p - 1 ≤ m - 1 := Nat.le_of_dvd (by omega) hdiv
  omega

/-- Every Carmichael number is squarefree (necessary half of Korselt's criterion). -/
theorem isCarmichael_squarefree {n : ℕ} (hn : IsCarmichael n) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hpn
  have hpd : p ∣ ArithmeticFunction.Carmichael (p * p) := by
    by_cases ht : p = 2
    · subst p
      have h2 : ArithmeticFunction.Carmichael 4 = 2 := by
        simpa using (ArithmeticFunction.carmichael_two_pow_of_le_two (n := 2) (by omega))
      norm_num [h2]
    · rw [← pow_two, ArithmeticFunction.carmichael_pow_of_prime_ne_two 2 hp ht,
        Nat.totient_prime_pow hp (by omega : 0 < 2)]
      simp
  have hdiv : p ∣ n := (dvd_mul_right p p).trans hpn
  have hpred : p ∣ n - 1 :=
    (hpd.trans (ArithmeticFunction.carmichael_dvd hpn)).trans
      (isCarmichael_lambda_dvd_sub_one hn)
  have hn1 : 1 < n := (hn 1 (by omega) (by simp)).2.2
  have hni : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hdiv
  have hnmi : (p : ℤ) ∣ (n : ℤ) - 1 := by
    have h : (p : ℤ) ∣ ((n - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpred
    simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] using h
  have hone : (p : ℤ) ∣ 1 := by
    convert dvd_sub hni hnmi using 1; ring
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hone)

/-- Korselt's criterion for the Fermat-pseudoprime definition used in this project. -/
theorem isCarmichael_iff_korselt (n : ℕ) :
    IsCarmichael n ↔ n.Composite ∧ Squarefree n ∧
      ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
  constructor
  · intro hn
    have h1 : n.FermatPsp 1 := hn 1 (by omega) (by simp)
    exact ⟨⟨h1.2.2, h1.2.1⟩, isCarmichael_squarefree hn,
      fun p hp hpn => carmichael_prime_sub_one_dvd hn hp hpn⟩
  · rintro ⟨hcomp, hsq, hprime⟩
    have hn0 : n ≠ 0 := by have := hcomp.1; omega
    haveI : NeZero n := ⟨hn0⟩
    have hlambda : ArithmeticFunction.Carmichael n ∣ n - 1 := by
      rw [ArithmeticFunction.carmichael_factorization n]
      apply Finset.lcm_dvd
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hfac := Nat.factorization_eq_one_of_squarefree hsq hpp hpd
      simpa [Function.comp_apply, hfac, carmichael_at_prime hpp] using hprime p hpp hpd
    intro b hb hcop
    let u : (ZMod n)ˣ := ZMod.unitOfCoprime b hcop.symm
    have hpow0 : u ^ ArithmeticFunction.Carmichael n = 1 :=
      ArithmeticFunction.pow_carmichael _
    have hpow : u ^ (n - 1) = 1 := by
      obtain ⟨k,hk⟩ := hlambda
      rw [hk, pow_mul, hpow0, one_pow]
    have hz : (b : ZMod n) ^ (n - 1) = 1 := by
      have h := congrArg (fun v : (ZMod n)ˣ => (v : ZMod n)) hpow
      simpa [u, ZMod.unitOfCoprime] using h
    refine ⟨(Nat.probablePrime_iff_modEq n hb).mpr ?_, hcomp.2, hcomp.1⟩
    exact (ZMod.natCast_eq_natCast_iff (b ^ (n - 1)) 1 n).mp (by simpa using hz)


end Erdos1057
