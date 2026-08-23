import Submission.Generic
open Nat Finset BigOperators Int Polynomial

namespace Core

abbrev ZPoly := Polynomial ℤ

noncomputable def cyclo3 : ZPoly := X ^ 2 + X + 1

def PMod (a b : ZPoly) : Prop := cyclo3 ∣ a - b

lemma pmod_refl (a : ZPoly) : PMod a a := by simp [PMod]
lemma pmod_symm {a b : ZPoly} (h : PMod a b) : PMod b a := by
  obtain ⟨q, hq⟩ := h
  use -q
  dsimp [PMod] at hq ⊢
  linear_combination -hq

lemma pmod_neg {a b : ZPoly} (h : PMod a b) : PMod (-a) (-b) := by
  obtain ⟨q, hq⟩ := h
  use -q
  dsimp [PMod] at hq ⊢
  linear_combination -hq
lemma pmod_trans {a b c : ZPoly} (h₁ : PMod a b) (h₂ : PMod b c) : PMod a c := by
  rw [PMod] at *
  convert dvd_add h₁ h₂ using 1 <;> ring
lemma pmod_add {a b c d : ZPoly} (h₁ : PMod a b) (h₂ : PMod c d) : PMod (a+c) (b+d) := by
  rw [PMod] at *
  convert dvd_add h₁ h₂ using 1 <;> ring
lemma pmod_mul {a b c d : ZPoly} (h₁ : PMod a b) (h₂ : PMod c d) : PMod (a*c) (b*d) := by
  rw [PMod] at *
  have h := dvd_add (dvd_mul_of_dvd_right h₁ c) (dvd_mul_of_dvd_left h₂ b)
  convert h using 1 <;> ring
lemma pmod_pow {a b : ZPoly} (h : PMod a b) (n : ℕ) : PMod (a^n) (b^n) := by
  induction n with
  | zero => exact pmod_refl _
  | succ n ih => simpa [pow_succ] using pmod_mul ih h

lemma one_add_X_pmod : PMod (1 + X) (-X^2) := by
  use 1
  dsimp [PMod, cyclo3]
  ring

lemma X_cube_pmod : PMod (X^3) 1 := by
  use X - 1
  dsimp [PMod, cyclo3]
  ring

lemma X_pow_pmod_mod3 (n : ℕ) : PMod (X^n) (X^(n%3)) := by
  have h := pmod_pow X_cube_pmod (n / 3)
  have hn : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm.trans (by omega)
  have hm := pmod_mul h (pmod_refl (X^(n%3)))
  convert hm using 1
  · rw [← pow_mul, ← pow_add, ← hn]
  · simp only [one_pow, one_mul]

lemma prime_mod_three {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : p % 3 = 1 ∨ p % 3 = 2 := by
  have hlt := Nat.mod_lt p (by omega : 0 < 3)
  have hn0 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.dvd_prime hp).mp hd
    omega
  omega

lemma frob_numerator_dvd_cyclo3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    cyclo3 ∣ (1 + X)^p - (1 + X^p) := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hpow := pmod_pow one_add_X_pmod p
  have hneg : (-X^2 : ZPoly)^p = -(X^(2*p)) := by
    obtain ⟨t, rfl⟩ := hodd
    simp [pow_succ, pow_mul]
  rw [hneg] at hpow
  rcases prime_mod_three hp hp5 with hpmod | hpmod
  · have hx := X_pow_pmod_mod3 (2*p)
    have h2 : (2*p)%3 = 2 := by omega
    rw [h2] at hx
    norm_num at hx
    have hx' := X_pow_pmod_mod3 p
    rw [hpmod] at hx'
    norm_num at hx'
    have hleft : PMod ((1+X)^p) (-X^2) :=
      pmod_trans hpow (pmod_neg hx)
    have hrhs : PMod (1 + X^p) (-X^2) :=
      pmod_trans (pmod_add (pmod_refl 1) hx') one_add_X_pmod
    exact pmod_trans hleft (pmod_symm hrhs)
  · have hx := X_pow_pmod_mod3 (2*p)
    have h2 : (2*p)%3 = 1 := by omega
    rw [h2] at hx
    norm_num at hx
    have hx' := X_pow_pmod_mod3 p
    rw [hpmod] at hx'
    norm_num at hx'
    have hone : PMod (1 + X^2) (-X) := by
      use 1
      dsimp [PMod, cyclo3]
      ring
    have hrhs : PMod (1 + X^p) (-X) :=
      pmod_trans (pmod_add (pmod_refl 1) hx') hone
    have hleft : PMod ((1+X)^p) (-X) :=
      pmod_trans hpow (pmod_neg hx)
    exact pmod_trans hleft (pmod_symm hrhs)


noncomputable def frobError (p : ℕ) : ZPoly :=
  ∑ i ∈ Finset.Ioo 0 p, C ((p.choose i / p : ℕ) : ℤ) * X ^ i

lemma coeff_frobError (p n : ℕ) :
    (frobError p).coeff n =
      if 0 < n ∧ n < p then ((p.choose n / p : ℕ) : ℤ) else 0 := by
  classical
  simp [frobError]

lemma frob_decomposition {p : ℕ} (hp : p.Prime) :
    (1 + X : ZPoly)^p = 1 + X^p + C (p : ℤ) * frobError p := by
  ext n
  rw [coeff_one_add_X_pow]
  rw [coeff_add, coeff_add, coeff_one, coeff_X_pow, coeff_C_mul, coeff_frobError]
  by_cases hn0 : n = 0
  · subst n; simp [hp.ne_zero, Ne.symm hp.ne_zero]
  by_cases hnp : n = p
  · subst n; simp [hp.ne_zero, Ne.symm hp.ne_zero]
  by_cases hlt : n < p
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hd : p ∣ p.choose n := hp.dvd_choose_self hn0 hlt
    simp only [hnpos, hlt, and_self, if_true, hn0, hnp, if_false, zero_add,
      Int.natCast_ediv]
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  · have hpn : p < n := by omega
    have hchoose : p.choose n = 0 := Nat.choose_eq_zero_of_lt hpn
    simp [hchoose, hn0, hnp, hlt]

lemma frobError_dvd_cyclo3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    cyclo3 ∣ frobError p := by
  have hmonic : cyclo3.Monic := by
    dsimp [cyclo3]
    monicity <;> norm_num
  have hnum := frob_numerator_dvd_cyclo3 hp hp5
  have heq : (1 + X : ZPoly)^p - (1 + X^p) = C (p : ℤ) * frobError p := by
    rw [frob_decomposition hp]
    ring
  rw [heq] at hnum
  have hrem : (p : ℤ) • (frobError p %ₘ cyclo3) = 0 := by
    rw [← Polynomial.smul_modByMonic]
    rw [← C_mul']
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hnum
  have hrem0 : frobError p %ₘ cyclo3 = 0 := by
    ext n
    have hn := congr_arg (fun f : ZPoly => f.coeff n) hrem
    simp only [coeff_smul, coeff_zero] at hn ⊢
    exact (mul_eq_zero.mp hn).resolve_left (by exact_mod_cast hp.ne_zero)
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mp hrem0


def qCoeff (n : ℕ) : ℤ :=
  if n = 0 then 1 else if 3 ∣ n then 2 else -1

noncomputable def Qseries : PowerSeries ℤ := PowerSeries.mk qCoeff

lemma qCoeff_mul_prime {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    qCoeff (p * n) = qCoeff n := by
  by_cases hn : n = 0
  · subst n; simp [qCoeff]
  have hp0 : p ≠ 0 := hp.ne_zero
  simp only [qCoeff, mul_eq_zero, hp0, hn, or_self, if_false]
  have hp3 : ¬3 ∣ p := by
    intro h
    have := (Nat.dvd_prime hp).mp h
    omega
  simp [Nat.prime_three.dvd_mul, hp3]

lemma qCoeff_recurrence (n : ℕ) :
    qCoeff n + (if 1 ≤ n then qCoeff (n-1) else 0) +
      (if 2 ≤ n then qCoeff (n-2) else 0) =
      if n = 0 then 1 else if n = 2 then -1 else 0 := by
  by_cases h0 : n = 0
  · subst n; norm_num [qCoeff]
  by_cases h1 : n = 1
  · subst n; norm_num [qCoeff]
  by_cases h2 : n = 2
  · subst n; norm_num [qCoeff]
  have hn3 : 3 ≤ n := by omega
  have hm : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have := Nat.mod_lt n (by omega : 0 < 3)
    omega
  rcases hm with hm | hm | hm <;>
    simp [qCoeff, h0, h2, hn3, show 1 ≤ n by omega,
      Nat.dvd_iff_mod_eq_zero, hm] <;> omega

lemma cyclo3_mul_Qseries :
    (cyclo3 : PowerSeries ℤ) * Qseries = 1 - PowerSeries.X^2 := by
  ext n
  rw [show (cyclo3 : PowerSeries ℤ) =
    (PowerSeries.X^2 + PowerSeries.X + 1) by simp [cyclo3]]

  change PowerSeries.coeff n
      ((PowerSeries.X^2 + PowerSeries.X + 1) * Qseries) = _
  rw [add_mul, add_mul]
  have hx : PowerSeries.coeff n (PowerSeries.X * Qseries) =
      if 1 ≤ n then qCoeff (n-1) else 0 := by
    simpa only [pow_one, Qseries, PowerSeries.coeff_mk] using
      PowerSeries.coeff_X_pow_mul' Qseries 1 n
  have hx2 : PowerSeries.coeff n (PowerSeries.X^2 * Qseries) =
      if 2 ≤ n then qCoeff (n-2) else 0 := by
    simpa only [Qseries, PowerSeries.coeff_mk] using
      PowerSeries.coeff_X_pow_mul' Qseries 2 n
  rw [map_add, map_add, hx2, hx]
  simp only [one_mul, Qseries, PowerSeries.coeff_mk, map_sub, map_one,
    PowerSeries.coeff_X_pow]
  rw [show ((if 2 ≤ n then qCoeff (n-2) else 0) +
      (if 1 ≤ n then qCoeff (n-1) else 0)) + qCoeff n =
      qCoeff n + (if 1 ≤ n then qCoeff (n-1) else 0) +
        (if 2 ≤ n then qCoeff (n-2) else 0) by ring]
  rw [qCoeff_recurrence]
  split_ifs <;> norm_num <;> omega


noncomputable def frobQuot (p : ℕ) : ZPoly := frobError p /ₘ cyclo3

lemma frobError_eq_mul_quot' {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    frobError p = cyclo3 * frobQuot p := by
  have hmonic : cyclo3.Monic := by
    dsimp [cyclo3]; monicity <;> norm_num
  calc
    frobError p = frobError p %ₘ cyclo3 + cyclo3 * (frobError p /ₘ cyclo3) :=
      (Polynomial.modByMonic_add_div (frobError p) hmonic).symm
    _ = cyclo3 * frobQuot p := by
      rw [(Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr
        (frobError_dvd_cyclo3 hp hp5), zero_add]
      rfl

lemma natDegree_frobError_le (p : ℕ) : (frobError p).natDegree ≤ p - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_frobError]
  simp only [ite_eq_right_iff]
  intro h
  omega

private lemma natDegree_cyclo3 : cyclo3.natDegree = 2 := by
  dsimp [cyclo3]
  compute_degree <;> norm_num

private lemma natDegree_frobQuot_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (frobQuot p).natDegree ≤ p - 3 := by
  have heq := frobError_eq_mul_quot' hp hp5
  have hq0 : frobQuot p ≠ 0 := by
    intro h
    rw [h, mul_zero] at heq
    have hc := congr_arg (fun f : ZPoly => f.coeff 1) heq
    change (frobError p).coeff 1 = 0 at hc
    rw [coeff_frobError] at hc
    norm_num [hp.one_lt, hp.ne_zero] at hc
  have hmonic : cyclo3.Monic := by
    dsimp [cyclo3]; monicity <;> norm_num
  have hdeg := Polynomial.natDegree_mul hmonic.ne_zero hq0
  rw [natDegree_cyclo3] at hdeg
  have hle := natDegree_frobError_le p
  rw [heq, hdeg] at hle
  omega

noncomputable def errorPoly (p j : ℕ) : ZPoly :=
  if j = 0 then 0 else
    (1 - X^2) * cyclo3^(j-1) * frobQuot p ^ j

lemma Qseries_mul_frobError_pow {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) :
    Qseries * (frobError p : PowerSeries ℤ) ^ j =
      (errorPoly p j : PowerSeries ℤ) := by
  rw [frobError_eq_mul_quot' hp hp5, Polynomial.coe_mul]
  rw [errorPoly, if_neg (Nat.ne_of_gt hj), Polynomial.coe_mul, Polynomial.coe_mul]
  simp only [Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_X]
  have hj_eq : j = (j-1)+1 := by omega
  conv_lhs =>
    enter [2]
    rw [hj_eq, pow_succ]
  have h := cyclo3_mul_Qseries
  change (cyclo3 : PowerSeries ℤ) * Qseries = 1 - PowerSeries.X^2 at h
  rw [← h]
  have hR : (frobQuot p : PowerSeries ℤ)^j =
      (frobQuot p : PowerSeries ℤ)^(j-1) * (frobQuot p : PowerSeries ℤ) := by
    conv_lhs => rw [hj_eq, pow_succ]
  rw [hR]
  ring


lemma reflect_frobError {p : ℕ} : Polynomial.reflect p (frobError p) = frobError p := by
  ext n
  change (Polynomial.reflect p (frobError p)).coeff n = (frobError p).coeff n

  rw [Polynomial.coeff_reflect]
  by_cases hnp : n ≤ p
  · rw [Polynomial.revAt_le hnp, coeff_frobError, coeff_frobError]
    by_cases hn0 : n = 0
    · subst n; simp
    by_cases hne : n = p
    · subst n; simp
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnlt : n < p := lt_of_le_of_ne hnp hne
    have hsubpos : 0 < p - n := Nat.sub_pos_of_lt hnlt
    have hsublt : p - n < p := Nat.sub_lt (by omega) hnpos
    simp only [hnpos, hnlt, hsubpos, hsublt, and_self, if_true]
    rw [Nat.choose_symm hnp]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hnp)]

private lemma reflect_cyclo3 : Polynomial.reflect 2 cyclo3 = cyclo3 := by
  ext n
  rw [Polynomial.coeff_reflect]
  by_cases hn : n ≤ 2
  · rw [Polynomial.revAt_le hn]
    interval_cases n <;> norm_num [cyclo3, Polynomial.coeff_X, Polynomial.coeff_one]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hn)]

private lemma reflect_pow_eq {f : ZPoly} {N : ℕ} (hdeg : f.natDegree ≤ N)
    (href : Polynomial.reflect N f = f) (j : ℕ) :
    Polynomial.reflect (N*j) (f^j) = f^j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Nat.mul_succ, Polynomial.reflect_mul (f^j) f]
      · rw [ih, href]
      · simpa [Nat.mul_comm] using
          Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hdeg)
      · exact hdeg

lemma reflect_frobQuot {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Polynomial.reflect (p-2) (frobQuot p) = frobQuot p := by
  have heq := frobError_eq_mul_quot' hp hp5
  have hdD : cyclo3.natDegree ≤ 2 := natDegree_cyclo3.le
  have hdR : (frobQuot p).natDegree ≤ p-2 :=
    (natDegree_frobQuot_le hp hp5).trans (by omega)
  have hprod := Polynomial.reflect_mul cyclo3 (frobQuot p) hdD hdR
  have hp2 : 2 + (p-2) = p := by omega
  rw [hp2, ← heq, reflect_frobError, reflect_cyclo3] at hprod
  apply (mul_left_cancel₀ (show cyclo3 ≠ 0 by
    have hm : cyclo3.Monic := by dsimp [cyclo3]; monicity <;> norm_num
    exact hm.ne_zero))
  calc
    cyclo3 * Polynomial.reflect (p-2) (frobQuot p) = frobError p := hprod.symm
    _ = cyclo3 * frobQuot p := heq

private lemma reflect_one_sub_X_sq :
    Polynomial.reflect 2 (1 - X^2 : ZPoly) = -(1-X^2) := by
  ext n
  simp [Polynomial.coeff_reflect, Polynomial.revAt]

lemma reflect_errorPoly {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 0 < j) :
    Polynomial.reflect (p*j) (errorPoly p j) = - errorPoly p j := by
  rw [errorPoly, if_neg (Nat.ne_of_gt hj)]
  have hDdeg : cyclo3.natDegree ≤ 2 := natDegree_cyclo3.le
  have hRdeg : (frobQuot p).natDegree ≤ p-2 :=
    (natDegree_frobQuot_le hp hp5).trans (by omega)
  have hDpow := reflect_pow_eq hDdeg reflect_cyclo3 (j-1)
  have hRpow := reflect_pow_eq hRdeg (reflect_frobQuot hp hp5) j
  have hAdeg : (1-X^2 : ZPoly).natDegree ≤ 2 := by compute_degree <;> norm_num
  have hBDeg : (cyclo3^(j-1)).natDegree ≤ 2*(j-1) := by
    have := Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (j-1) hDdeg)
    omega
  have hCDeg : (frobQuot p ^ j).natDegree ≤ (p-2)*j := by
    simpa [Nat.mul_comm] using
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left j hRdeg)
  have hmul1 := Polynomial.reflect_mul (1-X^2 : ZPoly) (cyclo3^(j-1)) hAdeg hBDeg
  have hmul2 := Polynomial.reflect_mul ((1-X^2 : ZPoly)*cyclo3^(j-1))
    (frobQuot p ^ j) (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hAdeg hBDeg)) hCDeg
  have htwo : 2 + 2 * (j - 1) = 2 * j := by omega
  have hpback : 2 + (p - 2) = p := by omega
  have hidx : 2 + 2*(j-1) + (p-2)*j = p*j := by
    rw [htwo, ← Nat.add_mul, hpback]
  rw [hidx] at hmul2
  rw [hmul1, reflect_one_sub_X_sq, hDpow, hRpow] at hmul2
  convert hmul2 using 1 <;> ring

lemma coeff_errorPoly_antisymm {p j d : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hj : 0 < j) (hd : d ≤ j) :
    (errorPoly p j).coeff (p*(j-d)) = -(errorPoly p j).coeff (p*d) := by
  have h := congr_arg (fun f : ZPoly => f.coeff (p*d)) (reflect_errorPoly hp hp5 hj)
  change (Polynomial.reflect (p*j) (errorPoly p j)).coeff (p*d) =
    (-errorPoly p j).coeff (p*d) at h

  rw [Polynomial.coeff_reflect] at h
  have hle : p*d ≤ p*j := Nat.mul_le_mul_left p hd
  rw [Polynomial.revAt_le hle, coeff_neg] at h
  rw [Nat.mul_sub_left_distrib]
  exact h





end Core
