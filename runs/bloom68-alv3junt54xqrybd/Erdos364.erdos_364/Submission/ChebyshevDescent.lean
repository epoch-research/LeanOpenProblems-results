import Submission.PowerfulStructure

/-!
# Full integer Chebyshev prime-square descent

An unconditional helper for Erdős problem 364. This module does not import
`Submission.Spec` and does not assert that a full powerful triple exists.
The Chebyshev polynomials are Mathlib's first-kind polynomials over `ℤ`.

The arithmetic uses prime-square divisibility, rather than an exact endpoint
valuation formula. In particular it allows the exceptional extra cancellation
at the index prime `3`.
-/

namespace Erdos364.ChebyshevDescent

open Polynomial
open Erdos364.PowerfulStructure

/-- First-kind Chebyshev evaluation at an integer, with a natural index. -/
noncomputable def cheb (n : ℕ) (x : ℤ) : ℤ :=
  (Polynomial.Chebyshev.T ℤ (n : ℤ)).eval x

/-- Powerfulness of a signed integer means powerfulness of its absolute value. -/
def Powerful (x : ℤ) : Prop := Nat.Powerful x.natAbs

/-- All three entries, including the middle one, are powerful. -/
def Full (x : ℤ) : Prop := Powerful (x - 1) ∧ Powerful x ∧ Powerful (x + 1)

/-- The factor of `X` in an odd first-kind Chebyshev polynomial. -/
noncomputable def linearFactor (n : ℕ) : ℤ[X] :=
  (Polynomial.Chebyshev.T ℤ (n : ℤ)).divX

/-- The square factor in the lower endpoint at the odd index `2k+1`. -/
noncomputable def endpointFactor (k : ℕ) : ℤ[X] :=
  Polynomial.Chebyshev.U ℤ (k : ℤ) + Polynomial.Chebyshev.U ℤ ((k : ℤ) - 1)

/-- The prime-square characterization over signed integers, including zero. -/
theorem powerful_iff_prime_sq_dvd (x : ℤ) :
    Powerful x ↔ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ x → (p : ℤ) ^ 2 ∣ x := by
  simp only [Powerful, powerful_iff_prime_sq_divides, ← Int.natCast_dvd,
    Int.natCast_pow]

private theorem U_norm (k : ℕ) :
    Polynomial.Chebyshev.U ℤ (k : ℤ) ^ 2 +
        Polynomial.Chebyshev.U ℤ ((k : ℤ) - 1) ^ 2 -
        2 * X * Polynomial.Chebyshev.U ℤ (k : ℤ) *
          Polynomial.Chebyshev.U ℤ ((k : ℤ) - 1) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Polynomial.Chebyshev.U_add_one ℤ (k : ℤ)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [h]
    linear_combination ih

/-- Uniform odd-index endpoint identity. No valuation assertion is made. -/
theorem odd_endpoint_factorization (k : ℕ) :
    Polynomial.Chebyshev.T ℤ (2 * (k : ℤ) + 1) - 1 =
      (X - 1) * endpointFactor k ^ 2 := by
  have h := Polynomial.Chebyshev.T_mul_T ℤ ((k : ℤ) + 1) (k : ℤ)
  have h1 := Polynomial.Chebyshev.T_eq_X_mul_U_sub_U ℤ ((k : ℤ) - 1)
  have h0 := Polynomial.Chebyshev.T_eq_U_sub_X_mul_U (R := ℤ) (k : ℤ)
  have hn := U_norm k
  have hi : (k : ℤ) + 1 + k = 2 * (k : ℤ) + 1 := by ring
  have hj : (k : ℤ) - 1 + 2 = (k : ℤ) + 1 := by ring
  rw [show (k : ℤ) + 1 - k = 1 by omega, Polynomial.Chebyshev.T_one, hi] at h
  rw [hj, sub_add_cancel] at h1
  dsimp [endpointFactor]
  linear_combination -h + 2 * Polynomial.Chebyshev.T ℤ (k : ℤ) * h1 +
    2 * (X * Polynomial.Chebyshev.U ℤ (k : ℤ) -
      Polynomial.Chebyshev.U ℤ ((k : ℤ) - 1)) * h0 + (X + 1) * hn

/-- At the seed endpoint `1`, the endpoint square factor is the odd index. -/
theorem endpointFactor_eval_one (k : ℕ) :
    (endpointFactor k).eval 1 = 2 * (k : ℤ) + 1 := by
  simp [endpointFactor]
  ring

/-- Every odd-index polynomial has a factor `X`. -/
theorem odd_linear_factorization {n : ℕ} (hn : Odd n) :
    Polynomial.Chebyshev.T ℤ (n : ℤ) = X * linearFactor n := by
  have hn' : Odd (n : ℤ) := by exact_mod_cast hn
  have h0 : (Polynomial.Chebyshev.T ℤ (n : ℤ)).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, Polynomial.Chebyshev.T_eval_zero_of_odd ℤ hn']
  simpa only [linearFactor, h0, C_0, add_zero] using
    (X_mul_divX_add (Polynomial.Chebyshev.T ℤ (n : ℤ))).symm

/-- The linear coefficient is the index times an integer unit. -/
theorem linearFactor_eval_zero {n : ℕ} (hn : Odd n) :
    (linearFactor n).eval 0 =
      (n : ℤ) * (((n : ℤ) - 1) / 2).negOnePow := by
  have hn' : Odd (n : ℤ) := by exact_mod_cast hn
  have he : Even ((n : ℤ) - 1) := hn'.sub_odd odd_one
  calc
    (linearFactor n).eval 0 = (Polynomial.Chebyshev.T ℤ (n : ℤ)).coeff 1 := by
      simp only [← coeff_zero_eq_eval_zero, linearFactor, coeff_divX, zero_add]
    _ = (derivative (Polynomial.Chebyshev.T ℤ (n : ℤ))).eval 0 := by
      simp only [← coeff_zero_eq_eval_zero, coeff_derivative, Nat.cast_zero, zero_add,
        mul_one]
    _ = (n : ℤ) * (((n : ℤ) - 1) / 2).negOnePow := by
      rw [Polynomial.Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast,
        Polynomial.Chebyshev.U_eval_zero_of_even ℤ he]
      norm_cast

/-- Integer evaluation of the odd-index factorization. -/
theorem cheb_eq_mul_linearFactor {n : ℕ} (hn : Odd n) (x : ℤ) :
    cheb n x = x * (linearFactor n).eval x := by
  simp only [cheb, odd_linear_factorization hn, eval_mul, eval_X]

/-- Frobenius congruence for the complete polynomial at any odd prime index. -/
theorem prime_polynomial_zmod {q : ℕ} (hq : q.Prime) (hodd : Odd q) :
    Polynomial.Chebyshev.T (ZMod q) (q : ℤ) = (X : (ZMod q)[X]) ^ q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by
    intro h
    subst q
    norm_num at hodd
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact hq.ne_one h
    · exact hq2 h
  haveI : NeZero (2 : ZMod q) := ⟨h2⟩
  have hd : derivative (Polynomial.Chebyshev.T (ZMod q) (q : ℤ)) = 0 := by
    rw [Polynomial.Chebyshev.T_derivative_eq_U]
    have hc : (q : (ZMod q)[X]) = 0 := by
      rw [← C_eq_natCast, ZMod.natCast_self, C_0]
    simp only [Int.cast_natCast, hc, zero_mul]
  have hdeg : (Polynomial.Chebyshev.T (ZMod q) (q : ℤ)).natDegree = q := by
    simp
  have hodd' : Odd (q : ℤ) := by exact_mod_cast hodd
  have h0 : (Polynomial.Chebyshev.T (ZMod q) (q : ℤ)).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero,
      Polynomial.Chebyshev.T_eval_zero_of_odd (ZMod q) hodd']
  ext n
  by_cases hnq : n = q
  · subst n
    calc
      (Polynomial.Chebyshev.T (ZMod q) (q : ℤ)).coeff q =
          (Polynomial.Chebyshev.T (ZMod q) (q : ℤ)).leadingCoeff := by
        simpa only [hdeg] using
          (coeff_natDegree (p := Polynomial.Chebyshev.T (ZMod q) (q : ℤ)))
      _ = 1 := by
        rw [Polynomial.Chebyshev.leadingCoeff_T, Int.natAbs_natCast]
        exact ZMod.pow_card_sub_one_eq_one h2
      _ = ((X : (ZMod q)[X]) ^ q).coeff q := by simp
  · by_cases hn0 : n = 0
    · subst n
      simp [h0, hnq]
    · by_cases hnlt : n < q
      · have hns : n - 1 + 1 = n := by omega
        have hdc := congrArg (fun P : (ZMod q)[X] => P.coeff (n - 1)) hd
        dsimp only at hdc
        rw [coeff_derivative, coeff_zero] at hdc
        have hcast : ((n - 1 : ℕ) : ZMod q) + 1 = (n : ZMod q) := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            congrArg (fun m : ℕ => (m : ZMod q)) hns
        rw [hns, hcast] at hdc
        have hnc : (n : ZMod q) ≠ 0 := by
          intro hn
          exact (Nat.not_dvd_of_pos_of_lt (by omega) hnlt)
            ((ZMod.natCast_eq_zero_iff n q).mp hn)
        have hz := (mul_eq_zero.mp hdc).resolve_right hnc
        simp [hz, hnq]
      · have hnlarge : q < n := by omega
        have hz : (Polynomial.Chebyshev.T (ZMod q) (q : ℤ)).coeff n = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hnlarge)
        simp [hz, hnq]

/-- At integer arguments the prime-index map is the identity modulo its index prime. -/
theorem cheb_mod_prime {q : ℕ} (hq : q.Prime) (hodd : Odd q) (x : ℤ) :
    (cheb q x : ZMod q) = (x : ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  change algebraMap ℤ (ZMod q) ((Polynomial.Chebyshev.T ℤ (q : ℤ)).eval x) = _
  rw [Polynomial.Chebyshev.algebraMap_eval_T, prime_polynomial_zmod hq hodd,
    eval_pow, eval_X]
  exact ZMod.pow_card _

/-- Prime-index evaluation cannot create divisibility by the index prime
in any prescribed residue class (in particular at `0`, `1`, or `-1`). -/
theorem prime_dvd_cheb_sub_iff {q : ℕ} (hq : q.Prime) (hodd : Odd q) (x a : ℤ) :
    (q : ℤ) ∣ cheb q x - a ↔ (q : ℤ) ∣ x - a := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    Int.cast_sub, Int.cast_sub, cheb_mod_prime hq hodd]

/-- Odd-index evaluation is an odd function over the integers. -/
theorem cheb_neg {n : ℕ} (hn : Odd n) (x : ℤ) :
    cheb n (-x) = -cheb n x := by
  have hn' : Odd (n : ℤ) := by exact_mod_cast hn
  simp [cheb, Polynomial.Chebyshev.T_eval_neg, Int.negOnePow_odd _ hn']

@[simp]
theorem powerful_neg (x : ℤ) : Powerful (-x) ↔ Powerful x := by
  simp [Powerful]

/-- Lower endpoint factorization evaluated over `ℤ`. -/
theorem cheb_odd_sub_one (k : ℕ) (x : ℤ) :
    cheb (2 * k + 1) x - 1 = (x - 1) * (endpointFactor k).eval x ^ 2 := by
  have h := congrArg (eval x) (odd_endpoint_factorization k)
  simpa only [cheb, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    eval_sub, eval_one, eval_mul, eval_X, eval_pow] using h

/-- Upper endpoint factorization evaluated over `ℤ`. -/
theorem cheb_odd_add_one (k : ℕ) (x : ℤ) :
    cheb (2 * k + 1) x + 1 = (x + 1) * (endpointFactor k).eval (-x) ^ 2 := by
  have h := cheb_odd_sub_one k (-x)
  rw [cheb_neg (show Odd (2 * k + 1) from ⟨k, rfl⟩)] at h
  linear_combination -h

/-- If the input is divisible by `d`, the odd-index linear factor is divisible
by `d` exactly when the index is. This applies also to composite `d`. -/
theorem linearFactor_eval_dvd_iff {n : ℕ} (hn : Odd n) {d x : ℤ} (hdx : d ∣ x) :
    d ∣ (linearFactor n).eval x ↔ d ∣ (n : ℤ) := by
  have hd : d ∣ (linearFactor n).eval x - (linearFactor n).eval 0 :=
    dvd_trans (by simpa only [sub_zero] using hdx)
      (sub_dvd_eval_sub x 0 (linearFactor n))
  rw [dvd_iff_dvd_of_dvd_sub hd, linearFactor_eval_zero hn]
  exact (Units.isUnit (((n : ℤ) - 1) / 2).negOnePow).dvd_mul_right

/-- At a divisor of the seed endpoint, only a divisor of the odd index can
divide its endpoint square factor. -/
theorem endpointFactor_eval_dvd_iff (k : ℕ) {d x : ℤ} (hdx : d ∣ x - 1) :
    d ∣ (endpointFactor k).eval x ↔ d ∣ 2 * (k : ℤ) + 1 := by
  have hd : d ∣ (endpointFactor k).eval x - (endpointFactor k).eval 1 :=
    dvd_trans hdx (sub_dvd_eval_sub x 1 (endpointFactor k))
  rw [dvd_iff_dvd_of_dvd_sub hd, endpointFactor_eval_one]

private theorem prime_eq_of_int_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : (p : ℤ) ∣ (q : ℤ)) : p = q := by
  exact ((hq.dvd_iff_eq hp.ne_one).mp (Int.natCast_dvd_natCast.mp h)).symm

/-- Extraction from a powerful integer product whose only possible shared
prime is `q`, provided the extracted factor is already saturated at `q`. -/
theorem powerful_of_single_overlap {a b : ℤ} {q : ℕ} (h : Powerful (a * b))
    (hoverlap : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b → p = q)
    (hsat : (q : ℤ) ∣ a → (q : ℤ) ^ 2 ∣ a) : Powerful a := by
  apply (powerful_iff_prime_sq_dvd a).mpr
  intro p hp hpa
  by_cases hpq : p = q
  · subst p
    exact hsat hpa
  · have hpb : ¬(p : ℤ) ∣ b := by
      intro hh
      exact hpq (hoverlap p hp hpa hh)
    have hcop : IsCoprime (p : ℤ) b :=
      (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hpb
    exact (hcop.pow_left (m := 2)).dvd_of_dvd_mul_right
      ((powerful_iff_prime_sq_dvd (a * b)).mp h p hp (dvd_mul_of_dvd_left hpa b))

/-- Powerfulness of the middle entry descends through a prime-index map
if the seed middle entry has no valuation-one obstruction at that prime. -/
theorem powerful_of_cheb_prime {q : ℕ} (hq : q.Prime) (hodd : Odd q) {x : ℤ}
    (h : Powerful (cheb q x)) (hsat : (q : ℤ) ∣ x → (q : ℤ) ^ 2 ∣ x) :
    Powerful x := by
  apply powerful_of_single_overlap (q := q) (b := (linearFactor q).eval x)
    (by simpa only [cheb_eq_mul_linearFactor hodd] using h) ?_ hsat
  intro p hp hpx hpf
  exact prime_eq_of_int_dvd hp hq ((linearFactor_eval_dvd_iff hodd hpx).mp hpf)

/-- Full lower-endpoint extraction, with the sole possible repair prime
stated explicitly. -/
theorem powerful_sub_one_of_cheb_prime {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {x : ℤ} (h : Powerful (cheb q x - 1))
    (hsat : (q : ℤ) ∣ x - 1 → (q : ℤ) ^ 2 ∣ x - 1) : Powerful (x - 1) := by
  obtain ⟨k, hk⟩ := hodd
  have hk' : (q : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  have hf : cheb q x - 1 = (x - 1) * (endpointFactor k).eval x ^ 2 := by
    rw [hk, cheb_odd_sub_one]
  apply powerful_of_single_overlap (q := q) (b := (endpointFactor k).eval x ^ 2)
    (hf ▸ h) ?_ hsat
  intro p hp hpx hpf
  have hpr : (p : ℤ) ∣ (endpointFactor k).eval x :=
    (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hpf
  have hpq := (endpointFactor_eval_dvd_iff k hpx).mp hpr
  rw [← hk'] at hpq
  exact prime_eq_of_int_dvd hp hq hpq

/-- Full upper-endpoint extraction, obtained by the odd reflection. -/
theorem powerful_add_one_of_cheb_prime {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {x : ℤ} (h : Powerful (cheb q x + 1))
    (hsat : (q : ℤ) ∣ x + 1 → (q : ℤ) ^ 2 ∣ x + 1) : Powerful (x + 1) := by
  have hf : cheb q (-x) - 1 = -(cheb q x + 1) := by
    rw [cheb_neg hodd]
    ring
  have hx : -x - 1 = -(x + 1) := by ring
  have hh : Powerful (cheb q (-x) - 1) := by
    rw [hf, powerful_neg]
    exact h
  have hs : (q : ℤ) ∣ -x - 1 → (q : ℤ) ^ 2 ∣ -x - 1 := by
    simpa only [hx, dvd_neg] using hsat
  have ht := powerful_sub_one_of_cheb_prime hq hodd hh hs
  simpa only [hx, powerful_neg] using ht

/-- A middle entry produced by one prime-index step is already saturated
at the index prime. Only square divisibility is needed here. -/
theorem prime_sq_dvd_cheb_of_dvd {q : ℕ} (hq : q.Prime) (hodd : Odd q) (x : ℤ)
    (h : (q : ℤ) ∣ cheb q x) : (q : ℤ) ^ 2 ∣ cheb q x := by
  have hx : (q : ℤ) ∣ x := by
    simpa only [sub_zero] using (prime_dvd_cheb_sub_iff hq hodd x 0).mp
      (by simpa only [sub_zero] using h)
  have hr : (q : ℤ) ∣ (linearFactor q).eval x :=
    (linearFactor_eval_dvd_iff hodd hx).mpr (dvd_refl _)
  rw [cheb_eq_mul_linearFactor hodd, pow_two]
  exact mul_dvd_mul hx hr

/-- A lower endpoint produced by one step has at least three factors of
the index prime whenever that prime divides it. Extra cancellation is allowed. -/
theorem prime_cube_dvd_cheb_sub_one_of_dvd {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (x : ℤ) (h : (q : ℤ) ∣ cheb q x - 1) : (q : ℤ) ^ 3 ∣ cheb q x - 1 := by
  have hx := (prime_dvd_cheb_sub_iff hq hodd x 1).mp h
  obtain ⟨k, hk⟩ := hodd
  have hk' : (q : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  have hr : (q : ℤ) ∣ (endpointFactor k).eval x := by
    apply (endpointFactor_eval_dvd_iff k hx).mpr
    rw [← hk']
  have hf : cheb q x - 1 = (x - 1) * (endpointFactor k).eval x ^ 2 := by
    rw [hk, cheb_odd_sub_one]
  rw [hf]
  convert mul_dvd_mul hx (pow_dvd_pow_of_dvd hr 2) using 1
  ring

/-- The reflected upper-endpoint saturation statement, also valid at `q = 3`. -/
theorem prime_cube_dvd_cheb_add_one_of_dvd {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (x : ℤ) (h : (q : ℤ) ∣ cheb q x + 1) : (q : ℤ) ^ 3 ∣ cheb q x + 1 := by
  have hf : cheb q (-x) - 1 = -(cheb q x + 1) := by
    rw [cheb_neg hodd]
    ring
  have hh : (q : ℤ) ∣ cheb q (-x) - 1 := by simpa only [hf, dvd_neg] using h
  have ht := prime_cube_dvd_cheb_sub_one_of_dvd hq hodd (-x) hh
  simpa only [hf, dvd_neg] using ht

/-- Prime-index full transfer once the three seed entries are saturated at
that prime. All transfer identities used above are proved in this module. -/
theorem full_of_cheb_prime {q : ℕ} (hq : q.Prime) (hodd : Odd q) {x : ℤ}
    (h : Full (cheb q x))
    (hminus : (q : ℤ) ∣ x - 1 → (q : ℤ) ^ 2 ∣ x - 1)
    (hcenter : (q : ℤ) ∣ x → (q : ℤ) ^ 2 ∣ x)
    (hplus : (q : ℤ) ∣ x + 1 → (q : ℤ) ^ 2 ∣ x + 1) : Full x := by
  exact ⟨powerful_sub_one_of_cheb_prime hq hodd h.1 hminus,
    powerful_of_cheb_prime hq hodd h.2.1 hcenter,
    powerful_add_one_of_cheb_prime hq hodd h.2.2 hplus⟩

/-- With a full large center, these three index-prime conditions are the
exact criterion for the seed to be full. No conditions at other primes remain. -/
theorem full_seed_iff_q_saturated {q : ℕ} (hq : q.Prime) (hodd : Odd q) {x : ℤ}
    (h : Full (cheb q x)) :
    Full x ↔
      ((q : ℤ) ∣ x - 1 → (q : ℤ) ^ 2 ∣ x - 1) ∧
      ((q : ℤ) ∣ x → (q : ℤ) ^ 2 ∣ x) ∧
      ((q : ℤ) ∣ x + 1 → (q : ℤ) ^ 2 ∣ x + 1) := by
  constructor
  · intro hx
    exact ⟨(powerful_iff_prime_sq_dvd (x - 1)).mp hx.1 q hq,
      (powerful_iff_prime_sq_dvd x).mp hx.2.1 q hq,
      (powerful_iff_prime_sq_dvd (x + 1)).mp hx.2.2 q hq⟩
  · rintro ⟨hminus, hcenter, hplus⟩
    exact full_of_cheb_prime hq hodd h hminus hcenter hplus

/-- Unconditional full prime-square-index descent over all signed integers.
No evenness, positivity, endpoint criterion, or exact valuation premise is needed. -/
theorem full_of_prime_square_index {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    (u : ℤ) (h : Full (cheb q (cheb q u))) : Full (cheb q u) := by
  apply full_of_cheb_prime hq hodd h
  · intro hqv
    exact dvd_trans (pow_dvd_pow (q : ℤ) (by decide : 2 ≤ 3))
      (prime_cube_dvd_cheb_sub_one_of_dvd hq hodd u hqv)
  · exact prime_sq_dvd_cheb_of_dvd hq hodd u
  · intro hqv
    exact dvd_trans (pow_dvd_pow (q : ℤ) (by decide : 2 ≤ 3))
      (prime_cube_dvd_cheb_add_one_of_dvd hq hodd u hqv)

@[simp]
theorem cheb_zero (x : ℤ) : cheb 0 x = 1 := by simp [cheb]

@[simp]
theorem cheb_one (x : ℤ) : cheb 1 x = x := by simp [cheb]

/-- The usual recurrence, without any truncating natural-number subtraction. -/
theorem cheb_add_two (n : ℕ) (x : ℤ) :
    cheb (n + 2) x = 2 * x * cheb (n + 1) x - cheb n x := by
  simp only [cheb, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    Polynomial.Chebyshev.T_add_two, eval_sub, eval_mul, eval_ofNat, eval_X]

private theorem cheb_positive_step {x : ℤ} (hx : 2 ≤ x) (n : ℕ) :
    0 < cheb n x ∧ cheb n x < cheb (n + 1) x := by
  induction n with
  | zero => simp only [cheb_zero, zero_add, cheb_one]; omega
  | succ n ih =>
    have hrec := cheb_add_two n x
    constructor
    · exact lt_trans ih.1 ih.2
    · change cheb (n + 1) x < cheb (n + 2) x
      nlinarith [mul_nonneg (show 0 ≤ x - 1 by omega)
        (show 0 ≤ cheb (n + 1) x by omega)]

/-- Chebyshev values are strictly increasing in the natural index at every
integer seed at least two. -/
theorem strictMono_cheb_index {x : ℤ} (hx : 2 ≤ x) :
    StrictMono (fun n : ℕ => cheb n x) := by
  exact strictMono_nat_of_lt_succ (fun n => (cheb_positive_step hx n).2)

/-- Every natural-index value is strictly positive for a seed at least two. -/
theorem cheb_pos {x : ℤ} (hx : 2 ≤ x) (n : ℕ) : 0 < cheb n x :=
  (cheb_positive_step hx n).1

/-- Nonzero-index values are at least their positive integer seed. -/
theorem cheb_ge_self {x : ℤ} (hx : 2 ≤ x) {n : ℕ} (hn : 1 ≤ n) : x ≤ cheb n x := by
  simpa only [cheb_one] using (strictMono_cheb_index hx).monotone hn

/-- Every index at least two gives a strict increase over the integer seed. -/
theorem cheb_gt_self {x : ℤ} (hx : 2 ≤ x) {n : ℕ} (hn : 2 ≤ n) : x < cheb n x := by
  simpa only [cheb_one] using (strictMono_cheb_index hx) (show 1 < n by omega)

/-- Any divisor of the seed divides its value at every odd index. In particular
this preserves divisibility by four without using powerfulness. -/
theorem dvd_cheb_of_dvd {n : ℕ} (hn : Odd n) {d x : ℤ} (h : d ∣ x) : d ∣ cheb n x := by
  rw [cheb_eq_mul_linearFactor hn]
  exact dvd_mul_of_dvd_left h _

/-- Even integer seeds stay even at odd indices. -/
theorem cheb_even {n : ℕ} (hn : Odd n) {x : ℤ} (hx : Even x) : Even (cheb n x) := by
  exact even_iff_two_dvd.mpr (dvd_cheb_of_dvd hn (even_iff_two_dvd.mp hx))

/-- Exact conversion to the natural centered triple, with no absolute-value
or subtraction ambiguity. -/
theorem full_natCast_iff {m : ℕ} (hm : 1 ≤ m) :
    Full (m : ℤ) ↔ Nat.Powerful (m - 1) ∧ Nat.Powerful m ∧ Nat.Powerful (m + 1) := by
  have hs : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := Int.natCast_sub hm
  have ha : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by simp
  simp only [Full, Powerful, ← hs, ← ha, Int.natAbs_natCast]

/-- The positive signed and natural formulations of full powerfulness agree. -/
theorem full_iff_toNat {x : ℤ} (hx : 1 ≤ x) :
    Full x ↔ Nat.Powerful (x.toNat - 1) ∧ Nat.Powerful x.toNat ∧
      Nat.Powerful (x.toNat + 1) := by
  have hn : 1 ≤ x.toNat := by omega
  simpa only [Int.toNat_of_nonneg (show 0 ≤ x by omega)] using (full_natCast_iff hn)

/-- Every positive full integer center at least two is divisible by four. -/
theorem full_four_dvd {x : ℤ} (hx : 2 ≤ x) (h : Full x) : (4 : ℤ) ∣ x := by
  have hn : 2 ≤ x.toNat := by omega
  have ht := (full_iff_toNat (show 1 ≤ x by omega)).mp h
  have h1 : x.toNat - 1 + 1 = x.toNat := by omega
  have h2 : x.toNat - 1 + 2 = x.toNat + 1 := by omega
  have htr : Nat.Powerful (x.toNat - 1) ∧ Nat.Powerful (x.toNat - 1 + 1) ∧
      Nat.Powerful (x.toNat - 1 + 2) := by
    simpa only [h1, h2] using ht
  have hmod := triple_mod_four htr
  have hd : 4 ∣ x.toNat := Nat.dvd_of_mod_eq_zero (by omega)
  have hd' : (4 : ℤ) ∣ (x.toNat : ℤ) := by exact_mod_cast hd
  simpa only [Int.toNat_of_nonneg (show 0 ≤ x by omega)] using hd'

/-- A strict denominator-one descent of the *full* triple. This is stronger
than the even-seed target: evenness of `u` is unnecessary, and the new center
is divisible by four unconditionally once the large center is full. -/
theorem prime_square_index_full_descent {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {u : ℤ} (hu : 4 ≤ u) (h : Full (cheb q (cheb q u))) :
    Full (cheb q u) ∧ 4 ≤ cheb q u ∧ 0 < cheb q u ∧
      cheb q u < cheb q (cheb q u) ∧ (4 : ℤ) ∣ cheb q u := by
  have hf := full_of_prime_square_index hq hodd u h
  have hv : 4 ≤ cheb q u := le_trans hu
    (cheb_ge_self (show 2 ≤ u by omega) (show 1 ≤ q by have := hq.two_le; omega))
  exact ⟨hf, hv, by omega, cheb_gt_self (by omega) hq.two_le,
    full_four_dvd (by omega) hf⟩

/-- Natural-number version of the strict full descent. All evaluations are
still performed in `ℤ`; positivity proves that the `toNat` conversions are exact. -/
theorem prime_square_index_nat_full_descent {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {u : ℤ} (hu : 4 ≤ u)
    (h : Nat.Powerful ((cheb q (cheb q u)).toNat - 1) ∧
      Nat.Powerful (cheb q (cheb q u)).toNat ∧
      Nat.Powerful ((cheb q (cheb q u)).toNat + 1)) :
    (Nat.Powerful ((cheb q u).toNat - 1) ∧ Nat.Powerful (cheb q u).toNat ∧
      Nat.Powerful ((cheb q u).toNat + 1)) ∧
      4 ≤ (cheb q u).toNat ∧ (cheb q u).toNat < (cheb q (cheb q u)).toNat ∧
      4 ∣ (cheb q u).toNat := by
  have hv : 4 ≤ cheb q u := le_trans hu
    (cheb_ge_self (by omega) (show 1 ≤ q by have := hq.two_le; omega))
  have ht : 4 ≤ cheb q (cheb q u) := le_trans hv
    (cheb_ge_self (by omega) (show 1 ≤ q by have := hq.two_le; omega))
  have hf := (full_iff_toNat (show 1 ≤ cheb q (cheb q u) by omega)).mpr h
  obtain ⟨hfull, _, _, hsmall, hd⟩ := prime_square_index_full_descent hq hodd hu hf
  refine ⟨(full_iff_toNat (by omega)).mp hfull, by omega, by omega, ?_⟩
  apply Int.natCast_dvd_natCast.mp
  simpa only [Int.toNat_of_nonneg (show 0 ≤ cheb q u by omega)] using hd

/-- First-kind composition over `ℤ`, for use in dividing a natural index. -/
theorem cheb_mul (m n : ℕ) (x : ℤ) :
    cheb (m * n) x = cheb m (cheb n x) := by
  simp only [cheb, Nat.cast_mul, Polynomial.Chebyshev.T_mul, eval_comp]

/-- Leastness among positive full integer centers. No existence is asserted. -/
def LeastFull (t : ℤ) : Prop :=
  4 ≤ t ∧ Full t ∧ ∀ s : ℤ, 4 ≤ s → Full s → t ≤ s

/-- A least full center cannot have a prime-square Chebyshev representation
with an integer seed at least four. -/
theorem least_full_not_prime_square_index {t u : ℤ} (ht : LeastFull t) (hu : 4 ≤ u)
    {q : ℕ} (hq : q.Prime) (hodd : Odd q) (heq : t = cheb q (cheb q u)) : False := by
  have hf : Full (cheb q (cheb q u)) := heq ▸ ht.2.1
  obtain ⟨hvfull, hv, _, hsmall, _⟩ := prime_square_index_full_descent hq hodd hu hf
  have hle := ht.2.2 (cheb q u) hv hvfull
  rw [← heq] at hsmall
  exact (not_le_of_gt hsmall) hle

/-- Conditional on leastness, the complete odd Chebyshev index is squarefree.
This does not require constructing a fundamental Pell unit or its index. -/
theorem least_full_index_squarefree {t r : ℤ} {n : ℕ} (hr : 4 ≤ r) (hn : Odd n)
    (ht : LeastFull t) (heq : t = cheb n r) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro q hq hqd
  have hqdiv : q ∣ n := dvd_trans (dvd_mul_right q q) hqd
  have hqodd : Odd q := hn.of_dvd_nat hqdiv
  obtain ⟨m, hm⟩ := hqd
  have hnpos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  have hmpos : 1 ≤ m := by
    by_contra hh
    have hm0 : m = 0 := by omega
    simp [hm0] at hm
    omega
  have hu : 4 ≤ cheb m r := le_trans hr (cheb_ge_self (by omega) hmpos)
  have heq' : t = cheb q (cheb q (cheb m r)) := by
    rw [heq, hm, cheb_mul, cheb_mul]
  exact least_full_not_prime_square_index ht hu hq hqodd heq'

end Erdos364.ChebyshevDescent

-- Exhaustive axiom audit of all public declarations in this helper.
#print axioms Erdos364.ChebyshevDescent.cheb
#print axioms Erdos364.ChebyshevDescent.Powerful
#print axioms Erdos364.ChebyshevDescent.Full
#print axioms Erdos364.ChebyshevDescent.linearFactor
#print axioms Erdos364.ChebyshevDescent.endpointFactor
#print axioms Erdos364.ChebyshevDescent.powerful_iff_prime_sq_dvd
#print axioms Erdos364.ChebyshevDescent.odd_endpoint_factorization
#print axioms Erdos364.ChebyshevDescent.endpointFactor_eval_one
#print axioms Erdos364.ChebyshevDescent.odd_linear_factorization
#print axioms Erdos364.ChebyshevDescent.linearFactor_eval_zero
#print axioms Erdos364.ChebyshevDescent.cheb_eq_mul_linearFactor
#print axioms Erdos364.ChebyshevDescent.prime_polynomial_zmod
#print axioms Erdos364.ChebyshevDescent.cheb_mod_prime
#print axioms Erdos364.ChebyshevDescent.prime_dvd_cheb_sub_iff
#print axioms Erdos364.ChebyshevDescent.cheb_neg
#print axioms Erdos364.ChebyshevDescent.powerful_neg
#print axioms Erdos364.ChebyshevDescent.cheb_odd_sub_one
#print axioms Erdos364.ChebyshevDescent.cheb_odd_add_one
#print axioms Erdos364.ChebyshevDescent.linearFactor_eval_dvd_iff
#print axioms Erdos364.ChebyshevDescent.endpointFactor_eval_dvd_iff
#print axioms Erdos364.ChebyshevDescent.powerful_of_single_overlap
#print axioms Erdos364.ChebyshevDescent.powerful_of_cheb_prime
#print axioms Erdos364.ChebyshevDescent.powerful_sub_one_of_cheb_prime
#print axioms Erdos364.ChebyshevDescent.powerful_add_one_of_cheb_prime
#print axioms Erdos364.ChebyshevDescent.prime_sq_dvd_cheb_of_dvd
#print axioms Erdos364.ChebyshevDescent.prime_cube_dvd_cheb_sub_one_of_dvd
#print axioms Erdos364.ChebyshevDescent.prime_cube_dvd_cheb_add_one_of_dvd
#print axioms Erdos364.ChebyshevDescent.full_of_cheb_prime
#print axioms Erdos364.ChebyshevDescent.full_seed_iff_q_saturated
#print axioms Erdos364.ChebyshevDescent.full_of_prime_square_index
#print axioms Erdos364.ChebyshevDescent.cheb_zero
#print axioms Erdos364.ChebyshevDescent.cheb_one
#print axioms Erdos364.ChebyshevDescent.cheb_add_two
#print axioms Erdos364.ChebyshevDescent.strictMono_cheb_index
#print axioms Erdos364.ChebyshevDescent.cheb_pos
#print axioms Erdos364.ChebyshevDescent.cheb_ge_self
#print axioms Erdos364.ChebyshevDescent.cheb_gt_self
#print axioms Erdos364.ChebyshevDescent.dvd_cheb_of_dvd
#print axioms Erdos364.ChebyshevDescent.cheb_even
#print axioms Erdos364.ChebyshevDescent.full_natCast_iff
#print axioms Erdos364.ChebyshevDescent.full_iff_toNat
#print axioms Erdos364.ChebyshevDescent.full_four_dvd
#print axioms Erdos364.ChebyshevDescent.prime_square_index_full_descent
#print axioms Erdos364.ChebyshevDescent.prime_square_index_nat_full_descent
#print axioms Erdos364.ChebyshevDescent.cheb_mul
#print axioms Erdos364.ChebyshevDescent.LeastFull
#print axioms Erdos364.ChebyshevDescent.least_full_not_prime_square_index
#print axioms Erdos364.ChebyshevDescent.least_full_index_squarefree
