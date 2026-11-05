import Submission.PellSaturation
import Submission.ChebyshevDescent

/-!
# Critical-prime terminal-index descent

An unconditional supporting helper for Erdős problem 364, not a settlement.
The specification is not imported and existing helpers are left unchanged.

For every odd prime q, powerfulness of the middle entry of a prime-index
Chebyshev step implies powerfulness of its seed middle entry away from q. An
odd-index Chebyshev polynomial has linear term ±n X and a remainder divisible
by X³. At q | x this gives the
precise equivalence q² | x iff q³ | T_q(x). Thus exact exponent two in the
large middle entry is the only *central* prime-step obstruction. Full descent
additionally requires powerful seed endpoints; the Pell saturation index
supplies those endpoints when q is removed outside that index. Leastness
then forces exact exponent two at every prime of the residual cofactor. The
actual canonical Pell bridge gives n = I*m, positive odd squarefree coprime
factors, m² | t, coprimality with all three cube kernels, and m | b.

No exact endpoint valuation is asserted, including at q = 3. Natural index
one is retained throughout. All statements about an actual least full center
are conditional on its full powerfulness and leastness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos364.CriticalIndexDescent

open Polynomial Erdos364.PowerfulStructure Erdos364.ChebyshevDescent
open Erdos364.PellBridge Erdos364.PellSaturation

/-- The quadratic coefficient of an odd Chebyshev polynomial vanishes. -/
theorem odd_cheb_coeff_two {n : ℕ} (hn : Odd n) :
    (Polynomial.Chebyshev.T ℤ (n : ℤ)).coeff 2 = 0 := by
  have hn' : Odd (n : ℤ) := by exact_mod_cast hn
  have h := Polynomial.Chebyshev.iterate_derivative_T_eval_zero_recurrence
    (R := ℤ) (n : ℤ) 0
  simp only [Function.iterate_zero, Function.iterate_succ_apply',
    Function.id_def, Polynomial.Chebyshev.T_eval_zero_of_odd ℤ hn',
    mul_zero, ← coeff_zero_eq_eval_zero, coeff_derivative] at h
  norm_num at h
  omega

/-- Uniform odd-index expansion with the exact signed linear coefficient. -/
theorem odd_cheb_cubic_expansion {n : ℕ} (hn : Odd n) :
    ∃ P : ℤ[X], Polynomial.Chebyshev.T ℤ (n : ℤ) =
      C ((n : ℤ) * (((n : ℤ) - 1) / 2).negOnePow) * X + X ^ 3 * P := by
  have hn' : Odd (n : ℤ) := by exact_mod_cast hn
  have hc0 : (Polynomial.Chebyshev.T ℤ (n : ℤ)).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, Polynomial.Chebyshev.T_eval_zero_of_odd ℤ hn']
  have hc1 : (Polynomial.Chebyshev.T ℤ (n : ℤ)).coeff 1 =
      (n : ℤ) * (((n : ℤ) - 1) / 2).negOnePow := by
    simpa only [← coeff_zero_eq_eval_zero, linearFactor, coeff_divX, zero_add]
      using linearFactor_eval_zero hn
  have hdiv : (X : ℤ[X]) ^ 3 ∣ Polynomial.Chebyshev.T ℤ (n : ℤ) -
      C ((n : ℤ) * (((n : ℤ) - 1) / 2).negOnePow) * X := by
    apply X_pow_dvd_iff.mpr
    intro j hj
    interval_cases j <;> simp [hc0, hc1, odd_cheb_coeff_two hn]
  obtain ⟨P, hP⟩ := hdiv
  exact ⟨P, by linear_combination hP⟩

/-- Integer evaluation of the uniform cubic-remainder expansion. -/
theorem cheb_cubic_expansion {n : ℕ} (hn : Odd n) (x : ℤ) :
    ∃ z : ℤ, cheb n x =
      (n : ℤ) * (((n : ℤ) - 1) / 2).negOnePow * x + x ^ 3 * z := by
  obtain ⟨P, hP⟩ := odd_cheb_cubic_expansion hn
  exact ⟨P.eval x, by simpa only [cheb, eval_add, eval_mul, eval_C, eval_X,
    eval_pow] using congrArg (eval x) hP⟩

/-- At q | x, T_q(x) is congruent to its signed linear term modulo q³.
Primality is unnecessary for this congruence. -/
theorem prime_cube_dvd_cheb_sub_linear {q : ℕ} (hodd : Odd q) {x : ℤ}
    (hqx : (q : ℤ) ∣ x) :
    (q : ℤ) ^ 3 ∣ cheb q x -
      (q : ℤ) * (((q : ℤ) - 1) / 2).negOnePow * x := by
  obtain ⟨z, hz⟩ := cheb_cubic_expansion hodd x
  rw [hz, add_sub_cancel_left]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hqx 3) z

/-- For every odd prime and every signed seed divisible by it, seed
square-divisibility is equivalent to output cube-divisibility. -/
theorem prime_sq_dvd_seed_iff_cube_dvd_cheb {q : ℕ} (hq : q.Prime)
    (hodd : Odd q) {x : ℤ} (hqx : (q : ℤ) ∣ x) :
    (q : ℤ) ^ 2 ∣ x ↔ (q : ℤ) ^ 3 ∣ cheb q x := by
  have hcong := prime_cube_dvd_cheb_sub_linear hodd hqx
  have hunit : IsUnit ((((q : ℤ) - 1) / 2).negOnePow : ℤ) :=
    Units.isUnit _
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  calc
    (q : ℤ) ^ 2 ∣ x ↔ (q : ℤ) ^ 3 ∣ (q : ℤ) * x := by
      rw [show (q : ℤ) ^ 3 = (q : ℤ) * (q : ℤ) ^ 2 by ring,
        mul_dvd_mul_iff_left hq0]
    _ ↔ (q : ℤ) ^ 3 ∣ (q : ℤ) *
        (((q : ℤ) - 1) / 2).negOnePow * x := by
      rw [mul_assoc, mul_comm ((((q : ℤ) - 1) / 2).negOnePow : ℤ) x,
        ← mul_assoc, hunit.dvd_mul_right]
    _ ↔ (q : ℤ) ^ 3 ∣ cheb q x :=
      (dvd_iff_dvd_of_dvd_sub hcong).symm

/-- Exact exponent two, expressed without choosing a valuation. -/
def ExactTwo (q : ℕ) (x : ℤ) : Prop :=
  (q : ℤ) ^ 2 ∣ x ∧ ¬(q : ℤ) ^ 3 ∣ x

/-- Prime-square saturation at all primes except the indicated prime. -/
def PowerfulAway (q : ℕ) (x : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ q → (p : ℤ) ∣ x → (p : ℤ) ^ 2 ∣ x

/-- The Frobenius congruence detects divisibility by the index prime in both directions. -/
theorem prime_dvd_cheb_iff {q : ℕ} (hq : q.Prime) (hodd : Odd q) (x : ℤ) :
    (q : ℤ) ∣ cheb q x ↔ (q : ℤ) ∣ x := by
  simpa only [sub_zero] using prime_dvd_cheb_sub_iff hq hodd x 0

/-- All prime-square conditions away from q descend from the powerful middle entry. -/
theorem powerful_away_of_cheb_prime {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {x : ℤ} (h : Powerful (cheb q x)) : PowerfulAway q x := by
  intro p hp hpq hpx
  have hpf : ¬(p : ℤ) ∣ (linearFactor q).eval x := by
    intro hpd
    have hpqd : p ∣ q := Int.natCast_dvd_natCast.mp
      ((linearFactor_eval_dvd_iff hodd hpx).mp hpd)
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpqd)
  have hcop : IsCoprime (p : ℤ) ((linearFactor q).eval x) :=
    (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hpf
  have hsq := (powerful_iff_prime_sq_dvd (cheb q x)).mp h p hp
    (dvd_cheb_of_dvd hodd hpx)
  rw [cheb_eq_mul_linearFactor hodd] at hsq
  exact (hcop.pow_left (m := 2)).dvd_of_dvd_mul_right hsq

/-- An output has exact exponent two at q exactly when its seed has exponent one there. -/
theorem prime_exact_two_cheb_iff {q : ℕ} (hq : q.Prime) (hodd : Odd q) (x : ℤ) :
    ExactTwo q (cheb q x) ↔ (q : ℤ) ∣ x ∧ ¬(q : ℤ) ^ 2 ∣ x := by
  constructor
  · rintro ⟨hsq, hcube⟩
    have hqx : (q : ℤ) ∣ x := (prime_dvd_cheb_iff hq hodd x).mp
      (dvd_trans (dvd_pow_self (q : ℤ) (by decide : 2 ≠ 0)) hsq)
    exact ⟨hqx, fun hx => hcube
      ((prime_sq_dvd_seed_iff_cube_dvd_cheb hq hodd hqx).mp hx)⟩
  · rintro ⟨hqx, hx⟩
    exact ⟨prime_sq_dvd_cheb_of_dvd hq hodd x
      ((prime_dvd_cheb_iff hq hodd x).mpr hqx),
      fun hc => hx ((prime_sq_dvd_seed_iff_cube_dvd_cheb hq hodd hqx).mpr hc)⟩

/-- With a powerful output middle entry, exact exponent two is the only
obstruction to powerfulness of the seed middle entry. -/
theorem powerful_seed_iff_not_exact_two {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {x : ℤ} (h : Powerful (cheb q x)) :
    Powerful x ↔ ¬ExactTwo q (cheb q x) := by
  constructor
  · intro hx he
    obtain ⟨hqx, hqxsq⟩ := (prime_exact_two_cheb_iff hq hodd x).mp he
    exact hqxsq ((powerful_iff_prime_sq_dvd x).mp hx q hq hqx)
  · intro he
    apply powerful_of_cheb_prime hq hodd h
    intro hqx
    by_contra hqxsq
    exact he ((prime_exact_two_cheb_iff hq hodd x).mpr ⟨hqx, hqxsq⟩)

/-- Once the seed endpoints are powerful, the central exact-two condition
exactly characterizes failure of full descent. -/
theorem full_seed_iff_not_exact_two_of_endpoints {q : ℕ} (hq : q.Prime)
    (hodd : Odd q) {x : ℤ} (h : Full (cheb q x))
    (hends : Powerful (x - 1) ∧ Powerful (x + 1)) :
    Full x ↔ ¬ExactTwo q (cheb q x) := by
  constructor
  · intro hx
    exact (powerful_seed_iff_not_exact_two hq hodd h.2.1).mp hx.2.1
  · intro he
    exact ⟨hends.1, (powerful_seed_iff_not_exact_two hq hodd h.2.1).mpr he, hends.2⟩

/-- Strict full descent when the seed endpoints are already powerful and the
large middle entry has no exact-two obstruction at the index prime. -/
theorem full_prime_step_descent {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {x : ℤ} (hx : 4 ≤ x) (h : Full (cheb q x))
    (hends : Powerful (x - 1) ∧ Powerful (x + 1))
    (hnot : ¬ExactTwo q (cheb q x)) :
    Full x ∧ 0 < x ∧ x < cheb q x ∧ (4 : ℤ) ∣ x := by
  have hf := (full_seed_iff_not_exact_two_of_endpoints hq hodd h hends).mpr hnot
  exact ⟨hf, by omega, cheb_gt_self (by omega) hq.two_le,
    full_four_dvd (by omega) hf⟩

/-- All needed quotient data, including positivity and parity. -/
theorem prime_division_index_data {n q : ℕ} (hn : Odd n)
    (hq : q.Prime) (hqn : q ∣ n) :
    0 < n / q ∧ Odd (n / q) ∧ n / q < n ∧ n = q * (n / q) := by
  have hnpos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  exact ⟨Nat.div_pos (Nat.le_of_dvd hnpos hqn) hq.pos,
    hn.of_dvd_nat (Nat.div_dvd_of_dvd hqn), Nat.div_lt_self hnpos hq.one_lt,
    (Nat.mul_div_cancel' hqn).symm⟩

/-- Removing a prime outside I preserves divisibility by I. -/
theorem index_dvd_quotient_of_prime_not_dvd {I n q : ℕ} (hq : q.Prime)
    (hIn : I ∣ n) (hqn : q ∣ n) (hqI : ¬q ∣ I) : I ∣ n / q := by
  have hcop : Nat.Coprime I q := (hq.coprime_iff_not_dvd.mpr hqI).symm
  apply hcop.dvd_of_dvd_mul_left
  simpa only [Nat.mul_div_cancel' hqn] using hIn

/-- Endpoint saturation survives removal of every prime outside I. -/
theorem pell_prime_removal_endpoints {d : ℕ} (hdpos : 0 < d) (hd : Squarefree d)
    (ε : Pell.Solution₁ (d : ℤ)) (hx4 : (4 : ℤ) ∣ ε.x) {n q : ℕ}
    (hn : Odd n) (hq : q.Prime) (hqn : q ∣ n)
    (hIn : saturationIndex ε ∣ n) (hqI : ¬q ∣ saturationIndex ε) :
    Powerful (cheb (n / q) ε.x - 1) ∧ Powerful (cheb (n / q) ε.x + 1) := by
  have hquot := prime_division_index_data hn hq hqn
  have hdiv := index_dvd_quotient_of_prime_not_dvd hq hIn hqn hqI
  simpa only [pell_x_pow_eq_cheb] using
    (pell_pow_endpoints_iff_index_dvd hdpos hd ε hx4 hquot.2.1).mpr hdiv

/-- The lower prime-removal center is positive, at least four, and strictly smaller. -/
theorem pell_prime_removal_center_data {d : ℕ} (ε : Pell.Solution₁ (d : ℤ))
    (hx : 4 ≤ ε.x) (hx4 : (4 : ℤ) ∣ ε.x) {n q : ℕ}
    (hn : Odd n) (hq : q.Prime) (hqn : q ∣ n) :
    0 < n / q ∧ Odd (n / q) ∧ 4 ≤ cheb (n / q) ε.x ∧
      0 < cheb (n / q) ε.x ∧ (4 : ℤ) ∣ cheb (n / q) ε.x ∧
      cheb (n / q) ε.x < cheb n ε.x ∧
      cheb n ε.x = cheb q (cheb (n / q) ε.x) := by
  obtain ⟨hpos, hodd, hlt, hfac⟩ := prime_division_index_data hn hq hqn
  have hlow : 4 ≤ cheb (n / q) ε.x :=
    le_trans hx (cheb_ge_self (by omega) (by omega : 1 ≤ n / q))
  refine ⟨hpos, hodd, hlow, by omega, dvd_cheb_of_dvd hodd hx4,
    strictMono_cheb_index (by omega) hlt, ?_⟩
  nth_rw 1 [hfac]
  exact cheb_mul q (n / q) ε.x

/-- Exact central obstruction for a full Pell prime step with q outside I. -/
theorem full_pell_prime_removal_iff_not_exact_two {d : ℕ}
    (hdpos : 0 < d) (hd : Squarefree d) (ε : Pell.Solution₁ (d : ℤ))
    (hx4 : (4 : ℤ) ∣ ε.x) {n q : ℕ} (hn : Odd n)
    (hq : q.Prime) (hqn : q ∣ n) (hIn : saturationIndex ε ∣ n)
    (hqI : ¬q ∣ saturationIndex ε) (hfull : Full (cheb n ε.x)) :
    Full (cheb (n / q) ε.x) ↔ ¬ExactTwo q (cheb n ε.x) := by
  have hcomp : cheb n ε.x = cheb q (cheb (n / q) ε.x) := by
    nth_rw 1 [(Nat.mul_div_cancel' hqn).symm]
    exact cheb_mul q (n / q) ε.x
  have hqodd : Odd q := hn.of_dvd_nat hqn
  rw [hcomp] at hfull ⊢
  exact full_seed_iff_not_exact_two_of_endpoints hq hqodd hfull
    (pell_prime_removal_endpoints hdpos hd ε hx4 hn hq hqn hIn hqI)

/-- At a least full center, a removable prime must have exact central exponent two. -/
theorem least_full_critical_prime {d : ℕ} (hdpos : 0 < d) (hd : Squarefree d)
    (ε : Pell.Solution₁ (d : ℤ)) (hx : 4 ≤ ε.x) (hx4 : (4 : ℤ) ∣ ε.x)
    {t : ℤ} {n q : ℕ} (hn : Odd n) (ht : LeastFull t) (heq : t = cheb n ε.x)
    (hq : q.Prime) (hqn : q ∣ n) (hqI : ¬q ∣ saturationIndex ε) :
    ExactTwo q t := by
  have hIn := (least_full_index_decomposition hdpos hd ε hx hx4 hn ht heq).1
  have hdata := pell_prime_removal_center_data ε hx hx4 hn hq hqn
  have hfull : Full (cheb n ε.x) := heq ▸ ht.2.1
  have hiff := full_pell_prime_removal_iff_not_exact_two hdpos hd ε hx4 hn hq
    hqn hIn hqI hfull
  by_contra hnot
  have hlowfull : Full (cheb (n / q) ε.x) := hiff.mpr (by simpa only [← heq] using hnot)
  have hle := ht.2.2 (cheb (n / q) ε.x) hdata.2.2.1 hlowfull
  have hlt : cheb (n / q) ε.x < t := by simpa only [← heq] using hdata.2.2.2.2.2.1
  exact (not_le_of_gt hlt) hle

/-- The failed smaller center has an exponent-one obstruction only at q. -/
theorem least_full_prime_removal_classification {d : ℕ} (hdpos : 0 < d)
    (hd : Squarefree d) (ε : Pell.Solution₁ (d : ℤ))
    (hx : 4 ≤ ε.x) (hx4 : (4 : ℤ) ∣ ε.x) {t : ℤ} {n q : ℕ}
    (hn : Odd n) (ht : LeastFull t) (heq : t = cheb n ε.x)
    (hq : q.Prime) (hqn : q ∣ n) (hqI : ¬q ∣ saturationIndex ε) :
    (Powerful (cheb (n / q) ε.x - 1) ∧ Powerful (cheb (n / q) ε.x + 1)) ∧
      PowerfulAway q (cheb (n / q) ε.x) ∧
      (q : ℤ) ∣ cheb (n / q) ε.x ∧ ¬(q : ℤ) ^ 2 ∣ cheb (n / q) ε.x ∧
      ¬Full (cheb (n / q) ε.x) ∧ ExactTwo q t := by
  have hIn := (least_full_index_decomposition hdpos hd ε hx hx4 hn ht heq).1
  have he := least_full_critical_prime hdpos hd ε hx hx4 hn ht heq hq hqn hqI
  have hcomp := (pell_prime_removal_center_data ε hx hx4 hn hq hqn).2.2.2.2.2.2
  have hqt : ExactTwo q (cheb q (cheb (n / q) ε.x)) := by
    simpa only [heq, hcomp] using he
  have hseed := (prime_exact_two_cheb_iff hq (hn.of_dvd_nat hqn)
    (cheb (n / q) ε.x)).mp hqt
  have hfull : Full (cheb q (cheb (n / q) ε.x)) := by
    simpa only [heq, hcomp] using ht.2.1
  refine ⟨pell_prime_removal_endpoints hdpos hd ε hx4 hn hq hqn hIn hqI,
    powerful_away_of_cheb_prime hq (hn.of_dvd_nat hqn) hfull.2.1,
    hseed.1, hseed.2, ?_, he⟩
  intro hf
  exact hseed.2 ((powerful_iff_prime_sq_dvd _).mp hf.2.1 q hq hseed.1)

/-- Assemble simultaneous prime-square divisibilities across a squarefree cofactor. -/
theorem squarefree_sq_dvd_of_prime_sq_dvd {m y : ℕ} (hm : Squarefree m)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → q ^ 2 ∣ y) : m ^ 2 ∣ y := by
  by_cases hy : y = 0
  · simp [hy]
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hm.ne_zero) hy).mp
  intro q
  rw [Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  by_cases hq : q.Prime
  · by_cases hqm : q ∣ m
    · rw [Nat.factorization_eq_one_of_squarefree hm hq hqm, mul_one]
      exact (hq.pow_dvd_iff_le_factorization hy).mp (h q hq hqm)
    · simp only [Nat.factorization_eq_zero_of_not_dvd hqm, mul_zero, Nat.zero_le]
  · simp only [Nat.factorization_eq_zero_of_not_prime m hq, mul_zero, Nat.zero_le]

/-- Signed version of simultaneous square-divisibility. -/
theorem squarefree_int_sq_dvd_of_exact_two {m : ℕ} (hm : Squarefree m) {t : ℤ}
    (h : ∀ q : ℕ, q.Prime → q ∣ m → ExactTwo q t) : (m : ℤ) ^ 2 ∣ t := by
  have hd : m ^ 2 ∣ t.natAbs := squarefree_sq_dvd_of_prime_sq_dvd hm (by
    intro q hq hqm
    simpa only [← Int.natCast_pow, Int.natCast_dvd] using (h q hq hqm).1)
  simpa only [← Int.natCast_pow, Int.natCast_dvd] using hd

/-- Necessary terminal-index arithmetic; it does not assert powerfulness or
leastness. Index and cofactor one are allowed. -/
def TerminalIndex {d : ℕ} (t : ℤ) (ε : Pell.Solution₁ (d : ℤ)) (n m : ℕ) : Prop :=
  (0 < n ∧ Odd n ∧ Squarefree n ∧ t = cheb n ε.x) ∧
  (0 < saturationIndex ε ∧ Odd (saturationIndex ε) ∧ Squarefree (saturationIndex ε)) ∧
  (0 < m ∧ Odd m ∧ Squarefree m ∧ Nat.Coprime (saturationIndex ε) m) ∧
  n = saturationIndex ε * m ∧
  (∀ q : ℕ, q.Prime → q ∣ m → ExactTwo q t) ∧ (m : ℤ) ^ 2 ∣ t

/-- Least-full classification at an arbitrary positive squarefree raw Pell seed. -/
theorem least_full_terminal_index {d : ℕ} (hdpos : 0 < d) (hd : Squarefree d)
    (ε : Pell.Solution₁ (d : ℤ)) (hx : 4 ≤ ε.x) (hx4 : (4 : ℤ) ∣ ε.x)
    {t : ℤ} {n : ℕ} (hn : Odd n) (ht : LeastFull t) (heq : t = cheb n ε.x) :
    ∃ m : ℕ, TerminalIndex t ε n m := by
  obtain ⟨hIn, m, hfac, hIsf, hmsf, hcop⟩ :=
    least_full_index_decomposition hdpos hd ε hx hx4 hn ht heq
  have hnpos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  have hIpos := (saturationIndex_pos_dvd hdpos ε).1
  have hmpos : 0 < m := by
    by_contra hh
    have hm0 : m = 0 := by omega
    simp only [hm0, mul_zero] at hfac
    omega
  have hmn : m ∣ n := hfac ▸ dvd_mul_left m (saturationIndex ε)
  have hcrit : ∀ q : ℕ, q.Prime → q ∣ m → ExactTwo q t := by
    intro q hq hqm
    have hqn := dvd_trans hqm hmn
    have hqI : ¬q ∣ saturationIndex ε := by
      intro hdiv
      exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hdiv hqm) hcop
    exact least_full_critical_prime hdpos hd ε hx hx4 hn ht heq hq hqn hqI
  exact ⟨m, ⟨hnpos, hn, least_full_index_squarefree hx hn ht heq, heq⟩,
    ⟨hIpos, hn.of_dvd_nat hIn, hIsf⟩,
    ⟨hmpos, hn.of_dvd_nat hmn, hmsf, hcop⟩, hfac, hcrit,
    squarefree_int_sq_dvd_of_exact_two hmsf hcrit⟩

/-- A center without any exact-two prime has no extra terminal cofactor. -/
theorem least_full_index_eq_saturation_of_no_exact_two {d : ℕ}
    (hdpos : 0 < d) (hd : Squarefree d) (ε : Pell.Solution₁ (d : ℤ))
    (hx : 4 ≤ ε.x) (hx4 : (4 : ℤ) ∣ ε.x) {t : ℤ} {n : ℕ}
    (hn : Odd n) (ht : LeastFull t) (heq : t = cheb n ε.x)
    (hno : ∀ q : ℕ, q.Prime → ¬ExactTwo q t) : n = saturationIndex ε := by
  obtain ⟨m, hterm⟩ := least_full_terminal_index hdpos hd ε hx hx4 hn ht heq
  have hm1 : m = 1 := by
    by_contra hm
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm
    exact hno q hq (hterm.2.2.2.2.1 q hq hqm)
  simpa only [hm1, mul_one] using hterm.2.2.2.1

/-- Critical primes avoid the cube kernel and occur in the square factor. -/
theorem critical_cofactor_middle_factors {t m B b : ℕ} (hm : Squarefree m)
    (hrep : t = B ^ 3 * b ^ 2)
    (hcrit : ∀ q : ℕ, q.Prime → q ∣ m → ExactTwo q (t : ℤ)) :
    m ^ 2 ∣ t ∧ Nat.Coprime m B ∧ m ∣ b := by
  have hmsq : m ^ 2 ∣ t := by
    exact_mod_cast squarefree_int_sq_dvd_of_exact_two hm hcrit
  have hcop : Nat.Coprime m B := by
    apply Nat.coprime_of_dvd
    intro q hq hqm hqB
    have hc : q ^ 3 ∣ t := by
      rw [hrep]
      exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hqB 3) _
    have hc' : (q : ℤ) ^ 3 ∣ (t : ℤ) := by exact_mod_cast hc
    exact (hcrit q hq hqm).2 hc'
  have hmbsq : m ^ 2 ∣ b ^ 2 :=
    ((hcop.pow_left 2).pow_right 3).dvd_of_dvd_mul_left (hrep ▸ hmsq)
  exact ⟨hmsq, hcop, (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hmbsq⟩

/-- In the actual canonical triple, every critical cofactor avoids all three
cube kernels, not only the middle kernel. -/
theorem canonical_critical_cofactor {t A B C a b c m : ℕ}
    (ht : LeastNatFull t) (hc : CanonicalTriple t A B C a b c) (hm : Squarefree m)
    (hcrit : ∀ q : ℕ, q.Prime → q ∣ m → ExactTwo q (t : ℤ)) :
    m ^ 2 ∣ t ∧ Nat.Coprime m B ∧ Nat.Coprime m (A * B * C) ∧ m ∣ b := by
  obtain ⟨_, _, _, heA, heB, heC⟩ := hc
  obtain ⟨hmsq, hcopB, hmb⟩ := critical_cofactor_middle_factors hm heB hcrit
  have hmt : m ∣ t := dvd_trans (dvd_pow_self m (by decide : 2 ≠ 0)) hmsq
  have hdA : A ∣ t - 1 := by
    rw [heA]
    exact dvd_mul_of_dvd_left (dvd_pow_self A (by decide : 3 ≠ 0)) _
  have hdC : C ∣ t + 1 := by
    rw [heC]
    exact dvd_mul_of_dvd_left (dvd_pow_self C (by decide : 3 ≠ 0)) _
  have hp := (natFull_properties (show 2 ≤ t by have := ht.1; omega) ht.2.1).2.2.2
  have hcopA : Nat.Coprime m A := ((hp.1.coprime_dvd_left hdA).coprime_dvd_right hmt).symm
  have hcopC : Nat.Coprime m C := (hp.2.2.coprime_dvd_left hmt).coprime_dvd_right hdC
  exact ⟨hmsq, hcopB, (hcopA.mul_right hcopB).mul_right hcopC, hmb⟩

/-- A terminal cofactor is exactly the quotient by the saturation index. -/
theorem terminalIndex_cofactor_eq_quotient {d : ℕ} {t : ℤ}
    {ε : Pell.Solution₁ (d : ℤ)} {n m : ℕ} (h : TerminalIndex t ε n m) :
    m = n / saturationIndex ε := by
  rw [h.2.2.2.1, Nat.mul_div_cancel_left m h.2.1.1]

/-- Cofactor prime divisors are precisely index primes lying outside I. -/
theorem terminalIndex_prime_divisors_iff {d q : ℕ} {t : ℤ}
    {ε : Pell.Solution₁ (d : ℤ)} {n m : ℕ} (h : TerminalIndex t ε n m)
    (hq : q.Prime) : q ∣ m ↔ q ∣ n ∧ ¬q ∣ saturationIndex ε := by
  constructor
  · intro hqm
    refine ⟨dvd_trans hqm (h.2.2.2.1 ▸ dvd_mul_left m (saturationIndex ε)), ?_⟩
    intro hqI
    exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqI hqm) h.2.2.1.2.2.2
  · rintro ⟨hqn, hqI⟩
    rw [h.2.2.2.1] at hqn
    exact (hq.dvd_mul.mp hqn).resolve_left hqI

/-- Saturation exhausts the full index exactly when the terminal cofactor is one. -/
theorem terminalIndex_eq_saturation_iff {d : ℕ} {t : ℤ}
    {ε : Pell.Solution₁ (d : ℤ)} {n m : ℕ} (h : TerminalIndex t ε n m) :
    n = saturationIndex ε ↔ m = 1 := by
  constructor
  · intro hn
    have he : saturationIndex ε * m = saturationIndex ε * 1 := by
      rw [← h.2.2.2.1, hn, mul_one]
    exact mul_left_cancel₀ h.2.1.1.ne' he
  · intro hm
    simpa only [hm, mul_one] using h.2.2.2.1

/-- The complete actual canonical Pell witness with its terminal index. No
existence is asserted, and no least-full or index-one case is excluded. -/
def TerminalPellFull (t : ℕ) : Prop :=
  ∃ A B C a b c d : ℕ, CanonicalTriple t A B C a b c ∧ d = A * C ∧
    0 < d ∧ Squarefree d ∧ d % 8 = 7 ∧ ¬IsSquare (d : ℤ) ∧
    ∃ ε : Pell.Solution₁ (d : ℤ), ∃ n m : ℕ,
      FundamentalPower t d a c ε n ∧ TerminalIndex (t : ℤ) ε n m ∧
      m ^ 2 ∣ t ∧ Nat.Coprime m B ∧ Nat.Coprime m (A * B * C) ∧ m ∣ b

/-- Every actual least natural full center supplies all canonical factors,
coordinates, fundamental seed, and terminal critical-prime data. -/
theorem leastNatFull_exists_terminal_pell {t : ℕ} (ht : LeastNatFull t) :
    TerminalPellFull t := by
  obtain ⟨A, B, C, a, b, c, d, hc, hd, hdpos, hdsf, hdmod, hdns, ε, n, hpower, _⟩ :=
    leastNatFull_exists_squarefree_pell ht
  obtain ⟨m, hterm⟩ := least_full_terminal_index hdpos hdsf ε hpower.2.1.1
    hpower.2.1.2.2.1 hpower.2.2.1.2 (leastNatFull_iff_leastFull.mp ht)
    hpower.2.2.2.2.2
  have hcanon := canonical_critical_cofactor ht hc hterm.2.2.1.2.2.1
    hterm.2.2.2.2.1
  exact ⟨A, B, C, a, b, c, d, hc, hd, hdpos, hdsf, hdmod, hdns,
    ε, n, m, hpower, hterm, hcanon⟩

/-- Raw-seed projection of the actual canonical least-full terminal witness. -/
theorem leastNatFull_exists_terminal_index {t : ℕ} (ht : LeastNatFull t) :
    ∃ d : ℕ, 0 < d ∧ Squarefree d ∧ d % 8 = 7 ∧ ¬IsSquare (d : ℤ) ∧
      ∃ ε : Pell.Solution₁ (d : ℤ), Pell.IsFundamental ε ∧
        4 ≤ ε.x ∧ (4 : ℤ) ∣ ε.x ∧ 0 < ε.y ∧
        ∃ n m : ℕ, TerminalIndex (t : ℤ) ε n m := by
  obtain ⟨A, B, C, a, b, c, d, _, _, hdpos, hdsf, hdmod, hdns,
    ε, n, m, hpower, hterm, _⟩ := leastNatFull_exists_terminal_pell ht
  exact ⟨d, hdpos, hdsf, hdmod, hdns, ε, hpower.1, hpower.2.1.1,
    hpower.2.1.2.2.1, hpower.2.1.2.2.2.1, n, m, hterm⟩

/-- Actual powerful-triple existence is equivalent to the least full canonical
terminal witness. This is a structural reduction, not an EMW settlement. -/
theorem exists_powerful_triple_iff_exists_least_terminal_pell :
    (∃ k : ℕ, Nat.Powerful k ∧ Nat.Powerful (k + 1) ∧ Nat.Powerful (k + 2)) ↔
      ∃ t : ℕ, LeastNatFull t ∧ TerminalPellFull t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_leastNatFull_of_exists_powerful_triple h
    exact ⟨t, ht, leastNatFull_exists_terminal_pell ht⟩
  · rintro ⟨t, ht, _⟩
    have h1 : t - 1 + 1 = t := by have := ht.1; omega
    have h2 : t - 1 + 2 = t + 1 := by have := ht.1; omega
    refine ⟨t - 1, ?_⟩
    simpa only [h1, h2] using ht.2.1

end Erdos364.CriticalIndexDescent

-- Exhaustive audit of every public definition and theorem.
#print axioms Erdos364.CriticalIndexDescent.odd_cheb_coeff_two
#print axioms Erdos364.CriticalIndexDescent.odd_cheb_cubic_expansion
#print axioms Erdos364.CriticalIndexDescent.cheb_cubic_expansion
#print axioms Erdos364.CriticalIndexDescent.prime_cube_dvd_cheb_sub_linear
#print axioms Erdos364.CriticalIndexDescent.prime_sq_dvd_seed_iff_cube_dvd_cheb
#print axioms Erdos364.CriticalIndexDescent.ExactTwo
#print axioms Erdos364.CriticalIndexDescent.PowerfulAway
#print axioms Erdos364.CriticalIndexDescent.prime_dvd_cheb_iff
#print axioms Erdos364.CriticalIndexDescent.powerful_away_of_cheb_prime
#print axioms Erdos364.CriticalIndexDescent.prime_exact_two_cheb_iff
#print axioms Erdos364.CriticalIndexDescent.powerful_seed_iff_not_exact_two
#print axioms Erdos364.CriticalIndexDescent.full_seed_iff_not_exact_two_of_endpoints
#print axioms Erdos364.CriticalIndexDescent.full_prime_step_descent
#print axioms Erdos364.CriticalIndexDescent.prime_division_index_data
#print axioms Erdos364.CriticalIndexDescent.index_dvd_quotient_of_prime_not_dvd
#print axioms Erdos364.CriticalIndexDescent.pell_prime_removal_endpoints
#print axioms Erdos364.CriticalIndexDescent.pell_prime_removal_center_data
#print axioms Erdos364.CriticalIndexDescent.full_pell_prime_removal_iff_not_exact_two
#print axioms Erdos364.CriticalIndexDescent.least_full_critical_prime
#print axioms Erdos364.CriticalIndexDescent.least_full_prime_removal_classification
#print axioms Erdos364.CriticalIndexDescent.squarefree_sq_dvd_of_prime_sq_dvd
#print axioms Erdos364.CriticalIndexDescent.squarefree_int_sq_dvd_of_exact_two
#print axioms Erdos364.CriticalIndexDescent.TerminalIndex
#print axioms Erdos364.CriticalIndexDescent.least_full_terminal_index
#print axioms Erdos364.CriticalIndexDescent.least_full_index_eq_saturation_of_no_exact_two
#print axioms Erdos364.CriticalIndexDescent.critical_cofactor_middle_factors
#print axioms Erdos364.CriticalIndexDescent.canonical_critical_cofactor
#print axioms Erdos364.CriticalIndexDescent.terminalIndex_cofactor_eq_quotient
#print axioms Erdos364.CriticalIndexDescent.terminalIndex_prime_divisors_iff
#print axioms Erdos364.CriticalIndexDescent.terminalIndex_eq_saturation_iff
#print axioms Erdos364.CriticalIndexDescent.TerminalPellFull
#print axioms Erdos364.CriticalIndexDescent.leastNatFull_exists_terminal_pell
#print axioms Erdos364.CriticalIndexDescent.leastNatFull_exists_terminal_index
#print axioms Erdos364.CriticalIndexDescent.exists_powerful_triple_iff_exists_least_terminal_pell
