import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators Int

-- Generalized binomial coefficient $\binom{r}{k}$ for $r \in \mathbb{Z}, k \in \mathbb{N}$.
-- We use the definition $\binom{r}{k} = \frac{\prod_{i=0}^{k-1} (r-i)}{k!}$ and rely on
-- the known property that this division results in an integer.
def generalized_choose_int (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) / (k.factorial : ℤ)

-- Helper definition for the generalized coefficient formula.
/--
The $k$-th power series coefficient of $c(x)^r$: $\frac{r}{r+k}\binom{r+2k-1}{k}$.
This expression is known to be an integer for all $r \in \mathbb{Z}$.
-/
def generalized_catalan_coefficient (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else
    let num_choose := generalized_choose_int (r + 2 * (k : ℤ) - 1) k
    let denominator : ℤ := r + k
    -- The division is exact because the coefficient is an integer.
    -- We rely on integer division to compute the result.
    (r * num_choose) / denominator

/--
The generalized sequence $a_m(n)$ is the $n$-th order Taylor polynomial (centered at 0) of $c(x)^{m \cdot n}$ evaluated at $x=1$.
$$a_m(n) = \sum_{k=0}^n [x^k] c(x)^{m n}$$
-/
def a_gen (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    let r : ℤ := m * (n : ℤ)
    Finset.sum (range (n + 1)) fun k =>
      generalized_catalan_coefficient r k

/--
A333096: The $n$-th order Taylor polynomial (centered at 0) of $c(x)^{4n}$ evaluated at $x=1$, where $c(x) = \frac{1 - \sqrt{1 - 4x}}{2x}$ is the o.g.f. of the sequence of Catalan numbers $A000108$.
The sequence is defined by the formula:
$$a(n) = \sum_{k = 0}^n \frac{4n}{4n+k}\binom{4n+2k-1}{k} \quad \text{for } n \ge 1$$
and $a(0) = 1.$$
The summand is the $k$-th coefficient of the power series $c(x)^{4n}$, which is an integer.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.sum (range (n + 1)) fun k =>
      let m : ℕ := 4 * n
      let numerator : ℕ := m * (m + 2 * k - 1).choose k
      let denominator : ℕ := m + k
      -- Since the combinatorial identity guarantees exact divisibility, Nat division is equivalent to integer division.
      numerator / denominator


namespace OEIS333096

open Polynomial PowerSeries

lemma choose_factorial (r : ℤ) (k : ℕ) :
    (k.factorial : ℤ) * Ring.choose r k =
      ∏ i ∈ Finset.range k, (r - (i : ℤ)) := by
  rw [← descPochhammer_eval_eq_prod_range]
  simpa [Polynomial.eval_eq_smeval, nsmul_eq_mul] using
    (Ring.descPochhammer_eq_factorial_smul_choose r k).symm

lemma generalized_choose_eq (r : ℤ) (k : ℕ) :
    generalized_choose_int r k = Ring.choose r k := by
  unfold generalized_choose_int
  split_ifs with hk
  · subst k; simp [Ring.choose_zero_right]
  · rw [← choose_factorial]
    exact Int.mul_ediv_cancel_left _ (by exact_mod_cast k.factorial_ne_zero)

lemma choose_step_mul (r : ℤ) (k : ℕ) :
    (k + 1 : ℤ) * Ring.choose r (k + 1) =
      (r - k) * Ring.choose r k := by
  apply mul_left_cancel₀ (show (k.factorial : ℤ) ≠ 0 by exact_mod_cast k.factorial_ne_zero)
  rw [← mul_assoc, ← Nat.cast_succ, ← Nat.cast_mul, Nat.mul_comm k.factorial,
    ← Nat.factorial_succ, choose_factorial, Finset.prod_range_succ]
  rw [mul_left_comm, choose_factorial, mul_comm]

lemma choose_top_mul (r : ℤ) (k : ℕ) :
    (r - k) * Ring.choose r k = r * Ring.choose (r - 1) k := by
  induction k with
  | zero => simp [Ring.choose_zero_right]
  | succ k ih =>
    apply mul_left_cancel₀ (show (k + 1 : ℤ) ≠ 0 by omega)
    calc
      (k + 1 : ℤ) * ((r - (k + 1)) * Ring.choose r (k + 1)) =
          (r - (k + 1)) * ((r - k) * Ring.choose r k) := by
        rw [mul_left_comm, choose_step_mul]
      _ = r * ((r - 1 - k) * Ring.choose (r - 1) k) := by rw [ih]; ring
      _ = (k + 1 : ℤ) * (r * Ring.choose (r - 1) (k + 1)) := by
        rw [← choose_step_mul]; ring

-- This polynomial form of the Catalan coefficient also makes sense at its
-- removable singularity.
def catCoeff (r : ℤ) (k : ℕ) : ℤ :=
  Ring.choose (r + 2 * k) k -
    if k = 0 then 0 else 2 * Ring.choose (r + 2 * k - 1) (k - 1)

lemma catCoeff_zero (r : ℤ) : catCoeff r 0 = 1 := by
  simp [catCoeff, Ring.choose_zero_right]

lemma catCoeff_succ (r : ℤ) (k : ℕ) :
    catCoeff r (k+1) = Ring.choose (r + 2 * (k+1) - 1) (k+1) -
      Ring.choose (r + 2 * (k+1) - 1) k := by
  simp only [catCoeff, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [show r + 2 * ((k+1 : ℕ) : ℤ) = (r + 2 * (k+1) - 1) + 1 by push_cast; ring,
    Ring.choose_succ_succ]
  ring

lemma catCoeff_mul (r : ℤ) (k : ℕ) :
    (r + k) * catCoeff r k = r * Ring.choose (r + 2 * k - 1) k := by
  cases k with
  | zero => simp [catCoeff_zero, Ring.choose_zero_right]
  | succ k =>
    rw [catCoeff_succ]
    have h := choose_step_mul (r + 2 * (k+1) - 1) k
    push_cast at *
    nlinarith

lemma catCoeff_singular (k : ℕ) (hk : k ≠ 0) : catCoeff (-(k : ℤ)) k = -1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [catCoeff_succ]
  have he : (-(↑(j+1) : ℤ) + 2 * (j+1) - 1) = j := by push_cast; ring
  rw [he, Ring.choose_natCast, Ring.choose_natCast]
  simp

lemma generalized_cat_eq (r : ℤ) (k : ℕ) :
    generalized_catalan_coefficient r k = catCoeff r k +
      if k ≠ 0 ∧ r + k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k; simp [generalized_catalan_coefficient, catCoeff_zero]
  · simp only [generalized_catalan_coefficient, hk, ↓reduceIte, generalized_choose_eq]
    by_cases hr : r + k = 0
    · have hreq : r = -(k : ℤ) := by omega
      rw [if_pos ⟨hk, hr⟩, hr, Int.ediv_zero, hreq, catCoeff_singular k hk]
      norm_num
    · rw [if_neg (by tauto), add_zero, ← catCoeff_mul]
      exact Int.mul_ediv_cancel_left _ hr

def weight (n : ℕ) : ℤ := if n = 0 then 1 else if n % 3 = 0 then 2 else -1

noncomputable def W : PowerSeries ℤ := PowerSeries.mk weight

lemma W_coeff (n : ℕ) : PowerSeries.coeff n W = weight n := by
  simp [W]

lemma weight_rec (n : ℕ) : weight (n+2) + weight (n+1) + weight n =
    if n = 0 then -1 else 0 := by
  by_cases hn : n = 0
  · subst n; decide
  · have h : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases hrem : n % 3 <;>
      simp [weight, hn, Nat.add_mod, hrem]

lemma W_mul_Q : W * (1 + PowerSeries.X + PowerSeries.X ^ 2) =
    (1 - PowerSeries.X ^ 2 : PowerSeries ℤ) := by
  ext n
  rw [mul_add, mul_add, mul_one]
  simp only [map_add, map_sub]
  cases n with
  | zero => simp [W_coeff, weight]
  | succ n =>
    cases n with
    | zero =>
      have hx : PowerSeries.coeff 1 (W * PowerSeries.X) = PowerSeries.coeff 0 W := by
        simpa only [pow_one] using PowerSeries.coeff_mul_X_pow W 1 0
      simp [W_coeff, weight, hx, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow]
    | succ n =>
      have hx : PowerSeries.coeff (n+1+1) (W * PowerSeries.X) = PowerSeries.coeff (n+1) W := by
        simpa only [pow_one] using PowerSeries.coeff_mul_X_pow W 1 (n+1)
      rw [hx, PowerSeries.coeff_mul_X_pow']
      simp only [show 1 ≤ n+1+1 by omega, show 2 ≤ n+1+1 by omega,
        ↓reduceIte, Nat.add_sub_cancel, show n+1+1-2=n by omega, W_coeff]
      rw [show n+1+1=n+2 by omega, weight_rec]
      by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, PowerSeries.coeff_X_pow, hn]

noncomputable def binSum (A : ℤ) (B : ℕ) : ℤ :=
  PowerSeries.coeff B (W * PowerSeries.binomialSeries ℤ A)

lemma binSum_zero (A : ℤ) : binSum A 0 = 1 := by
  simp [binSum, PowerSeries.coeff_zero_eq_constantCoeff, W, weight]

lemma binSum_step (r : ℤ) (n : ℕ) :
    binSum (r + 2 * (n+1)) (n+1) = binSum (r + 2 * n) n + catCoeff r (n+1) := by
  have h1 (t : ℤ) : PowerSeries.binomialSeries ℤ (t+1) =
      PowerSeries.binomialSeries ℤ t * (1 + PowerSeries.X) := by
    have h : PowerSeries.binomialSeries ℤ (1:ℤ) = 1 + PowerSeries.X := by
      simpa only [Nat.cast_one, pow_one] using
        PowerSeries.binomialSeries_nat (R := ℤ) (A := ℤ) 1
    rw [PowerSeries.binomialSeries_add, h]
  have h2 (t : ℤ) : PowerSeries.binomialSeries ℤ (t+2) =
      PowerSeries.binomialSeries ℤ t * (1 + PowerSeries.X)^2 := by
    have h : PowerSeries.binomialSeries ℤ (2:ℤ) = (1 + PowerSeries.X)^2 := by
      simpa only [Nat.cast_ofNat] using
        PowerSeries.binomialSeries_nat (R := ℤ) (A := ℤ) 2
    rw [PowerSeries.binomialSeries_add, h]
  have hw : W * (1 + PowerSeries.X)^2 =
      PowerSeries.X * W + (1 - PowerSeries.X)*(1 + PowerSeries.X) := by
    have := W_mul_Q
    linear_combination this
  have hs : W * PowerSeries.binomialSeries ℤ (r + 2 * (n+1)) =
      PowerSeries.X * (W * PowerSeries.binomialSeries ℤ (r+2*n)) +
        (1 - PowerSeries.X) * PowerSeries.binomialSeries ℤ (r+2*n+1) := by
    rw [show r+2*(n+1) = (r+2*n)+2 by ring, h2, h1]
    linear_combination PowerSeries.binomialSeries ℤ (r+2*n) * hw
  unfold binSum
  rw [hs, map_add, PowerSeries.coeff_succ_X_mul]
  congr 1
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, catCoeff_succ]
  simp only [PowerSeries.binomialSeries_coeff, zsmul_eq_mul, mul_one, Int.cast_id]
  rw [show r + 2 * (↑n + 1) - 1 = r + 2 * ↑n + 1 by ring]

lemma sum_catCoeff (r : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n+1), catCoeff r k = binSum (r + 2*n) n := by
  induction n with
  | zero => simp [catCoeff_zero, binSum_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simpa only [Nat.cast_add, Nat.cast_one] using (binSum_step r n).symm

lemma a_gen_eq (m : ℤ) (n : ℕ) (hn : 0 < n) :
    a_gen m n = binSum ((m+2)*n) n + if m = -1 then 1 else 0 := by
  rw [a_gen, if_neg (by omega)]
  simp only [generalized_cat_eq]
  rw [Finset.sum_add_distrib, sum_catCoeff]
  have hA : m * (n : ℤ) + 2*n = (m+2)*n := by ring
  rw [hA]
  congr 1
  have hh (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      (k ≠ 0 ∧ m * (n : ℤ) + k = 0) ↔ (m = -1 ∧ k = n) := by
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hnz : (0 : ℤ) < n := by exact_mod_cast hn
    have hkz : (k : ℤ) ≤ n := by exact_mod_cast hkn
    constructor
    · rintro ⟨hk0, he⟩
      have hkpos : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have hm : m = -1 := by
        by_contra hm
        have hcases : m ≤ -2 ∨ 0 ≤ m := by omega
        rcases hcases with hm | hm <;> nlinarith
      refine ⟨hm, ?_⟩
      subst m
      have : (k : ℤ) = n := by linarith
      exact_mod_cast this
    · rintro ⟨rfl, rfl⟩
      exact ⟨by omega, by ring⟩
  trans ∑ k ∈ Finset.range (n+1), if m = -1 ∧ k = n then (1 : ℤ) else 0
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [hh k hk]
  · by_cases hm : m = -1 <;> simp [hm]

end OEIS333096


open Nat Finset BigOperators Int
namespace OEIS333096
open Polynomial

noncomputable def Q : Polynomial ℤ := 1 + X + X^2
lemma Q_monic : Q.Monic := by unfold Q; monicity!
lemma Q_degree : Q.natDegree = 2 := by unfold Q; compute_degree!
lemma Q_ne : Q ≠ 0 := Q_monic.ne_zero
lemma Q_reflect : Q.reflect 2 = Q := by
  ext i
  simp only [coeff_reflect, Q, coeff_add, coeff_one, coeff_X, coeff_X_pow]
  by_cases hi : i ≤ 2
  · interval_cases i <;> norm_num [revAt]
  · simp [revAt, hi]

lemma prime_mod_six (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := by intro h; have := (Nat.dvd_prime hp).mp h; omega
  have h3 : ¬ 3 ∣ p := by intro h; have := (Nat.dvd_prime hp).mp h; omega
  omega

lemma pow_frobenius_at_cubic {R : Type*} [CommRing R] (x : R)
    (hx : 1 + x + x^2 = 0) (p : ℕ) (hp : p % 6 = 1 ∨ p % 6 = 5) :
    (1+x)^p = 1+x^p := by
  have hx3 : x^3 = 1 := by linear_combination (x-1)*hx
  have hy3 : (1+x)^3 = -1 := by linear_combination (x+2)*hx
  have hx6 : x^6 = 1 := by rw [show 6=3*2 by decide, pow_mul, hx3]; simp
  have hy6 : (1+x)^6 = 1 := by rw [show 6=3*2 by decide, pow_mul, hy3]; ring
  have powmod (y : R) (hy : y^6=1) : y^p = y^(p%6) := by
    nth_rw 1 [← Nat.div_add_mod p 6]
    rw [pow_add, pow_mul, hy, one_pow, one_mul]
  rw [powmod x hx6, powmod (1+x) hy6]
  rcases hp with hp | hp
  · simp [hp]
  · rw [hp]
    linear_combination (5*x*(x+1))*hx

lemma Q_dvd_frobenius (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Q ∣ ((1+X)^p - 1 - X^p : Polynomial ℤ) := by
  apply (AdjoinRoot.mk_eq_zero).mp
  have hx : (1 : AdjoinRoot Q) + AdjoinRoot.root Q + (AdjoinRoot.root Q)^2 = 0 := by
    simpa only [Q, map_add, map_pow, map_one, AdjoinRoot.mk_X] using (AdjoinRoot.mk_self (f := Q))
  simp only [map_sub, map_pow, map_add, map_one, AdjoinRoot.mk_X]
  linear_combination pow_frobenius_at_cubic (AdjoinRoot.root Q) hx p (prime_mod_six p hp hp5)

lemma monic_dvd_of_C_mul {D H : Polynomial ℤ} (hD : D.Monic) (c : ℤ)
    (hc : c ≠ 0) (h : D ∣ C c * H) : D ∣ H := by
  apply (modByMonic_eq_zero_iff_dvd hD).mp
  have hz := (modByMonic_eq_zero_iff_dvd hD).mpr h
  rw [← smul_eq_C_mul, smul_modByMonic] at hz
  exact (smul_eq_zero.mp hz).resolve_left hc

lemma reflect_pow (H : Polynomial ℤ) (p : ℕ) (hdeg : H.natDegree ≤ p)
    (h : H.reflect p = H) (j : ℕ) : (H^j).reflect (p*j) = H^j := by
  induction j with
  | zero => simp [reflect_one]
  | succ j ih =>
    rw [pow_succ, Nat.mul_succ, reflect_mul _ _ (by
      calc (H^j).natDegree ≤ j * H.natDegree := natDegree_pow_le
           _ ≤ p*j := by nlinarith) hdeg, ih, h]

lemma frobenius_data (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ H : Polynomial ℤ,
      (1+X)^p - 1 - X^p = C (p : ℤ) * H ∧ Q ∣ H ∧
      H.natDegree ≤ p ∧ H.reflect p = H ∧ H.coeff 0 = 0 := by
  let F : Polynomial ℤ := (1+X)^p - 1 - X^p
  have hF : C (p : ℤ) ∣ F := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    simp only [F, coeff_sub, coeff_one_add_X_pow, coeff_one, coeff_X_pow]
    by_cases hi0 : i = 0
    · subst i; simp [show p ≠ 0 by omega, show 0 ≠ p by omega]
    · by_cases hip : i = p
      · subst i; simp [show p ≠ 0 by omega, show 0 ≠ p by omega]
      · simp only [hi0, hip, ↓reduceIte, sub_zero]
        by_cases hi : i < p
        · exact_mod_cast hp.dvd_choose_self hi0 hi
        · simp [Nat.choose_eq_zero_of_lt (by omega : p < i)]
  obtain ⟨H, hH⟩ := hF
  have hpn : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hCp : (C (p : ℤ) : Polynomial ℤ) ≠ 0 := by simpa using hp.ne_zero
  have hdegF : F.natDegree ≤ p := by
    dsimp [F]
    compute_degree!
  have hdeg : H.natDegree ≤ p := by
    rw [hH, natDegree_C_mul hpn] at hdegF
    exact hdegF
  have hFref : F.reflect p = F := by
    unfold F
    rw [reflect_sub, reflect_sub, reflect_one, reflect_monomial, revAt_le le_rfl,
      Nat.sub_self, pow_zero]
    have hpow : ((1+X : Polynomial ℤ)^p).reflect p = (1+X)^p := by
      simpa using reflect_pow (1+X) 1 (by compute_degree!) (by
        rw [reflect_add, reflect_one, reflect_one_X]; ring) p
    rw [hpow]
    ring
  refine ⟨H, hH, monic_dvd_of_C_mul Q_monic (p : ℤ) hpn ?_, hdeg, ?_, ?_⟩
  · rw [← hH]
    exact Q_dvd_frobenius p hp hp5
  · rw [hH, reflect_C_mul] at hFref
    exact mul_left_cancel₀ hCp hFref
  · have hz : F.coeff 0 = 0 := by simp [F, coeff_one_add_X_pow, coeff_X_pow, show p ≠ 0 by omega, show 0 ≠ p by omega]
    rw [hH, coeff_C_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hpn

lemma weighted_poly_data (H : Polynomial ℤ) (p : ℕ) (hQ : Q ∣ H)
    (hdeg : H.natDegree ≤ p) (href : H.reflect p = H) (hzero : H.coeff 0 = 0)
    (j : ℕ) (hj : 0 < j) :
    ∃ P : Polynomial ℤ,
      (P : PowerSeries ℤ) = W * (H : PowerSeries ℤ)^j ∧
      P.natDegree ≤ p*j ∧ P.reflect (p*j) = -P ∧ P.coeff 0 = 0 := by
  obtain ⟨R, hR⟩ := hQ
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  let P : Polynomial ℤ := (1-X^2)*R*H^j
  have hPQ : Q*P = (1-X^2)*H^(j+1) := by
    dsimp [P]
    calc
      _ = (1-X^2)*(Q*R)*H^j := by ring
      _ = (1-X^2)*H^(j+1) := by rw [← hR, pow_succ]; ring
  have hHP : (H^(j+1)).natDegree ≤ p*(j+1) := by
    calc
      _ ≤ (j+1)*H.natDegree := natDegree_pow_le
      _ ≤ p*(j+1) := by nlinarith
  have hPdeg : P.natDegree ≤ p*(j+1) := by
    by_cases hP : P = 0
    · simp [hP]
    have hdegree : (Q*P).natDegree ≤ (1-X^2 : Polynomial ℤ).natDegree + (H^(j+1)).natDegree := by
      rw [hPQ]; exact natDegree_mul_le
    have hnum : (1-X^2 : Polynomial ℤ).natDegree = 2 := by compute_degree!
    rw [natDegree_mul Q_ne hP, Q_degree, hnum] at hdegree
    omega
  have hPref : P.reflect (p*(j+1)) = -P := by
    have he := congrArg (Polynomial.reflect (2+p*(j+1))) hPQ
    rw [reflect_mul _ _ (by rw [Q_degree]) hPdeg,
      reflect_mul _ _ (by compute_degree!) hHP,
      Q_reflect, reflect_pow H p hdeg href] at he
    have hnumref : (1-X^2 : Polynomial ℤ).reflect 2 = -(1-X^2) := by
      rw [reflect_sub, reflect_one, reflect_monomial, revAt_le le_rfl,
        Nat.sub_self, pow_zero]
      ring
    rw [hnumref, neg_mul, ← hPQ, ← mul_neg] at he
    exact mul_left_cancel₀ Q_ne he
  have hPzero : P.coeff 0 = 0 := by
    have he := congrArg (Polynomial.constantCoeff) hPQ
    simp only [map_mul, map_pow] at he
    simpa [Q, Polynomial.constantCoeff_apply, hzero] using he
  refine ⟨P, ?_, hPdeg, hPref, hPzero⟩
  have hw : ((1-X^2 : Polynomial ℤ) : PowerSeries ℤ) = W * (Q : PowerSeries ℤ) := by
    simpa [Q] using W_mul_Q.symm
  have hRc := congrArg (fun T : Polynomial ℤ => (T : PowerSeries ℤ)) hR
  simp only [Polynomial.coe_mul] at hRc
  dsimp [P]
  push_cast
  rw [← show ((1-X^2 : Polynomial ℤ) : PowerSeries ℤ) = 1-PowerSeries.X^2 by simp, hw]
  rw [mul_assoc W, ← hRc, pow_succ]
  ring

end OEIS333096

open Nat Finset BigOperators Int
namespace OEIS333096
open Polynomial

lemma sum_antisymmetric (v : ℕ → ℤ) (j : ℕ)
    (hv : ∀ l ≤ j, v (j-l) = -v l) : ∑ l ∈ range (j+1), v l = 0 := by
  have h := Finset.sum_range_reflect v (j+1)
  simp only [Nat.add_sub_cancel] at h
  have h' : (∑ l ∈ range (j+1), v (j-l)) = -(∑ l ∈ range (j+1), v l) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun l hl => hv l (by simpa using hl))
  omega

noncomputable def fallTail (l : ℕ) : Polynomial ℤ :=
  ∏ i ∈ range (l-1), (X - C (i+1 : ℤ))

lemma desc_eq_tail (B l : ℕ) (hl : 0 < l) :
    (B.descFactorial l : ℤ) = (B : ℤ) * (fallTail l).eval (B : ℤ) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  rw [← descPochhammer_eval_eq_descFactorial ℤ, descPochhammer_eval_eq_prod_range,
    Finset.prod_range_succ']
  simp only [fallTail, Nat.succ_sub_one, eval_prod, eval_sub, eval_X, eval_C,
    Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
  ring

lemma tail_eval_congr (q B : ℤ) (hB : q ∣ B) (l : ℕ) :
    q ∣ (fallTail l).eval B - (fallTail l).eval 0 := by
  have h := Polynomial.sub_dvd_eval_sub B 0 (fallTail l)
  simp only [sub_zero] at h
  exact hB.trans h

lemma cubic_product_dvd (q B C U U₀ V V₀ : ℤ)
    (hB : q ∣ B) (hC : q ∣ C) (hU : q ∣ U-U₀) (hV : q ∣ V-V₀) :
    q^3 ∣ B*C*U*V-B*C*U₀*V₀ := by
  have hUV : q ∣ U*V-U₀*V₀ := by
    convert dvd_add (dvd_mul_of_dvd_left hU V) (dvd_mul_of_dvd_right hV U₀) using 1 <;> ring
  convert mul_dvd_mul (mul_dvd_mul hB hC) hUV using 1 <;> ring

lemma antisymmetric_desc_dvd (q : ℤ) (B C j : ℕ) (hB : q ∣ (B : ℤ))
    (hC : q ∣ (C : ℤ)) (v : ℕ → ℤ)
    (hzero : v 0 = 0) (hend : v j = 0) (hv : ∀ l ≤ j, v (j-l) = -v l) :
    q^3 ∣ ∑ l ∈ range (j+1), v l * (B.descFactorial l : ℤ) * (C.descFactorial (j-l) : ℤ) := by
  let w : ℕ → ℤ := fun l => v l * (fallTail l).eval 0 * (fallTail (j-l)).eval 0
  have hw : ∑ l ∈ range (j+1), w l = 0 := by
    apply sum_antisymmetric
    intro l hl
    dsimp [w]
    rw [hv l hl, Nat.sub_sub_self hl]
    ring
  have hmod : (∑ l ∈ range (j+1), v l * (B.descFactorial l : ℤ) * (C.descFactorial (j-l) : ℤ)) ≡
      ∑ l ∈ range (j+1), (B : ℤ)*(C : ℤ)*w l [ZMOD q^3] := by
    apply Int.ModEq.sum
    intro l hl
    have hlj : l ≤ j := by simpa using hl
    by_cases hl0 : l = 0
    · simp [hl0, hzero, w]
    by_cases hlj' : l = j
    · simp [hlj', hend, w]
    rw [desc_eq_tail B l (by omega), desc_eq_tail C (j-l) (by omega)]
    apply Int.modEq_iff_dvd.mpr
    have h := cubic_product_dvd q B C _ _ _ _ hB hC
      (tail_eval_congr q B hB l) (tail_eval_congr q C hC (j-l))
    have hh := dvd_mul_of_dvd_right h (-v l)
    convert hh using 1 <;> dsimp [w] <;> ring
  have hs : (∑ l ∈ range (j+1), (B : ℤ)*(C : ℤ)*w l) = 0 := by
    rw [← Finset.mul_sum, hw, mul_zero]
  rw [hs] at hmod
  exact (Int.modEq_zero_iff_dvd.mp hmod)

lemma antisymmetric_small_zero (B C j : ℕ) (hj : j ≤ 2) (v : ℕ → ℤ)
    (hzero : v 0 = 0) (hend : v j = 0) (hv : ∀ l ≤ j, v (j-l) = -v l) :
    (∑ l ∈ range (j+1), v l * (B.descFactorial l : ℤ) * (C.descFactorial (j-l) : ℤ)) = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  have hlj : l ≤ j := by simpa using hl
  suffices v l = 0 by simp [this]
  by_cases h0 : l = 0
  · simpa [h0] using hzero
  by_cases hjl : l = j
  · simpa [hjl] using hend
  have hm : j-l=l := by omega
  have he := hv l hlj
  rw [hm] at he
  omega

lemma binomial_desc_identity (A B j l : ℕ) (hBA : B ≤ A) (hjA : j ≤ A) (hlj : l ≤ j) :
    (j.factorial : ℤ) * (A.choose j : ℤ) *
      (if l ≤ B then ((A-j).choose (B-l) : ℤ) else 0) =
    (A.choose B : ℤ) * (B.descFactorial l : ℤ) * ((A-B).descFactorial (j-l) : ℤ) := by
  by_cases hlB : l ≤ B
  · rw [if_pos hlB]
    by_cases hjl : j-l ≤ A-B
    · have hB : B-l ≤ A-j := by omega
      have he : A-j-(B-l) = A-B-(j-l) := by omega
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      rw [Nat.cast_choose ℚ hjA, Nat.cast_choose ℚ hB, Nat.cast_choose ℚ hBA,
        Nat.cast_choose ℚ hlB, Nat.cast_choose ℚ hjl, he]
      have hn (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      field_simp
    · have hB : A-j < B-l := by omega
      rw [Nat.choose_eq_zero_of_lt hB, Nat.descFactorial_of_lt (by omega : A-B < j-l)]
      simp
  · rw [if_neg hlB, Nat.descFactorial_of_lt (by omega : B < l)]
    simp

lemma factorial_valuation_bound (p j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 3 ≤ j) :
    padicValNat p j.factorial + 3 ≤ j := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : j ≠ 0)
  have h4 : 4 * padicValNat p j.factorial < j := by
    have hh : 4 ≤ p-1 := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hh) h
  by_cases hz : padicValNat p j.factorial = 0 <;> omega

lemma factorial_cancel_prime_power (p j e : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hj : 3 ≤ j)
    (t u : ℤ) (heq : (j.factorial : ℤ)*t = (p : ℤ)^j*u)
    (hu : (p : ℤ)^(3*e) ∣ u) : (p : ℤ)^(3*(e+1)) ∣ t := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases ht : t = 0
  · simp [ht]
  have hfac : (j.factorial : ℤ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hpj : (p : ℤ)^j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hu0 : u ≠ 0 := by intro h; rw [h, mul_zero] at heq; exact mul_ne_zero hfac ht heq
  have hv := congrArg (padicValInt p) heq
  rw [padicValInt.mul hfac ht, padicValInt.mul hpj hu0, padicValInt.of_nat,
    ← Nat.cast_pow, padicValInt.of_nat, padicValNat.prime_pow] at hv
  have hul : 3*e ≤ padicValInt p u := ((padicValInt_dvd_iff _ _).mp hu).resolve_left hu0
  have hb := factorial_valuation_bound p j hp hp5 hj
  apply (padicValInt_dvd_iff _ _).mpr
  right
  omega

end OEIS333096

open Nat Finset BigOperators Int
namespace OEIS333096
open Polynomial

noncomputable def cartier (p : ℕ) (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => PowerSeries.coeff (n*p) f)

lemma cartier_coeff (p n : ℕ) (f : PowerSeries ℤ) :
    PowerSeries.coeff n (cartier p f) = PowerSeries.coeff (n*p) f := by simp [cartier]

lemma cartier_mul_expand (p : ℕ) (hp : p ≠ 0) (f g : PowerSeries ℤ) :
    cartier p (f * PowerSeries.expand p hp g) = cartier p f * g := by
  ext n
  rw [cartier_coeff, PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.sum_subset
    (s₁ := (antidiagonal n).image fun x : ℕ × ℕ => (x.1*p, x.2*p)), Finset.sum_image]
  · simp_rw [show ∀ t, PowerSeries.coeff (t*p) (PowerSeries.expand p hp g) = PowerSeries.coeff t g by
      intro t; simpa [Nat.mul_comm] using PowerSeries.coeff_expand_mul p hp g t, cartier_coeff]
  · intro x hx y hy eq
    simpa only [Prod.ext_iff, Nat.mul_right_cancel_iff hp.bot_lt] using eq
  · simp_rw [Finset.subset_iff, Finset.mem_image, Finset.mem_antidiagonal]
    rintro _ ⟨x, rfl, rfl⟩
    simp_rw [add_mul]
  simp_rw [Finset.mem_image, Finset.mem_antidiagonal]
  intro ⟨x,y⟩ eq nex
  by_cases h : p ∣ y
  · obtain ⟨x, rfl⟩ : p ∣ x := (Nat.dvd_add_iff_left h).mpr (eq ▸ dvd_mul_left p n)
    obtain ⟨y, rfl⟩ := h
    refine (nex ⟨⟨x,y⟩, (Nat.mul_right_cancel_iff hp.bot_lt).mp ?_, by simp_rw [mul_comm]⟩).elim
    rw [← eq, mul_comm, mul_add]
  · rw [PowerSeries.coeff_expand p hp, if_neg h, mul_zero]

lemma weight_mul (p n : ℕ) (hp : p ≠ 0) (h3 : ¬ 3 ∣ p) : weight (n*p) = weight n := by
  have hd : 3 ∣ n*p ↔ 3 ∣ n := by rw [Nat.prime_three.dvd_mul]; tauto
  have hm : (n*p)%3=0 ↔ n%3=0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hd
  simp [weight, hm, mul_eq_zero, hp]

lemma cartier_W (p : ℕ) (hp : p ≠ 0) (h3 : ¬ 3 ∣ p) : cartier p W = W := by
  ext n
  simp only [cartier_coeff, W_coeff, weight_mul p n hp h3]

lemma W_binomial_expand_coeff (p A B : ℕ) (hp : p ≠ 0) (h3 : ¬ 3 ∣ p) :
    PowerSeries.coeff (p*B) (W*(1+PowerSeries.X^p)^A) = binSum (A : ℤ) B := by
  have h := congrArg (PowerSeries.coeff B) (cartier_mul_expand p hp W ((1+PowerSeries.X)^A))
  rw [cartier_W p hp h3, cartier_coeff] at h
  simpa [binSum, PowerSeries.binomialSeries_nat, map_pow, map_add, map_one,
    PowerSeries.expand_X, Nat.mul_comm] using h

lemma poly_contract_data (P : Polynomial ℤ) (p j : ℕ) (hp : 0 < p)
    (hdeg : P.natDegree ≤ p*j) (href : P.reflect (p*j) = -P) (hzero : P.coeff 0 = 0) :
    (P.contract p).natDegree ≤ j ∧ (P.contract p).coeff 0 = 0 ∧
    (P.contract p).coeff j = 0 ∧
    ∀ l ≤ j, (P.contract p).coeff (j-l) = -(P.contract p).coeff l := by
  have hanti : ∀ l ≤ j, (P.contract p).coeff (j-l) = -(P.contract p).coeff l := by
    intro l hl
    have h := congrArg (fun T : Polynomial ℤ => T.coeff (l*p)) href
    dsimp only at h
    rw [coeff_reflect, revAt_le (by nlinarith), coeff_neg] at h
    simpa [coeff_contract (Nat.ne_of_gt hp), Nat.sub_mul, Nat.mul_sub, Nat.mul_comm] using h
  have h0 : (P.contract p).coeff 0 = 0 := by simp [coeff_contract (Nat.ne_of_gt hp), hzero]
  refine ⟨?_, h0, ?_, hanti⟩
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro l hl
    rw [coeff_contract (Nat.ne_of_gt hp)]
    exact coeff_eq_zero_of_natDegree_lt (by nlinarith)
  · simpa [h0] using hanti 0 (Nat.zero_le j)

lemma contract_binomial_coeff (P : Polynomial ℤ) (p t B : ℕ) (hp : 0 < p) :
    (P * (1+X^p)^t).coeff (p*B) = ((P.contract p)*(1+X)^t).coeff B := by
  have he : (1+X^p : Polynomial ℤ)^t = Polynomial.expand ℤ p ((1+X)^t) := by simp
  rw [he, Nat.mul_comm p B, ← coeff_contract (Nat.ne_of_gt hp) _ B, contract_mul_expand (Nat.ne_of_gt hp)]
  all_goals first | rfl | omega

lemma polynomial_binomial_coeff (V : Polynomial ℤ) (j t B : ℕ) (hdeg : V.natDegree ≤ j) :
    (V*(1+X)^t).coeff B =
      ∑ l ∈ range (j+1), V.coeff l * (if l ≤ B then ((t.choose (B-l)) : ℤ) else 0) := by
  conv_lhs => rw [V.as_sum_range_C_mul_X_pow' (show V.natDegree < j+1 by omega)]
  rw [Finset.sum_mul, finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro l hl
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one_add_X_pow]

lemma binomial_weight_identity (V : Polynomial ℤ) (A B j : ℕ)
    (hBA : B ≤ A) (hjA : j ≤ A) (hdeg : V.natDegree ≤ j) :
    (j.factorial : ℤ)*(A.choose j : ℤ)*(V*(1+X)^(A-j)).coeff B =
      (A.choose B : ℤ) * ∑ l ∈ range (j+1),
        V.coeff l * (B.descFactorial l : ℤ) * ((A-B).descFactorial (j-l) : ℤ) := by
  rw [polynomial_binomial_coeff V j (A-j) B hdeg, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have he := binomial_desc_identity A B j l hBA hjA (by simpa using hl)
  linear_combination V.coeff l * he

lemma weighted_term_dvd (p e A B j : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B ≤ A) (hjA : j ≤ A) (hA : (p : ℤ)^e ∣ (A : ℤ)) (hB : (p : ℤ)^e ∣ (B : ℤ))
    (V : Polynomial ℤ) (hdeg : V.natDegree ≤ j) (hzero : V.coeff 0 = 0)
    (hend : V.coeff j = 0) (href : ∀ l ≤ j, V.coeff (j-l) = -V.coeff l) :
    (p : ℤ)^(3*(e+1)) ∣
      (p : ℤ)^j * (A.choose j : ℤ) * (V*(1+X)^(A-j)).coeff B := by
  let S : ℤ := ∑ l ∈ range (j+1),
    V.coeff l * (B.descFactorial l : ℤ) * ((A-B).descFactorial (j-l) : ℤ)
  have he : (j.factorial : ℤ) *
      ((p : ℤ)^j * (A.choose j : ℤ) * (V*(1+X)^(A-j)).coeff B) =
      (p : ℤ)^j * ((A.choose B : ℤ)*S) := by
    dsimp [S]
    linear_combination (p : ℤ)^j * binomial_weight_identity V A B j hBA hjA hdeg
  by_cases hj : 3 ≤ j
  · apply factorial_cancel_prime_power p j e hp hp5 hj _ _ he
    have hC : (p : ℤ)^e ∣ ((A-B : ℕ) : ℤ) := by rw [Nat.cast_sub hBA]; exact dvd_sub hA hB
    have hs := antisymmetric_desc_dvd ((p : ℤ)^e) B (A-B) j hB hC V.coeff hzero hend href
    have hs' : (p : ℤ)^(3*e) ∣ S := by simpa [S, ← pow_mul, Nat.mul_comm] using hs
    exact dvd_mul_of_dvd_right hs' _
  · have hs : S = 0 := antisymmetric_small_zero B (A-B) j (by omega) V.coeff hzero hend href
    rw [hs, mul_zero, mul_zero] at he
    have ht := (mul_eq_zero.mp he).resolve_left (by exact_mod_cast j.factorial_ne_zero)
    rw [ht]
    exact dvd_zero _

end OEIS333096

open Nat Finset BigOperators Int
namespace OEIS333096
open Polynomial

lemma binSum_frobenius_expansion (p A B : ℕ) (H : Polynomial ℤ)
    (hH : (1+X)^p - 1 - X^p = C (p : ℤ)*H) :
    binSum ((p*A : ℕ) : ℤ) (p*B) =
      ∑ j ∈ range (A+1), (p : ℤ)^j * (A.choose j : ℤ) *
        PowerSeries.coeff (p*B) (W*(H : PowerSeries ℤ)^j*(1+PowerSeries.X^p)^(A-j)) := by
  have hf : (1+X : Polynomial ℤ)^p = C (p : ℤ)*H+(1+X^p) := by linear_combination hH
  have hex : (1+X : Polynomial ℤ)^(p*A) =
      ∑ j ∈ range (A+1), C ((p : ℤ)^j*(A.choose j : ℤ))*H^j*(1+X^p)^(A-j) := by
    rw [pow_mul, hf, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow, ← map_pow, ← C_eq_natCast, map_mul]
    ring
  rw [binSum, PowerSeries.binomialSeries_nat]
  have hex' := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℤ)) hex
  simp only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply] at hex'
  push_cast at hex'
  rw [hex', Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he : W * (PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) * (H : PowerSeries ℤ)^j *
      (1+PowerSeries.X^p)^(A-j)) =
      PowerSeries.C ((p : ℤ)^j * (A.choose j : ℤ)) *
        (W*(H : PowerSeries ℤ)^j*(1+PowerSeries.X^p)^(A-j)) := by ring
  rw [he, PowerSeries.coeff_C_mul]

lemma binSum_supercongruence_nat (p e A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B ≤ A) (hA : (p : ℤ)^e ∣ (A : ℤ)) (hB : (p : ℤ)^e ∣ (B : ℤ)) :
    binSum ((p*A : ℕ) : ℤ) (p*B) ≡ binSum (A : ℤ) B [ZMOD (p : ℤ)^(3*(e+1))] := by
  obtain ⟨H, hH, hQ, hdeg, href, hzero⟩ := frobenius_data p hp hp5
  have h3 : ¬ 3 ∣ p := by intro h; have := (Nat.dvd_prime hp).mp h; omega
  rw [binSum_frobenius_expansion p A B H hH, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one, Nat.sub_zero]
  rw [W_binomial_expand_coeff p A B hp.ne_zero h3]
  rw [Int.modEq_iff_dvd, sub_add_eq_sub_sub_swap, sub_self, zero_sub, dvd_neg]
  apply Finset.dvd_sum
  intro j hj
  have hjA : j+1 ≤ A := by simpa using hj
  obtain ⟨P, hP, hPdeg, hPref, hPzero⟩ :=
    weighted_poly_data H p hQ hdeg href hzero (j+1) (by omega)
  obtain ⟨hVdeg, hVzero, hVend, hVref⟩ := poly_contract_data P p (j+1) hp.pos hPdeg hPref hPzero
  have hd := weighted_term_dvd p e A B (j+1) hp hp5 hBA hjA hA hB
    (P.contract p) hVdeg hVzero hVend hVref
  rw [← hP]
  have he : PowerSeries.coeff (p*B) ((P : PowerSeries ℤ)*(1+PowerSeries.X^p)^(A-(j+1))) =
      ((P.contract p)*(1+X)^(A-(j+1))).coeff B := by
    rw [← contract_binomial_coeff P p (A-(j+1)) B hp.pos]
    simp only [← Polynomial.coeff_coe]
    push_cast
    rfl
  rw [he]
  exact hd

end OEIS333096

open Nat Finset BigOperators Int
namespace OEIS333096
open Polynomial

lemma choose_difference_dvd (a b M : ℤ) (D k : ℕ) (hk : k ≤ D)
    (h : (D.factorial : ℤ)*M ∣ a-b) : M ∣ Ring.choose a k-Ring.choose b k := by
  have hfac : (k.factorial : ℤ) ∣ (D.factorial : ℤ) := by
    exact_mod_cast Nat.factorial_dvd_factorial hk
  have hd : (k.factorial : ℤ)*M ∣ a-b := (mul_dvd_mul_right hfac M).trans h
  have he := hd.trans (Polynomial.sub_dvd_eval_sub a b (descPochhammer ℤ k))
  rw [descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_prod_range,
    ← choose_factorial, ← choose_factorial, ← mul_sub] at he
  exact Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast k.factorial_ne_zero) he

lemma binSum_difference_dvd (a b M : ℤ) (B : ℕ)
    (h : (B.factorial : ℤ)*M ∣ a-b) : M ∣ binSum a B-binSum b B := by
  unfold binSum
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro uv huv
  simp only [PowerSeries.binomialSeries_coeff, zsmul_eq_mul, mul_one, Int.cast_id]
  rw [← mul_sub]
  apply _root_.dvd_mul_of_dvd_right
  exact choose_difference_dvd a b M B uv.2 (Finset.antidiagonal.snd_le huv) h

lemma binSum_mod_congr (a b M : ℤ) (B : ℕ)
    (h : (B.factorial : ℤ)*M ∣ a-b) : binSum a B ≡ binSum b B [ZMOD M] := by
  apply Int.ModEq.symm
  apply Int.modEq_iff_dvd.mpr
  exact binSum_difference_dvd a b M B h

lemma exists_nat_congr_ge (a L : ℤ) (hL : 0 < L) (B : ℕ) :
    ∃ a' : ℕ, B ≤ a' ∧ L ∣ (a' : ℤ)-a := by
  obtain ⟨z, hz, he⟩ := Int.existsUnique_equiv_nat a hL
  refine ⟨z+L.toNat*(B+1), ?_, ?_⟩
  · have hpos : 0 < L.toNat := by omega
    nlinarith
  · have hcast : (L.toNat : ℤ) = L := Int.toNat_of_nonneg hL.le
    have he' : L ∣ (z : ℤ)-a := Int.modEq_iff_dvd.mp he.symm
    convert dvd_add he' (dvd_mul_right L (B+1 : ℤ)) using 1 <;> push_cast <;> rw [hcast] <;> ring

lemma binSum_supercongruence_int (p e B : ℕ) (A : ℤ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : (p : ℤ)^e ∣ A) (hB : (p : ℤ)^e ∣ (B : ℤ)) :
    binSum ((p : ℤ)*A) (p*B) ≡ binSum A B [ZMOD (p : ℤ)^(3*(e+1))] := by
  let M : ℤ := (p : ℤ)^(3*(e+1))
  let L : ℤ := ((p*B).factorial : ℤ)*M
  have hMpos : 0 < M := pow_pos (by exact_mod_cast hp.pos) _
  have hLpos : 0 < L := mul_pos (by exact_mod_cast (p*B).factorial_pos) hMpos
  obtain ⟨A', hBA', hL⟩ := exists_nat_congr_ge A L hLpos B
  have hbase : (p : ℤ)^e ∣ M := pow_dvd_pow _ (by omega)
  have hbaseL : (p : ℤ)^e ∣ L := dvd_mul_of_dvd_right hbase _
  have hA' : (p : ℤ)^e ∣ (A' : ℤ) := by
    have he := dvd_add (hbaseL.trans hL) hA
    simpa using he
  have hnat := binSum_supercongruence_nat p e A' B hp hp5 hBA' hA' hB
  have hhi : binSum ((p : ℤ)*A) (p*B) ≡ binSum ((p*A' : ℕ) : ℤ) (p*B) [ZMOD M] := by
    apply binSum_mod_congr
    have he := dvd_mul_of_dvd_right hL (-(p : ℤ))
    convert he using 1 <;> dsimp [L] <;> push_cast <;> ring
  have hlo : binSum (A' : ℤ) B ≡ binSum A B [ZMOD M] := by
    apply binSum_mod_congr
    have hBD : B ≤ p*B := by nlinarith [hp.pos]
    have hfac : (B.factorial : ℤ) ∣ ((p*B).factorial : ℤ) := by
      exact_mod_cast Nat.factorial_dvd_factorial hBD
    exact (mul_dvd_mul_right hfac M).trans hL
  exact hhi.trans (hnat.trans hlo)

end OEIS333096

/--
Conjecture on OEIS A333096:
More generally, for each integer $m$, we conjecture that the sequence
$a_m(n) := \text{the } n\text{-th order Taylor polynomial of } c(x)^{m \cdot n} \text{ evaluated at } x = 1$
satisfies the supercongruences $a_m(n \cdot p^k) \equiv a_m(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [Nat.succ_sub_one]
  have hBpos : 0 < n*p^e := Nat.mul_pos hn (pow_pos hp.pos _)
  have hNpos : 0 < n*p^(e+1) := Nat.mul_pos hn (pow_pos hp.pos _)
  rw [OEIS333096.a_gen_eq m _ hNpos, OEIS333096.a_gen_eq m _ hBpos]
  apply Int.ModEq.add_right
  have hB : (p : ℤ)^e ∣ ((n*p^e : ℕ) : ℤ) := by
    push_cast
    exact dvd_mul_left _ _
  have hA : (p : ℤ)^e ∣ (m+2)*((n*p^e : ℕ) : ℤ) := dvd_mul_of_dvd_right hB _
  have h := OEIS333096.binSum_supercongruence_int p e (n*p^e)
    ((m+2)*((n*p^e : ℕ) : ℤ)) hp hp5 hA hB
  have hnid : n*p^(e+1) = p*(n*p^e) := by rw [pow_succ]; ring
  rw [hnid]
  convert h using 1 <;> push_cast <;> ring

theorem oeis_333096_supercongruence_conjecture.disproof : ¬ (type_of% @oeis_333096_supercongruence_conjecture) := sorry
