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

open PowerSeries

namespace Cat

/-- The binomial series `(1+X)^M` for an integer `M`. -/
noncomputable def B (M : ℤ) : PowerSeries ℤ := PowerSeries.mk (fun j => Ring.choose M j)

/-- The weight sequence: `e 0 = 1`, `e d = 2` if `3 ∣ d`, `e d = -1` otherwise. -/
def e (d : ℕ) : ℤ := if d = 0 then 1 else if d % 3 = 0 then 2 else -1

noncomputable def Φ : PowerSeries ℤ := PowerSeries.mk (fun d => e d)

@[simp] lemma coeff_B (M : ℤ) (j : ℕ) : coeff j (B M) = Ring.choose M j := by
  simp [B]

@[simp] lemma coeff_Φ (d : ℕ) : coeff d Φ = e d := by
  simp [Φ]

lemma B_succ (M : ℤ) : B (M + 1) = B M * (1 + X) := by
  ext j
  rw [mul_add, mul_one, map_add, coeff_B]
  cases j with
  | zero => simp [Ring.choose_zero_right]
  | succ k =>
    rw [coeff_succ_mul_X, coeff_B, coeff_B, Ring.choose_succ_succ, add_comm]

lemma B_add_nat (M : ℤ) (n : ℕ) : B (M + n) = B M * (1 + X) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, B_succ, ih, pow_succ, mul_assoc]

lemma B_zero : B 0 = 1 := by
  ext j
  rw [coeff_B, coeff_one, Ring.choose_zero_ite]

lemma B_nat (n : ℕ) : B n = (1 + X) ^ n := by
  have := B_add_nat 0 n
  rwa [zero_add, B_zero, one_mul] at this

lemma pow_mul_B_neg (n : ℕ) : (1 + X : PowerSeries ℤ) ^ n * B (-n) = 1 := by
  have := B_add_nat (-n) n
  rw [neg_add_cancel, B_zero] at this
  rw [mul_comm]; exact this.symm

/-- Cancellation of the unit `(1+X)^n` in a divisibility by `X^m`. -/
lemma X_pow_dvd_of_dvd_mul_pow {m n : ℕ} {f : PowerSeries ℤ}
    (h : (X : PowerSeries ℤ) ^ m ∣ f * (1 + X) ^ n) : (X : PowerSeries ℤ) ^ m ∣ f := by
  have : f = f * (1 + X) ^ n * B (-n) := by
    rw [mul_assoc, pow_mul_B_neg, mul_one]
  rw [this]
  exact dvd_mul_of_dvd_left h _

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add_three_add (d : ℕ) : e (d + 3) + e (d + 2) + e (d + 1) = 0 := by
  unfold e
  have h : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases h with h | h | h <;> simp [Nat.add_mod, h]

lemma Φ_mul : (1 + X + X ^ 2 : PowerSeries ℤ) * Φ = 1 - X ^ 2 := by
  ext d
  rw [add_mul, add_mul, one_mul, map_add, map_add, map_sub, coeff_one, coeff_X_pow,
    coeff_X_pow_mul', coeff_Φ]
  rcases d with _ | _ | _ | d
  · simp [e]
  · simp [e, coeff_succ_X_mul]
  · simp [e, coeff_succ_X_mul]
  · have h1 : coeff (d + 3) (X * Φ) = e (d + 2) := by
      rw [show d + 3 = d + 2 + 1 by ring, coeff_succ_X_mul, coeff_Φ]
    rw [h1]
    have h2 := e_add_three_add d
    simp only [show 2 ≤ d + 3 by omega, if_true, show d + 3 - 2 = d + 1 by omega, coeff_Φ]
    have : (d + 3 ≠ 0) := by omega
    simp only [this, if_false, show d + 3 ≠ 2 by omega]
    linarith

lemma e_mul_of_not_three_dvd {p : ℕ} (hp : ¬ 3 ∣ p) (d : ℕ) : e (p * d) = e d := by
  have hp0 : p ≠ 0 := by rintro rfl; exact hp (dvd_zero 3)
  have hcop : Nat.Coprime 3 p := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hp
  have key : 3 ∣ p * d ↔ 3 ∣ d := by
    rw [mul_comm]; exact hcop.dvd_mul_right
  unfold e
  have h1 : p * d = 0 ↔ d = 0 := by simp [hp0]
  simp only [h1, ← Nat.dvd_iff_mod_eq_zero, key]

end Cat

namespace Cat

/-- `k! * C(M,k) = (M)_k` (falling factorial). -/
lemma fact_mul_choose (M : ℤ) (k : ℕ) :
    (k.factorial : ℤ) * Ring.choose M k = (descPochhammer ℤ k).eval M := by
  rw [Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]

lemma choose_absorb (M : ℤ) (k : ℕ) :
    ((k:ℤ) + 1) * Ring.choose M (k+1) = (M - k) * Ring.choose M k := by
  have h1 := fact_mul_choose M (k+1)
  have h2 := fact_mul_choose M k
  rw [descPochhammer_succ_eval, ← h2, Nat.factorial_succ, Nat.cast_mul] at h1
  have hk : (k.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply mul_left_cancel₀ hk
  push_cast at h1
  linear_combination h1

lemma gchoose_eq (r : ℤ) (k : ℕ) : generalized_choose_int r k = Ring.choose r k := by
  unfold generalized_choose_int
  split_ifs with hk
  · subst hk; simp [Ring.choose_zero_right]
  · rw [← descPochhammer_eval_eq_prod_range, ← fact_mul_choose,
      Int.mul_ediv_cancel_left _ (by exact_mod_cast Nat.factorial_ne_zero k)]

def T (r : ℤ) : ℕ → ℤ
  | 0 => 1
  | k+1 => Ring.choose (r + 2*k + 1) (k+1) - Ring.choose (r + 2*k + 1) k

lemma gcc_eq (r : ℤ) (k : ℕ) :
    generalized_catalan_coefficient r k = T r k + (if k ≠ 0 ∧ r + k = 0 then 1 else 0) := by
  cases k with
  | zero => simp [generalized_catalan_coefficient, T]
  | succ k =>
    simp only [generalized_catalan_coefficient, Nat.succ_ne_zero, if_false, gchoose_eq, T, ne_eq,
      not_false_eq_true, true_and]
    have hM : r + 2 * ((k+1 : ℕ) : ℤ) - 1 = r + 2 * k + 1 := by push_cast; ring
    rw [hM]
    set M := r + 2 * k + 1 with hMdef
    have habs := choose_absorb M k
    have key : (r + ((k+1 : ℕ) : ℤ)) * (Ring.choose M (k+1) - Ring.choose M k)
        = r * Ring.choose M (k+1) := by
      push_cast
      have : M - k = r + k + 1 := by rw [hMdef]; ring
      rw [this] at habs
      linear_combination habs
    by_cases h0 : r + ((k+1 : ℕ) : ℤ) = 0
    · rw [if_pos h0, h0, Int.ediv_zero]
      have hr : r = -((k:ℤ)+1) := by push_cast at h0; linarith
      have hMk : M = (k : ℤ) := by rw [hMdef, hr]; ring
      rw [hMk, Ring.choose_natCast, Ring.choose_natCast, Nat.choose_succ_self, Nat.choose_self]
      simp
    · rw [if_neg h0, add_zero, ← key, Int.mul_ediv_cancel_left _ h0]

lemma coeff_zero_mul' (f g : PowerSeries ℤ) : coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  simp [coeff_zero_eq_constantCoeff]

lemma sum_T (r : ℤ) (N : ℕ) : ∑ k ∈ Finset.range (N+1), T r k = coeff N (B (r + 2 * N) * Φ) := by
  induction N with
  | zero =>
    simp [T, coeff_zero_mul', e_zero, Ring.choose_zero_right]
  | succ N ih =>
    rw [sum_range_succ, ih]
    have hB : B (r + 2 * ((N+1 : ℕ) : ℤ)) = B (r + 2*N) * (1 + X)^2 := by
      rw [← B_add_nat]; congr 1; push_cast; ring
    rw [hB]
    have : B (r + 2*N) * (1+X)^2 * Φ = B (r+2*N) * (1 - X^2) + X * (B (r + 2*N) * Φ) := by
      have h := Φ_mul
      calc B (r + 2*N) * (1+X)^2 * Φ
          = B (r+2*N) * ((1 + X + X^2) * Φ) + X * (B (r+2*N) * Φ) := by ring
        _ = _ := by rw [h]
    rw [this, map_add, coeff_succ_X_mul, mul_sub, mul_one, map_sub, coeff_B, coeff_mul_X_pow',
      coeff_B]
    simp only [T]
    rcases N with _ | N
    · simp [Ring.choose_succ_succ, Ring.choose_one_right]
      exact add_comm _ _
    · have h1 : r + 2 * ((N + 1 : ℕ) : ℤ) + 1 = (r + 2 * ((N+1 : ℕ) : ℤ)) + 1 := by ring
      rw [h1, Ring.choose_succ_succ, Ring.choose_succ_succ (r + 2 * ((N+1 : ℕ) : ℤ)) N]
      rw [if_pos (by omega), show N + 1 + 1 - 2 = N by omega]
      ring

lemma indicator_sum (m : ℤ) (N : ℕ) (hN : 0 < N) :
    ∑ k ∈ Finset.range (N+1), (if k ≠ 0 ∧ m * N + k = 0 then (1:ℤ) else 0) = if m = -1 then 1 else 0 := by
  by_cases hm : m = -1
  · subst hm
    rw [if_pos rfl]
    have : ∀ k ∈ Finset.range (N+1),
        (if k ≠ 0 ∧ (-1) * (N:ℤ) + k = 0 then (1:ℤ) else 0) = if k = N then 1 else 0 := by
      intro k hk
      congr 1
      apply propext; constructor
      · rintro ⟨h1, h2⟩; omega
      · rintro rfl; exact ⟨by omega, by ring⟩
    rw [sum_congr rfl this, sum_ite_eq']
    simp
  · rw [if_neg hm]
    apply sum_eq_zero
    intro k hk
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hk' : k ≤ N := by simpa [Nat.lt_succ_iff] using hk
    have hk1 : (k:ℤ) ≥ 1 := by omega
    have hkN : (k:ℤ) ≤ N := by exact_mod_cast hk'
    have hN1 : (N:ℤ) ≥ 1 := by exact_mod_cast hN
    apply hm
    rcases le_or_gt 0 m with h | h
    · have : 0 ≤ m * N := mul_nonneg h (by positivity)
      exfalso; linarith
    · have hm2 : m ≤ -2 := by omega
      have : m * N ≤ -2 * N := by nlinarith
      exfalso; linarith

lemma a_gen_eq (m : ℤ) (N : ℕ) (hN : 0 < N) :
    a_gen m N = coeff N (B ((m + 2) * N) * Φ) + (if m = -1 then 1 else 0) := by
  unfold a_gen
  rw [if_neg (by omega)]
  simp only []
  rw [sum_congr rfl (fun k _ => gcc_eq (m * N) k), sum_add_distrib, sum_T, indicator_sum m N hN,
    add_mul]

end Cat

namespace Cat
/-- `Δ p = ((1+X)^p - 1 - X^p)/p` as an integer polynomial. -/
noncomputable def Δ (p : ℕ) : Polynomial ℤ :=
  ∑ r ∈ Finset.range (p+1), Polynomial.monomial r ((p.choose r / p : ℕ) : ℤ)

lemma coeff_Δ (p n : ℕ) :
    (Δ p).coeff n = if n ≤ p then ((p.choose n / p : ℕ) : ℤ) else 0 := by
  unfold Δ
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [Nat.lt_succ_iff]

lemma coeff_Δ_zero (p : ℕ) (hp : 1 < p) : (Δ p).coeff 0 = 0 := by
  rw [coeff_Δ, if_pos (Nat.zero_le _), Nat.choose_zero_right, Nat.div_eq_of_lt hp]
  simp

lemma coeff_Δ_of_ge (p n : ℕ) (hp : 1 < p) (hn : p ≤ n) : (Δ p).coeff n = 0 := by
  rw [coeff_Δ]
  rcases hn.lt_or_eq with h | h
  · rw [if_neg (not_le.mpr h)]
  · subst h
    rw [if_pos le_rfl, Nat.choose_self, Nat.div_eq_of_lt hp]
    simp

lemma natDegree_Δ_le (p : ℕ) (hp : 1 < p) : (Δ p).natDegree ≤ p - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  exact coeff_Δ_of_ge p N hp (by omega)

lemma natDegree_Δ_le' (p : ℕ) (hp : 1 < p) : (Δ p).natDegree ≤ p :=
  (natDegree_Δ_le p hp).trans (Nat.sub_le _ _)

lemma p_mul_Δ (p : ℕ) (hp : p.Prime) :
    (Polynomial.C (p : ℤ)) * Δ p = (1 + Polynomial.X) ^ p - 1 - Polynomial.X ^ p := by
  ext n
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one, Polynomial.coeff_X_pow, coeff_Δ]
  have hp1 := hp.one_lt
  by_cases hn0 : n = 0
  · subst hn0
    simp [Nat.div_eq_of_lt hp1, hp.ne_zero, hp.ne_zero.symm]
  by_cases hnp : n = p
  · subst hnp
    simp [Nat.div_eq_of_lt hp1, hp.ne_zero]
  by_cases hn : n ≤ p
  · have hlt : n < p := lt_of_le_of_ne hn hnp
    rw [if_pos hn, if_neg hn0, if_neg hnp, sub_zero, sub_zero, ← Nat.cast_mul,
      Nat.mul_div_cancel' (Nat.Prime.dvd_choose_self hp hn0 hlt)]
  · rw [if_neg hn, if_neg hn0, if_neg hnp, Nat.choose_eq_zero_of_lt (not_le.mp hn)]
    simp

lemma reflect_Δ (p : ℕ) : (Δ p).reflect p = Δ p := by
  ext n
  rw [Polynomial.coeff_reflect, coeff_Δ, coeff_Δ]
  by_cases hn : n ≤ p
  · rw [Polynomial.revAt_le hn, if_pos (Nat.sub_le _ _), if_pos hn, Nat.choose_symm hn]
  · rw [Polynomial.revAt_eq_self_of_lt (not_le.mp hn), if_neg hn]

lemma cyclo_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ) ∣ (1 + Polynomial.X) ^ p - 1 - Polynomial.X ^ p := by
  rw [← AdjoinRoot.mk_eq_zero]
  set r := AdjoinRoot.root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ) with hr_def
  have hr : r ^ 2 + r + 1 = 0 := by
    have := AdjoinRoot.mk_self (f := (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ))
    simpa [map_add, map_pow, AdjoinRoot.mk_X] using this
  have hr3 : r ^ 3 = 1 := by linear_combination (r - 1) * hr
  have h1r : 1 + r = -r ^ 2 := by linear_combination hr
  simp only [map_sub, map_pow, map_add, map_one, AdjoinRoot.mk_X]
  rw [h1r]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  rw [Odd.neg_pow hodd, ← pow_mul]
  have h3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  set q := p / 3 with hq
  have hpq : p = 3 * q + p % 3 := (Nat.div_add_mod p 3).symm
  rcases hmod with h | h
  · rw [h] at hpq
    rw [hpq, show 2 * (3 * q + 1) = 3 * (2 * q) + 2 by ring, pow_add, pow_mul, hr3, one_pow,
      one_mul, pow_add, pow_mul, hr3, one_pow, one_mul, pow_one]
    linear_combination -hr
  · rw [h] at hpq
    rw [hpq, show 2 * (3 * q + 2) = 3 * (2 * q + 1) + 1 by ring, pow_add, pow_mul, hr3, one_pow,
      one_mul, pow_add, pow_mul, hr3, one_pow, one_mul, pow_one]
    linear_combination -hr

lemma cyclo_monic : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ).Monic := by
  monicity!

lemma cyclo_dvd_Δ (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ) ∣ Δ p := by
  have h := cyclo_dvd p hp hp5
  rw [← p_mul_Δ p hp] at h
  rw [← Polynomial.map_dvd_map (Int.castRingHom ℚ) Int.cast_injective cyclo_monic]
  have h' := Polynomial.map_dvd (Int.castRingHom ℚ) h
  rw [Polynomial.map_mul, Polynomial.map_C] at h'
  have hu : IsUnit (Polynomial.C ((Int.castRingHom ℚ) (p : ℤ))) := by
    rw [Polynomial.isUnit_C]
    simp [hp.ne_zero]
  exact (IsUnit.dvd_mul_left hu).mp h'

end Cat

namespace Cat

noncomputable def Δ' (p : ℕ) : Polynomial ℤ := Δ p /ₘ (Polynomial.X ^ 2 + Polynomial.X + 1)

lemma Δ_eq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Δ p = (Polynomial.X ^ 2 + Polynomial.X + 1) * Δ' p := by
  have h := Polynomial.modByMonic_add_div (Δ p) cyclo_monic
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd cyclo_monic).mpr (cyclo_dvd_Δ p hp hp5),
    zero_add] at h
  exact h.symm

/-- The polynomial equal to `Δ^(i+1) * Φ`. -/
noncomputable def Pi (p i : ℕ) : Polynomial ℤ := (Δ p) ^ i * Δ' p * (1 - Polynomial.X ^ 2)

lemma cyclo_mul_Pi (p i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Polynomial.X ^ 2 + Polynomial.X + 1) * Pi p i = (Δ p) ^ (i+1) * (1 - Polynomial.X ^ 2) := by
  unfold Pi
  have h := Δ_eq p hp hp5
  calc (Polynomial.X ^ 2 + Polynomial.X + 1) * ((Δ p) ^ i * Δ' p * (1 - Polynomial.X ^ 2))
      = (Δ p) ^ i * ((Polynomial.X ^ 2 + Polynomial.X + 1) * Δ' p) * (1 - Polynomial.X ^ 2) := by
        ring
    _ = _ := by rw [← h]; ring

lemma coe_cyclo :
    ((Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ) : PowerSeries ℤ) = 1 + X + X ^ 2 := by
  simp only [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_one]
  ring

lemma coe_one_sub_X_sq :
    ((1 - Polynomial.X ^ 2 : Polynomial ℤ) : PowerSeries ℤ) = 1 - X ^ 2 := by
  simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_one]

lemma cyclo_ne_zero : (1 + X + X ^ 2 : PowerSeries ℤ) ≠ 0 := by
  intro h
  have := congr_arg (coeff 0) h
  simp at this

lemma Δ_pow_mul_Φ (p i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((Δ p : Polynomial ℤ) : PowerSeries ℤ) ^ (i+1) * Φ = (Pi p i : PowerSeries ℤ) := by
  apply mul_left_cancel₀ cyclo_ne_zero
  have h1 := cyclo_mul_Pi p i hp hp5
  have h2 := congr_arg (fun q : Polynomial ℤ => (q : PowerSeries ℤ)) h1
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, coe_cyclo, coe_one_sub_X_sq] at h2
  calc (1 + X + X ^ 2) * (((Δ p : Polynomial ℤ) : PowerSeries ℤ) ^ (i+1) * Φ)
      = ((Δ p : Polynomial ℤ) : PowerSeries ℤ) ^ (i+1) * ((1 + X + X ^ 2) * Φ) := by ring
    _ = ((Δ p : Polynomial ℤ) : PowerSeries ℤ) ^ (i+1) * (1 - X ^ 2) := by rw [Φ_mul]
    _ = _ := h2.symm

lemma natDegree_Δ'_le (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : (Δ' p).natDegree ≤ p - 3 := by
  by_cases h0 : Δ' p = 0
  · rw [h0]; simp
  have h := Δ_eq p hp hp5
  have hdeg := Polynomial.Monic.natDegree_mul' cyclo_monic h0
  rw [← h] at hdeg
  have h2 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ).natDegree = 2 := by
    compute_degree!
  have h3 := natDegree_Δ_le p hp.one_lt
  omega

lemma natDegree_Pi_le (p i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Pi p i).natDegree ≤ (i+1) * (p-1) := by
  unfold Pi
  have h1 : ((Δ p) ^ i).natDegree ≤ i * (p - 1) :=
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_Δ_le p hp.one_lt))
  have h2 := natDegree_Δ'_le p hp hp5
  have h3 : (1 - Polynomial.X ^ 2 : Polynomial ℤ).natDegree ≤ 2 := by compute_degree
  calc _ ≤ _ := Polynomial.natDegree_mul_le
    _ ≤ (i * (p-1) + (p - 3)) + 2 :=
        _root_.add_le_add (Polynomial.natDegree_mul_le.trans (_root_.add_le_add h1 h2)) h3
    _ = (i+1)*(p-1) := by
      have : p - 3 + 2 = p - 1 := by omega
      rw [add_assoc, this, add_mul, one_mul]

lemma natDegree_Pi_le' (p i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Pi p i).natDegree ≤ (i+1) * p :=
  (natDegree_Pi_le p i hp hp5).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

lemma reflect_Δ_pow (p j : ℕ) (hp : 1 < p) : ((Δ p) ^ j).reflect (j * p) = (Δ p) ^ j := by
  induction j with
  | zero => rw [pow_zero, ← Polynomial.C_1, Polynomial.reflect_C]; simp
  | succ j ih =>
    have hF : ((Δ p) ^ j).natDegree ≤ j * p :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_Δ_le' p hp))
    rw [pow_succ, add_mul, one_mul, Polynomial.reflect_mul _ _ hF (natDegree_Δ_le' p hp), ih,
      reflect_Δ]

lemma reflect_cyclo :
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ).reflect 2
      = Polynomial.X ^ 2 + Polynomial.X + 1 := by
  ext n
  rw [Polynomial.coeff_reflect]
  rcases n with _ | _ | _ | n
  · simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
  · simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
  · simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)]

lemma reflect_one_sub_X_sq :
    (1 - Polynomial.X ^ 2 : Polynomial ℤ).reflect 2 = -(1 - Polynomial.X ^ 2) := by
  ext n
  rw [Polynomial.coeff_reflect]
  rcases n with _ | _ | _ | n
  · simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
  · simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
  · simp [Polynomial.revAt, Polynomial.coeff_one, Polynomial.coeff_X]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)]
    simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]

lemma cyclo_ne_zero_poly : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ) ≠ 0 :=
  cyclo_monic.ne_zero

lemma reflect_Pi (p i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Pi p i).reflect ((i+1) * p) = -(Pi p i) := by
  apply mul_left_cancel₀ cyclo_ne_zero_poly
  have hc2 : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ).natDegree ≤ 2 := by
    compute_degree
  have h12 : (1 - Polynomial.X ^ 2 : Polynomial ℤ).natDegree ≤ 2 := by compute_degree
  have hΔ : ((Δ p) ^ (i+1)).natDegree ≤ (i+1) * p :=
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_Δ_le' p hp.one_lt))
  have h1 : (Polynomial.X ^ 2 + Polynomial.X + 1) * (Pi p i).reflect ((i+1) * p)
      = ((Polynomial.X ^ 2 + Polynomial.X + 1) * Pi p i).reflect (2 + (i+1) * p) := by
    rw [Polynomial.reflect_mul _ _ hc2 (natDegree_Pi_le' p i hp hp5), reflect_cyclo]
  rw [h1, cyclo_mul_Pi p i hp hp5, add_comm 2, Polynomial.reflect_mul _ _ hΔ h12,
    reflect_Δ_pow p (i+1) hp.one_lt, reflect_one_sub_X_sq, mul_neg, ← cyclo_mul_Pi p i hp hp5]
  ring

/-- `π_i(L) = coeff_{pL}(Δ^{i+1} Φ)`. -/
noncomputable def π (p i L : ℕ) : ℤ := (Pi p i).coeff (p * L)

lemma π_eq (p i L : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    coeff (p * L) (((Δ p : Polynomial ℤ) : PowerSeries ℤ) ^ (i+1) * Φ) = π p i L := by
  rw [Δ_pow_mul_Φ p i hp hp5, Polynomial.coeff_coe, π]

lemma π_antisymm (p i L : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hL : L ≤ i + 1) :
    π p i (i + 1 - L) = - π p i L := by
  have h := reflect_Pi p i hp hp5
  have h2 := congr_arg (fun q : Polynomial ℤ => q.coeff (p * L)) h
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg] at h2
  rw [Polynomial.revAt_le (by nlinarith)] at h2
  unfold π
  rw [← h2, Nat.mul_sub, mul_comm p (i+1)]

lemma π_eq_zero_of_ge (p i L : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hL : i + 1 ≤ L) :
    π p i L = 0 := by
  unfold π
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc (Pi p i).natDegree ≤ (i+1) * (p-1) := natDegree_Pi_le p i hp hp5
    _ < (i+1) * p := by
        have : 1 ≤ p := hp.one_lt.le
        have : (i+1) * (p-1) + (i+1) = (i+1) * p := by
          rw [← Nat.mul_succ]; congr 1; omega
        omega
    _ ≤ p * L := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hL

lemma π_zero (p i : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : π p i 0 = 0 := by
  rw [← π_eq p i 0 hp hp5, mul_zero, coeff_zero_eq_constantCoeff, map_mul, map_pow]
  have : constantCoeff ((Δ p : Polynomial ℤ) : PowerSeries ℤ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_Δ_zero p hp.one_lt]
  rw [this, zero_pow (Nat.succ_ne_zero i), zero_mul]

end Cat

namespace Cat

/-- `Bp K = (1 + X^p)^K`. -/
noncomputable def Bp (p : ℕ) (hp : p ≠ 0) (K : ℤ) : PowerSeries ℤ := PowerSeries.expand p hp (B K)

lemma Bp_succ (p : ℕ) (hp : p ≠ 0) (K : ℤ) : Bp p hp K * (1 + X ^ p) = Bp p hp (K + 1) := by
  unfold Bp
  rw [B_succ, map_mul, map_add, map_one, expand_X]

lemma Bp_zero (p : ℕ) (hp : p ≠ 0) : Bp p hp 0 = 1 := by
  unfold Bp; rw [B_zero, map_one]

/-- Coefficient extraction against an expanded series. -/
lemma coeff_mul_expand (p : ℕ) (hp : p ≠ 0) (Ψ ψ : PowerSeries ℤ) (N : ℕ) :
    coeff (p * N) (Ψ * expand p hp ψ)
      = ∑ l ∈ Finset.range (N + 1), coeff (p * (N - l)) Ψ * coeff l ψ := by
  rw [coeff_mul, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_expand, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun l => p * l) (fun k => k / p)
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
    exact ⟨by nlinarith [Nat.pos_of_ne_zero hp], dvd_mul_right _ _⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hk1, hk2⟩ := hk
    have := Nat.div_mul_cancel hk2
    have hp0 := Nat.pos_of_ne_zero hp
    by_contra hcon
    push_neg at hcon
    have : k / p * p ≥ (N + 1) * p := Nat.mul_le_mul_right _ hcon
    nlinarith
  · intro l _; exact Nat.mul_div_cancel_left l (Nat.pos_of_ne_zero hp)
  · intro k hk
    simp only [Finset.mem_filter] at hk
    exact Nat.mul_div_cancel' hk.2
  · intro l _
    rw [Nat.mul_sub, Nat.mul_div_cancel_left l (Nat.pos_of_ne_zero hp)]

/-- `D p = p * Δ p` as a power series. -/
noncomputable def D (p : ℕ) : PowerSeries ℤ := ((Polynomial.C (p : ℤ) * Δ p : Polynomial ℤ) : PowerSeries ℤ)

lemma one_add_X_pow (p : ℕ) (hp : p.Prime) : (1 + X : PowerSeries ℤ) ^ p = 1 + X ^ p + D p := by
  unfold D
  rw [p_mul_Δ p hp]
  simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_X]
  ring

lemma D_eq (p : ℕ) : D p = PowerSeries.C (p : ℤ) * ((Δ p : Polynomial ℤ) : PowerSeries ℤ) := by
  unfold D; rw [Polynomial.coe_mul, Polynomial.coe_C]

lemma X_dvd_D (p : ℕ) (hp : 1 < p) : (X : PowerSeries ℤ) ∣ D p := by
  have : constantCoeff ((Δ p : Polynomial ℤ) : PowerSeries ℤ) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_Δ_zero p hp]
  rw [X_dvd_iff, D_eq, map_mul, this, mul_zero]

/-- Truncated expansion `Σ_{i≤n} C(M,i) (pΔ)^i (1+X^p)^{M-i}`. -/
noncomputable def R (p : ℕ) (hp : p ≠ 0) (n : ℕ) (M : ℤ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range (n + 1), PowerSeries.C (Ring.choose M i) * D p ^ i * Bp p hp (M - i)

lemma R_step (p : ℕ) (hp : p ≠ 0) (n : ℕ) (M : ℤ) :
    R p hp n M * (1 + X ^ p + D p)
      = R p hp n (M + 1) + PowerSeries.C (Ring.choose M n) * D p ^ (n + 1) * Bp p hp (M - n) := by
  unfold R
  rw [mul_add, Finset.sum_mul, Finset.sum_mul]
  have h1 : ∀ i ∈ Finset.range (n + 1),
      PowerSeries.C (Ring.choose M i) * D p ^ i * Bp p hp (M - i) * (1 + X ^ p)
        = PowerSeries.C (Ring.choose M i) * D p ^ i * Bp p hp (M + 1 - i) := by
    intro i _
    rw [mul_assoc, Bp_succ]
    congr 2; ring
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_range_succ' (fun i => PowerSeries.C (Ring.choose M i) * D p ^ i * Bp p hp (M + 1 - i))]
  rw [Finset.sum_range_succ (fun i => PowerSeries.C (Ring.choose M i) * D p ^ i * Bp p hp (M - i) * D p)]
  rw [Finset.sum_range_succ' (fun i => PowerSeries.C (Ring.choose (M + 1) i) * D p ^ i * Bp p hp (M + 1 - i))]
  simp only [Ring.choose_zero_right, map_one, one_mul, pow_zero, Nat.cast_zero, sub_zero]
  have h2 : ∀ i ∈ Finset.range n,
      PowerSeries.C (Ring.choose (M + 1) (i + 1)) * D p ^ (i + 1) * Bp p hp (M + 1 - ((i + 1 : ℕ) : ℤ))
        = PowerSeries.C (Ring.choose M (i + 1)) * D p ^ (i + 1) * Bp p hp (M + 1 - ((i + 1 : ℕ) : ℤ))
          + PowerSeries.C (Ring.choose M i) * D p ^ i * Bp p hp (M - i) * D p := by
    intro i _
    have : M + 1 - ((i + 1 : ℕ) : ℤ) = M - i := by push_cast; ring
    rw [this, Ring.choose_succ_succ, map_add]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  ring

lemma cartier (p : ℕ) (hp : p.Prime) (n : ℕ) (M : ℤ) :
    (X : PowerSeries ℤ) ^ (n + 1) ∣ B (p * M) - R p hp.ne_zero n M := by
  have hXD : (X : PowerSeries ℤ) ^ (n + 1) ∣ D p ^ (n + 1) := pow_dvd_pow_of_dvd (X_dvd_D p hp.one_lt) _
  have hstep : ∀ M : ℤ, B (p * (M + 1)) - R p hp.ne_zero n (M + 1)
      = (B (p * M) - R p hp.ne_zero n M) * (1 + X ^ p + D p)
        + PowerSeries.C (Ring.choose M n) * D p ^ (n + 1) * Bp p hp.ne_zero (M - n) := by
    intro M
    have h := R_step p hp.ne_zero n M
    have hB : B (p * (M + 1)) = B (p * M) * (1 + X ^ p + D p) := by
      rw [mul_add, mul_one, B_add_nat, one_add_X_pow p hp]
    rw [hB, eq_sub_of_add_eq h.symm]
    ring
  induction M with
  | zero =>
    rw [mul_zero, B_zero]
    unfold R
    rw [Finset.sum_eq_single 0]
    · simp [Bp_zero]
    · intro i _ hi
      rw [Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
      simp
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  | succ M ih =>
    rw [hstep]
    exact dvd_add (dvd_mul_of_dvd_left ih _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hXD _) _)
  | pred M ih =>
    have h := hstep (-(M : ℤ) - 1)
    rw [sub_add_cancel] at h
    have h2 : (X : PowerSeries ℤ) ^ (n + 1) ∣
        (B (p * (-(M : ℤ) - 1)) - R p hp.ne_zero n (-(M : ℤ) - 1)) * (1 + X) ^ p := by
      rw [one_add_X_pow p hp]
      have : (B (p * (-(M : ℤ) - 1)) - R p hp.ne_zero n (-(M : ℤ) - 1)) * (1 + X ^ p + D p)
          = (B (p * -(M : ℤ)) - R p hp.ne_zero n (-(M : ℤ)))
            - PowerSeries.C (Ring.choose (-(M : ℤ) - 1) n) * D p ^ (n + 1)
              * Bp p hp.ne_zero (-(M : ℤ) - 1 - n) := by
        rw [h]; ring
      rw [this]
      exact dvd_sub ih (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hXD _) _)
    exact X_pow_dvd_of_dvd_mul_pow h2

lemma coeff_B_mul_Φ (p : ℕ) (hp : p.Prime) (M : ℤ) (n : ℕ) :
    coeff n (B (p * M) * Φ) = coeff n (R p hp.ne_zero n M * Φ) := by
  have h := cartier p hp n M
  have h2 : (X : PowerSeries ℤ) ^ (n + 1) ∣ (B (p * M) - R p hp.ne_zero n M) * Φ :=
    dvd_mul_of_dvd_left h _
  rw [X_pow_dvd_iff] at h2
  have := h2 n (Nat.lt_succ_self n)
  rw [sub_mul, map_sub, sub_eq_zero] at this
  exact this

end Cat

namespace Cat

/-- Falling factorial `x (x-1) ⋯ (x-n+1)`. -/
noncomputable def dp (n : ℕ) (x : ℤ) : ℤ := (descPochhammer ℤ n).eval x

lemma dp_add (a b : ℕ) (x : ℤ) : dp (a + b) x = dp a x * dp b (x - a) := by
  unfold dp
  rw [← descPochhammer_mul, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_natCast]

lemma dp_succ_left (a : ℕ) (x : ℤ) : dp (a + 1) x = x * dp a (x - 1) := by
  unfold dp
  rw [descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]

lemma dvd_dp (a : ℕ) (x : ℤ) : x ∣ dp (a + 1) x := by
  rw [dp_succ_left]; exact dvd_mul_right _ _

lemma dp_nat (a N : ℕ) : dp a (N : ℤ) = (N.descFactorial a : ℤ) :=
  descPochhammer_eval_eq_descFactorial ℤ N a

lemma fact_mul_choose' (x : ℤ) (n : ℕ) : (n.factorial : ℤ) * Ring.choose x n = dp n x :=
  fact_mul_choose x n

/-- Binomial coefficient with an integer lower index (zero when negative). -/
noncomputable def Ch (x : ℤ) (t : ℤ) : ℤ := if 0 ≤ t then Ring.choose x t.toNat else 0

lemma Ch_of_le (x : ℤ) (N L : ℕ) (h : L ≤ N) : Ch x ((N:ℤ) - L) = Ring.choose x (N - L) := by
  unfold Ch
  rw [if_pos (by omega)]
  congr 1
  omega

lemma Ch_of_lt (x : ℤ) (N L : ℕ) (h : N < L) : Ch x ((N:ℤ) - L) = 0 := by
  unfold Ch; rw [if_neg (by omega)]

lemma key_identity (x : ℤ) (N i L : ℕ) (hL : L ≤ i) :
    (i.factorial : ℤ) * Ring.choose x i * Ch (x - i) ((N:ℤ) - L)
      = Ring.choose x N * dp (i - L) (x - N) * dp L N := by
  by_cases hLN : L ≤ N
  · rw [Ch_of_le (x - i) N L hLN]
    have hfac : ((N - L).factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    apply mul_left_cancel₀ hfac
    calc ((N-L).factorial : ℤ) * (i.factorial * Ring.choose x i * Ring.choose (x - i) (N - L))
        = (i.factorial * Ring.choose x i) * ((N-L).factorial * Ring.choose (x - i) (N - L)) := by
          ring
      _ = dp i x * dp (N - L) (x - i) := by rw [fact_mul_choose', fact_mul_choose']
      _ = dp (i + (N - L)) x := (dp_add i (N - L) x).symm
      _ = dp (N + (i - L)) x := by congr 1; omega
      _ = dp N x * dp (i - L) (x - N) := dp_add N (i - L) x
      _ = (N.factorial * Ring.choose x N) * dp (i - L) (x - N) := by rw [fact_mul_choose']
      _ = (((N-L).factorial * N.descFactorial L : ℕ) : ℤ) * Ring.choose x N * dp (i - L) (x - N) := by
          rw [Nat.factorial_mul_descFactorial hLN]
      _ = _ := by rw [dp_nat]; push_cast; ring
  · rw [Ch_of_lt (x - i) N L (not_le.mp hLN), dp_nat,
      Nat.descFactorial_eq_zero_iff_lt.mpr (not_le.mp hLN)]
    simp

lemma bracket_identity (x : ℤ) (N i L : ℕ) (hL : L ≤ i) :
    (i.factorial : ℤ) * Ring.choose x i
        * (Ch (x - i) ((N:ℤ) - L) - Ch (x - i) ((N:ℤ) - ((i - L : ℕ) : ℤ)))
      = Ring.choose x N * (dp (i - L) (x - N) * dp L N - dp L (x - N) * dp (i - L) N) := by
  rw [mul_sub, key_identity x N i L hL, key_identity x N i (i - L) (Nat.sub_le _ _),
    Nat.sub_sub_self hL]
  ring

lemma triple_dvd (q N u : ℤ) (hN : q ∣ N) (hu : q ∣ u) (huN : q ∣ u - N) (a d : ℕ) (ha : 1 ≤ a) :
    q ^ 3 ∣ dp a u * dp a N * (dp d (u - a) - dp d (N - a)) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have h1 : q ∣ dp (a' + 1) u := hu.trans (dvd_dp a' u)
  have h2 : q ∣ dp (a' + 1) N := hN.trans (dvd_dp a' N)
  have h3 : q ∣ dp d (u - ((a' + 1 : ℕ) : ℤ)) - dp d (N - ((a' + 1 : ℕ) : ℤ)) := by
    apply huN.trans
    have := Polynomial.sub_dvd_eval_sub (u - ((a' + 1 : ℕ) : ℤ)) (N - ((a' + 1 : ℕ) : ℤ))
      (descPochhammer ℤ d)
    rwa [show u - ((a' + 1 : ℕ) : ℤ) - (N - ((a' + 1 : ℕ) : ℤ)) = u - N by ring] at this
  rw [pow_succ, pow_two]
  exact mul_dvd_mul (mul_dvd_mul h1 h2) h3

lemma bracket_dvd_aux (q N u : ℤ) (hN : q ∣ N) (hu : q ∣ u) (huN : q ∣ u - N) (a d : ℕ)
    (ha : 1 ≤ a) : q ^ 3 ∣ dp (a + d) u * dp a N - dp a u * dp (a + d) N := by
  rw [dp_add a d u, dp_add a d N]
  have := triple_dvd q N u hN hu huN a d ha
  convert this using 1; ring

lemma bracket_dvd (q N u : ℤ) (hN : q ∣ N) (hu : q ∣ u) (huN : q ∣ u - N) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) : q ^ 3 ∣ dp b u * dp a N - dp a u * dp b N := by
  rcases le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact bracket_dvd_aux q N u hN hu huN a d ha
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have := bracket_dvd_aux q N u hN hu huN b d hb
    rw [← dvd_neg]; convert this using 1; ring

lemma padicValNat_factorial_le (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (i : ℕ) (hi : 3 ≤ i) :
    padicValNat p i.factorial ≤ i - 3 := by
  haveI := Fact.mk hp
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := i) (by omega)
  have h4 : 4 * padicValNat p i.factorial ≤ (p - 1) * padicValNat p i.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- The main p-adic bound. -/
lemma main_bound (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k N : ℕ) (s : ℤ)
    (hN : (p:ℤ) ^ (k - 1) ∣ (N:ℤ)) (i L : ℕ) (hi : 3 ≤ i) (hL1 : 1 ≤ L) (hLi : L ≤ i - 1) :
    (p:ℤ) ^ (3 * k) ∣ (p:ℤ) ^ i * Ring.choose (s * N) i
      * (Ch (s * N - i) ((N:ℤ) - L) - Ch (s * N - i) ((N:ℤ) - ((i - L : ℕ) : ℤ))) := by
  haveI := Fact.mk hp
  set x : ℤ := s * N with hx
  set Y := Ring.choose x i
    * (Ch (x - i) ((N:ℤ) - L) - Ch (x - i) ((N:ℤ) - ((i - L : ℕ) : ℤ))) with hYdef
  have hY : (i.factorial : ℤ) * Y
      = Ring.choose x N * (dp (i - L) (x - N) * dp L N - dp L (x - N) * dp (i - L) N) := by
    rw [hYdef, ← mul_assoc]; exact bracket_identity x N i L (by omega)
  have hdiv : ((p:ℤ) ^ (k - 1)) ^ 3 ∣ (i.factorial : ℤ) * Y := by
    rw [hY]; apply _root_.dvd_mul_of_dvd_right
    apply bracket_dvd _ _ _ hN _ _ L (i - L) hL1 (by omega)
    · have : x - N = (s - 1) * N := by rw [hx]; ring
      rw [this]; exact _root_.dvd_mul_of_dvd_right hN _
    · have : x - N - N = (s - 2) * N := by rw [hx]; ring
      rw [this]; exact _root_.dvd_mul_of_dvd_right hN _
  set v := padicValNat p i.factorial with hv
  have hv' : v ≤ i - 3 := padicValNat_factorial_le p hp hp5 i hi
  obtain ⟨w, hw⟩ : ∃ w : ℕ, i.factorial = p ^ v * w := pow_padicValNat_dvd
  have hpw : ¬ p ∣ w := by
    intro h
    apply pow_succ_padicValNat_not_dvd (p := p) (Nat.factorial_ne_zero i)
    rw [← hv, pow_succ]
    calc p ^ v * p ∣ p ^ v * w := mul_dvd_mul_left _ h
      _ = i.factorial := hw.symm
  have h1 : (p:ℤ) ^ (3 * k + v) ∣ (p:ℤ) ^ i * ((i.factorial : ℤ) * Y) := by
    have : (p:ℤ) ^ (3 * k + v) ∣ (p:ℤ) ^ i * ((p:ℤ) ^ (k - 1)) ^ 3 := by
      rw [← pow_mul, ← pow_add]; apply pow_dvd_pow; omega
    exact this.trans (mul_dvd_mul_left _ hdiv)
  rw [hw, Nat.cast_mul, Nat.cast_pow] at h1
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 : (p:ℤ) ^ (3 * k) * (p:ℤ) ^ v ∣ ((p:ℤ) ^ i * Y * w) * (p:ℤ) ^ v := by
    rw [← pow_add]; convert h1 using 1; ring
  have h3 : (p:ℤ) ^ (3 * k) ∣ (p:ℤ) ^ i * Y * w :=
    (mul_dvd_mul_iff_right (pow_ne_zero _ hp0)).mp h2
  have hcop : IsCoprime ((p:ℤ) ^ (3 * k)) (w : ℤ) := by
    apply IsCoprime.pow_left
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpw)
  have := hcop.dvd_of_dvd_mul_right h3
  rw [hYdef, ← mul_assoc] at this
  exact this

end Cat

namespace Cat

lemma coeff_R_mul_Φ (p : ℕ) (hp : p.Prime) (M : ℤ) (N : ℕ) :
    coeff (p * N) (R p hp.ne_zero (p * N) M * Φ)
      = ∑ i ∈ Finset.range (p * N + 1), Ring.choose M i * (p:ℤ) ^ i *
          ∑ l ∈ Finset.range (N + 1),
            coeff (p * (N - l)) (((Δ p : Polynomial ℤ) : PowerSeries ℤ) ^ i * Φ)
              * Ring.choose (M - i) l := by
  unfold R
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have : PowerSeries.C (Ring.choose M i) * D p ^ i * Bp p hp.ne_zero (M - i) * Φ
       = PowerSeries.C (Ring.choose M i * (p:ℤ) ^ i)
          * ((((Δ p : Polynomial ℤ) : PowerSeries ℤ) ^ i * Φ) * expand p hp.ne_zero (B (M - i))) := by
    rw [D_eq, mul_pow, ← map_pow, map_mul]; unfold Bp; ring
  rw [this, coeff_C_mul, coeff_mul_expand]
  congr 1
  apply Finset.sum_congr rfl; intro l _; rw [coeff_B]

lemma coeff_B_mul_Φ_eq (M : ℤ) (N : ℕ) :
    coeff N (B M * Φ) = ∑ l ∈ Finset.range (N + 1), Ring.choose M l * e (N - l) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [coeff_B, coeff_Φ]

lemma term_zero (p : ℕ) (h3 : ¬ 3 ∣ p) (M : ℤ) (N : ℕ) :
    ∑ l ∈ Finset.range (N + 1), coeff (p * (N - l)) Φ * Ring.choose M l = coeff N (B M * Φ) := by
  rw [coeff_B_mul_Φ_eq]; apply Finset.sum_congr rfl; intro l _
  rw [coeff_Φ, e_mul_of_not_three_dvd h3, mul_comm]

lemma not_three_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ 3 ∣ p := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
  omega

lemma diff_eq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (M : ℤ) (N : ℕ) :
    coeff (p * N) (B (p * M) * Φ) - coeff N (B M * Φ)
      = ∑ i ∈ Finset.range (p * N), Ring.choose M (i + 1) * (p:ℤ) ^ (i + 1) *
          ∑ l ∈ Finset.range (N + 1), π p i (N - l) * Ring.choose (M - ((i + 1 : ℕ) : ℤ)) l := by
  rw [coeff_B_mul_Φ p hp M (p * N), coeff_R_mul_Φ p hp M N, Finset.sum_range_succ']
  simp only [pow_zero, Ring.choose_zero_right, one_mul, mul_one, Nat.cast_zero, sub_zero]
  rw [term_zero p (not_three_dvd p hp hp5) M N, add_sub_cancel_right]
  apply Finset.sum_congr rfl; intro i _
  congr 1; apply Finset.sum_congr rfl; intro l _
  rw [π_eq p i (N - l) hp hp5]

lemma term_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k N : ℕ) (s : ℤ)
    (hN : (p:ℤ) ^ (k - 1) ∣ (N:ℤ)) (i : ℕ) :
    (p:ℤ) ^ (3 * k) ∣ Ring.choose (s * N) (i + 1) * (p:ℤ) ^ (i + 1) *
        ∑ l ∈ Finset.range (N + 1), π p i (N - l) * Ring.choose (s * N - ((i + 1 : ℕ) : ℤ)) l := by
  set x := s * N with hx
  set t : ℕ → ℤ := fun L => π p i L * Ch (x - ((i + 1 : ℕ) : ℤ)) ((N:ℤ) - L) with ht
  have h1 : ∑ l ∈ Finset.range (N + 1), π p i (N - l) * Ring.choose (x - ((i + 1 : ℕ) : ℤ)) l
      = ∑ L ∈ Finset.range (N + 1), t L := by
    rw [← Finset.sum_range_reflect t (N + 1)]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' : l ≤ N := by simpa [Nat.lt_succ_iff] using hl
    simp only [ht]
    rw [show N + 1 - 1 - l = N - l by omega, Ch_of_le _ N (N - l) (Nat.sub_le _ _),
      Nat.sub_sub_self hl']
  have h2 : ∑ L ∈ Finset.range (N + 1), t L = ∑ L ∈ Finset.range (N + (i + 1) + 1), t L := by
    have hsub : Finset.range (N + 1) ⊆ Finset.range (N + (i + 1) + 1) :=
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
    apply Finset.sum_subset hsub
    intro L hL hL'
    simp only [Finset.mem_range, not_lt] at hL hL'
    simp only [ht]
    rw [Ch_of_lt _ N L (by omega), mul_zero]
  have h3 : ∑ L ∈ Finset.range (i + 1 + 1), t L = ∑ L ∈ Finset.range (N + (i + 1) + 1), t L := by
    have hsub : Finset.range (i + 1 + 1) ⊆ Finset.range (N + (i + 1) + 1) :=
      (by intro x hx; simp only [Finset.mem_range] at hx ⊢; omega)
    apply Finset.sum_subset hsub
    intro L hL hL'
    simp only [Finset.mem_range, not_lt] at hL hL'
    simp only [ht]
    rw [π_eq_zero_of_ge p i L hp hp5 (by omega), zero_mul]
  rw [h1, h2, ← h3]
  have h4 := Finset.sum_range_reflect t (i + 1 + 1)
  simp only [Nat.add_sub_cancel] at h4
  have h5 : (2:ℤ) * ∑ L ∈ Finset.range (i + 1 + 1), t L
      = ∑ L ∈ Finset.range (i + 1 + 1), π p i L *
          (Ch (x - ((i + 1 : ℕ) : ℤ)) ((N:ℤ) - L)
            - Ch (x - ((i + 1 : ℕ) : ℤ)) ((N:ℤ) - ((i + 1 - L : ℕ) : ℤ))) := by
    rw [two_mul]
    nth_rewrite 2 [← h4]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro L hL
    have hL' : L ≤ i + 1 := by simpa [Nat.lt_succ_iff] using hL
    simp only [ht]
    rw [π_antisymm p i L hp hp5 hL']; ring
  have h6 : (p:ℤ) ^ (3 * k) ∣ Ring.choose x (i + 1) * (p:ℤ) ^ (i + 1)
      * (2 * ∑ L ∈ Finset.range (i + 1 + 1), t L) := by
    rw [h5, Finset.mul_sum]
    apply Finset.dvd_sum
    intro L hL
    have hL' : L ≤ i + 1 := by simpa [Nat.lt_succ_iff] using hL
    rcases Nat.eq_zero_or_pos L with hL0 | hL0
    · subst hL0; rw [π_zero p i hp hp5]; simp
    rcases eq_or_lt_of_le hL' with hLI | hLI
    · rw [hLI, π_eq_zero_of_ge p i (i + 1) hp hp5 le_rfl]; simp
    rcases Nat.lt_or_ge i 2 with hi | hi
    · have hi1 : i = 1 := by omega
      have hL1 : L = 1 := by omega
      subst hi1; subst hL1
      simp
    · have hmb := main_bound p hp hp5 k N s hN (i + 1) L (by omega) hL0 (by omega)
      have := Dvd.dvd.mul_left hmb (π p i L)
      rw [hx]
      convert this using 1; ring
  have hcop : IsCoprime ((p:ℤ) ^ (3 * k)) 2 := by
    apply IsCoprime.pow_left
    rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num]
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have h7 : Ring.choose x (i + 1) * (p:ℤ) ^ (i + 1) * (2 * ∑ L ∈ Finset.range (i + 1 + 1), t L)
      = (Ring.choose x (i + 1) * (p:ℤ) ^ (i + 1) * ∑ L ∈ Finset.range (i + 1 + 1), t L) * 2 := by
    ring
  rw [h7] at h6
  exact hcop.dvd_of_dvd_mul_right h6

theorem core (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k N : ℕ) (s : ℤ)
    (hN : (p:ℤ) ^ (k - 1) ∣ (N:ℤ)) :
    (p:ℤ) ^ (3 * k) ∣ coeff (p * N) (B (s * ((p * N : ℕ) : ℤ)) * Φ) - coeff N (B (s * N) * Φ) := by
  have : s * ((p * N : ℕ) : ℤ) = p * (s * N) := by push_cast; ring
  rw [this, diff_eq p hp hp5 (s * N) N]
  apply Finset.dvd_sum
  intro i _
  exact term_dvd p hp hp5 k N s hN i

end Cat

/--
Conjecture on OEIS A333096:
More generally, for each integer $m$, we conjecture that the sequence
$a_m(n) := \text{the } n\text{-th order Taylor polynomial of } c(x)^{m \cdot n} \text{ evaluated at } x = 1$
satisfies the supercongruences $a_m(n \cdot p^k) \equiv a_m(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  set N := n * p ^ (k - 1) with hN
  have hNpos : 0 < N := by positivity
  have hpN : n * p ^ k = p * N := by
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hN, hk', Nat.add_sub_cancel, pow_succ]; ring
  have hdvd : (p:ℤ) ^ (k - 1) ∣ (N:ℤ) := by
    rw [hN]; push_cast; exact Dvd.intro_left _ rfl
  rw [Int.modEq_iff_dvd, hpN, Cat.a_gen_eq m (p * N) (by positivity), Cat.a_gen_eq m N hNpos]
  have := Cat.core p hp hp5 k N (m + 2) hdvd
  rw [← dvd_neg]
  convert this using 1
  push_cast
  ring

theorem oeis_333096_supercongruence_conjecture.disproof : ¬ (type_of% @oeis_333096_supercongruence_conjecture) := sorry
