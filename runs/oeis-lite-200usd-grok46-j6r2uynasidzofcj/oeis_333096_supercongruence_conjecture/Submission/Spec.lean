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

open scoped BigOperators
open PowerSeries Polynomial

-- ═══════════════════════════════════════════════════════════════════════
-- Section 1: `generalized_choose_int` = `Ring.choose`
-- ═══════════════════════════════════════════════════════════════════════

lemma falling_prod_eq_descPochhammer (r : ℤ) (k : ℕ) :
    (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) =
      (descPochhammer ℤ k).eval r := by
  induction k with
  | zero =>
    simp [descPochhammer]
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, descPochhammer_succ_right]
    simp [eval_mul, eval_X, eval_natCast]

lemma generalized_choose_int_eq_ringChoose (r : ℤ) (k : ℕ) :
    generalized_choose_int r k = Ring.choose r k := by
  rw [generalized_choose_int]
  split_ifs with hk
  · subst hk
    simp
  · have hfac : (k.factorial : ℤ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k
    have hsmul := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) r k
    rw [nsmul_eq_mul] at hsmul
    have : (Finset.prod (Finset.range k) fun i => r - (i : ℤ)) =
        (k.factorial : ℤ) * Ring.choose r k := by
      rw [falling_prod_eq_descPochhammer, eval_eq_smeval, hsmul]
    rw [this, Int.mul_ediv_cancel_left _ hfac]

/-- `k * binom(N,k) = (N-k+1) * binom(N, k-1)` for `k > 0`. -/
lemma ringChoose_mul_succ (N : ℤ) {k : ℕ} (hk : 0 < k) :
    (k : ℤ) * Ring.choose N k = (N - k + 1) * Ring.choose N (k - 1) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N k
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) N (k - 1)
  rw [nsmul_eq_mul, ← eval_eq_smeval] at h1 h2
  have hks : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have heval : (descPochhammer ℤ k).eval N =
      (descPochhammer ℤ (k - 1)).eval N * (N - ↑(k - 1)) := by
    simpa [hks] using descPochhammer_succ_eval (k - 1) N
  have hf : (k.factorial : ℤ) = (k : ℤ) * ((k - 1).factorial : ℤ) := by
    rw [← Nat.cast_mul, ← Nat.mul_factorial_pred hk.ne']
  have hN : N - ↑(k - 1) = N - k + 1 := by
    have : (k : ℤ) - 1 = ↑(k - 1) := by
      rw [Nat.cast_sub (Nat.one_le_of_lt hk), Nat.cast_one]
    linarith
  have hfac : ((k - 1).factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  apply mul_left_cancel₀ hfac
  calc
    ((k - 1).factorial : ℤ) * ((k : ℤ) * Ring.choose N k)
        = (k.factorial : ℤ) * Ring.choose N k := by rw [hf]; ring
    _ = (descPochhammer ℤ k).eval N := h1.symm
    _ = (descPochhammer ℤ (k - 1)).eval N * (N - ↑(k - 1)) := heval
    _ = ((k - 1).factorial : ℤ) * Ring.choose N (k - 1) * (N - k + 1) := by
        rw [h2, hN]
    _ = ((k - 1).factorial : ℤ) * ((N - k + 1) * Ring.choose N (k - 1)) := by ring

/-- Difference-of-binomials form of the Catalan-like coefficient. -/
def catalanDiff (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else Ring.choose (r + 2 * (k : ℤ) - 1) k - Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)

lemma catalan_diff_mul (r : ℤ) {k : ℕ} (hk : 0 < k) :
    let N := r + 2 * (k : ℤ) - 1
    (r + k) * (Ring.choose N k - Ring.choose N (k - 1)) = r * Ring.choose N k := by
  intro N
  have hrec := ringChoose_mul_succ N hk
  -- (r+k) = N - k + 1
  have hNk : N - k + 1 = r + k := by
    simp [N]; ring
  rw [hNk] at hrec
  -- (r+k)(C(N,k) - C(N,k-1)) = (r+k) C(N,k) - (r+k) C(N,k-1)
  --                           = (r+k) C(N,k) - k C(N,k)
  --                           = r C(N,k)
  have : (r + k) * Ring.choose N (k - 1) = (k : ℤ) * Ring.choose N k := hrec.symm
  linarith [this]

lemma generalized_catalan_eq_diff (r : ℤ) (k : ℕ) (hden : r + k ≠ 0) :
    generalized_catalan_coefficient r k = catalanDiff r k := by
  unfold generalized_catalan_coefficient catalanDiff
  split_ifs with hk
  · rfl
  · rw [generalized_choose_int_eq_ringChoose]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hmul := catalan_diff_mul r hkpos
    simp only at hmul
    change r * Ring.choose (r + 2 * (k : ℤ) - 1) k / (r + k) =
      Ring.choose (r + 2 * (k : ℤ) - 1) k - Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)
    rw [← hmul, Int.mul_ediv_cancel_left _ hden]

/-- True Catalan coefficient (equals `-1` rather than `0` when `r = -k`). -/
def catalanTrue (r : ℤ) (k : ℕ) : ℤ :=
  if k = 0 then 1
  else Ring.choose (r + 2 * (k : ℤ) - 1) k - Ring.choose (r + 2 * (k : ℤ) - 1) (k - 1)

lemma catalanTrue_eq_diff (r : ℤ) (k : ℕ) : catalanTrue r k = catalanDiff r k := rfl

/-- The mathematically correct truncated series (differs from `a_gen` only at `m = -1`). -/
def aTrue (m : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1
  else (Finset.range (n + 1)).sum fun k => catalanTrue (m * n) k

/-- Periodic coefficients of `g(w) = (1-w)^2(1+w)/(1-w^3)`. -/
def gCoeff (j : ℕ) : ℤ :=
  if j = 0 then 1
  else if j % 3 = 0 then 2 else -1

lemma gCoeff_zero : gCoeff 0 = 1 := rfl

lemma gCoeff_pos {j : ℕ} (hj : j ≠ 0) : gCoeff j = if j % 3 = 0 then 2 else -1 := by
  simp [gCoeff, hj]

lemma gCoeff_mod_three (j : ℕ) (hj : j ≠ 0) :
    gCoeff j = if j % 3 = 0 then (2 : ℤ) else (-1 : ℤ) :=
  gCoeff_pos hj

lemma three_not_dvd_of_prime_ge_five {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) : ¬ 3 ∣ p := by
  intro h
  have h3 : Nat.Prime 3 := by decide
  have : p = 3 := ((Nat.prime_dvd_prime_iff_eq h3 hp).mp h).symm
  omega

lemma gCoeff_mul_of_not_dvd_three {q j : ℕ} (hq : ¬ 3 ∣ q) :
    gCoeff (q * j) = gCoeff j := by
  by_cases hj : j = 0
  · subst hj; simp [gCoeff]
  by_cases hq0 : q = 0
  · subst hq0; exact (hq (dvd_zero 3)).elim
  have hpmul : q * j ≠ 0 := Nat.mul_ne_zero hq0 hj
  rw [gCoeff_pos hpmul, gCoeff_pos hj]
  have hiff : (q * j) % 3 = 0 ↔ j % 3 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
    constructor
    · intro h
      have h3 : Nat.Prime 3 := by decide
      rcases h3.dvd_or_dvd h with hq' | hj'
      · exact (hq hq').elim
      · exact hj'
    · intro h; exact dvd_mul_of_dvd_right h q
  by_cases h1 : (q * j) % 3 = 0
  · simp [h1, hiff.mp h1]
  · simp [h1, mt hiff.mpr h1]

/-- `U A B = [w^A] g(w) (1+w)^B`. -/
def U (A : ℕ) (B : ℤ) : ℤ :=
  (Finset.range (A + 1)).sum fun j => gCoeff j * Ring.choose B (A - j)

lemma gCoeff_add_three (j : ℕ) : gCoeff (j + 3) + gCoeff (j + 2) + gCoeff (j + 1) = 0 := by
  rw [gCoeff_pos (by omega : j + 3 ≠ 0), gCoeff_pos (by omega : j + 2 ≠ 0),
    gCoeff_pos (by omega : j + 1 ≠ 0)]
  have h1 : (j + 1) % 3 = (j % 3 + 1) % 3 := Nat.add_mod _ _ _
  have h2 : (j + 2) % 3 = (j % 3 + 2) % 3 := Nat.add_mod _ _ _
  have h3 : (j + 3) % 3 = j % 3 := by omega
  have hj : j % 3 < 3 := Nat.mod_lt j (by norm_num)
  interval_cases h : j % 3 <;> simp [h1, h2, h3, h]

lemma ringChoose_zero_of_neg {k : ℕ} (hk : 0 < k) : Ring.choose (0 : ℤ) k = 0 :=
  Ring.choose_zero_pos ℤ hk

lemma ringChoose_pascal (N : ℤ) (k : ℕ) :
    Ring.choose (N + 1) (k + 1) = Ring.choose N k + Ring.choose N (k + 1) :=
  Ring.choose_succ_succ N k

/-- Pascal in the form used below. -/
lemma ringChoose_succ_left (N : ℤ) (k : ℕ) :
    Ring.choose (N + 1) k = Ring.choose N k +
      (if k = 0 then 0 else Ring.choose N (k - 1)) := by
  by_cases hk : k = 0
  · subst hk; simp [Ring.choose_zero_right, Ring.choose_one_right]
  · have : k = (k - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)).symm
    rw [this, ringChoose_pascal]
    simp [hk]
    rw [add_comm]

lemma gCoeff_one : gCoeff 1 = -1 := rfl

lemma gCoeff_two : gCoeff 2 = -1 := rfl

lemma gCoeff_sum_three {j : ℕ} (hj : 3 ≤ j) :
    gCoeff j + gCoeff (j - 1) + gCoeff (j - 2) = 0 := by
  have : j = j - 3 + 3 := (Nat.sub_add_cancel hj).symm
  rw [this]
  have e1 : j - 3 + 3 - 1 = j - 3 + 2 := by omega
  have e2 : j - 3 + 3 - 2 = j - 3 + 1 := by omega
  rw [e1, e2]
  exact gCoeff_add_three (j - 3)

/-- Pascal: `choose(N+1, k) = choose(N,k) + choose(N, k-1)` (with `choose(_, -1) = 0`). -/
lemma ringChoose_succ_pred (N : ℤ) : ∀ k : ℕ,
    Ring.choose (N + 1) k =
      Ring.choose N k + if k = 0 then 0 else Ring.choose N (k - 1)
  | 0 => by simp [Ring.choose_zero_right]
  | k + 1 => by
    rw [ringChoose_pascal, add_comm]
    simp

lemma ringChoose_add_two (N : ℤ) : ∀ k : ℕ,
    Ring.choose (N + 2) k =
      Ring.choose N k
        + (if k = 0 then 0 else 2 * Ring.choose N (k - 1))
        + (if k ≤ 1 then 0 else Ring.choose N (k - 2))
  | 0 => by simp
  | 1 => by simp [Ring.choose_one_right]
  | k + 2 => by
    have hN : N + 2 = (N + 1) + 1 := by ring
    rw [hN]
    rw [show k + 2 = (k + 1) + 1 by rfl, ringChoose_pascal]
    rw [ringChoose_pascal N k, ringChoose_pascal N (k + 1)]
    simp
    ring

lemma choose_sub_choose_eq (N : ℤ) {n : ℕ} (hn : 0 < n) :
    Ring.choose (N - 2) n -
        (if 2 ≤ n then Ring.choose (N - 2) (n - 2) else 0) =
      Ring.choose (N - 1) n - Ring.choose (N - 1) (n - 1) := by
  have hN : N - 1 = (N - 2) + 1 := by ring
  match n with
  | 0 => exact (Nat.lt_irrefl _ hn).elim
  | 1 =>
    simp [Ring.choose_zero_right]
    ring
  | n + 2 =>
    have hif : (if 2 ≤ n + 2 then Ring.choose (N - 2) (n + 2 - 2) else 0) =
        Ring.choose (N - 2) n := by simp
    have hidx : n + 2 - 1 = n + 1 := by omega
    rw [hif, hN, hidx]
    rw [ringChoose_succ_pred (N - 2) (n + 2)]
    rw [ringChoose_succ_pred (N - 2) (n + 1)]
    simp
    ring

lemma U_eq_reindex (n : ℕ) (N : ℤ) :
    U n N = ∑ k ∈ Finset.range (n + 1), gCoeff (n - k) * Ring.choose N k := by
  unfold U
  refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    exact Nat.sub_lt_succ n j
  · intro j₁ hj₁ j₂ hj₂ h
    simp only [Finset.mem_range] at hj₁ hj₂
    have hj₁' : j₁ ≤ n := Nat.lt_succ_iff.mp hj₁
    have hj₂' : j₂ ≤ n := Nat.lt_succ_iff.mp hj₂
    have h' : n - j₁ = n - j₂ := h
    calc
      j₁ = n - (n - j₁) := (Nat.sub_sub_self hj₁').symm
      _ = n - (n - j₂) := by rw [h']
      _ = j₂ := Nat.sub_sub_self hj₂'
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨n - k, ?_, ?_⟩
    · simp only [Finset.mem_range]
      exact Nat.sub_lt_succ n k
    · exact Nat.sub_sub_self (Nat.lt_succ_iff.mp hk)
  · intro j hj
    simp only [Finset.mem_range] at hj
    have : n - (n - j) = j := Nat.sub_sub_self (Nat.lt_succ_iff.mp hj)
    simp [this]

/-- Window identity: three consecutive `g`-coefficients. -/
lemma g_window : ∀ t : ℕ,
    gCoeff t
      + (if t = 0 then 0 else gCoeff (t - 1))
      + (if t ≤ 1 then 0 else gCoeff (t - 2)) =
      if t = 0 then 1 else if t = 2 then (-1 : ℤ) else 0
  | 0 => by simp [gCoeff]
  | 1 => by simp [gCoeff]
  | 2 => by simp [gCoeff]
  | t + 3 => by
    have h := gCoeff_add_three t
    have e1 : t + 3 - 1 = t + 2 := by omega
    have e2 : t + 3 - 2 = t + 1 := by omega
    simp [e1, e2]
    linarith [h]

lemma U_sub_U (n : ℕ) (N : ℤ) (hn : 0 < n) :
    U n N - U (n - 1) (N - 2) =
      Ring.choose (N - 1) n - Ring.choose (N - 1) (n - 1) := by
  have hN2 : N = (N - 2) + 2 := by ring
  -- Treat the two cases n = 1 and n ≥ 2 separately.
  match n with
  | 0 => exact (Nat.lt_irrefl _ hn).elim
  | 1 =>
    unfold U
    simp [Finset.sum_range_succ, Finset.sum_range_zero, gCoeff_zero, gCoeff_one,
      Ring.choose_zero_right, Ring.choose_one_right]
    ring
  | n + 2 =>
    -- Use the reindexed form and Pascal expansion of C(N,·).
    rw [U_eq_reindex, U_eq_reindex]
    have hexp : ∀ k : ℕ,
        Ring.choose N k =
          Ring.choose (N - 2) k
            + (if k = 0 then 0 else 2 * Ring.choose (N - 2) (k - 1))
            + (if k ≤ 1 then 0 else Ring.choose (N - 2) (k - 2)) := by
      intro k
      conv_lhs => rw [hN2]
      simpa using ringChoose_add_two (N - 2) k
    -- Expand and reindex the three pieces. We work with n' := n+2.
    -- After a long but elementary calculation the difference equals
    -- C(N-2, n+2) - C(N-2, n), which is the claim by `choose_sub_choose_eq`.
    -- Direct expansion:
    simp only [hexp]
    -- Isolate the three summands
    have hsplit :
        ∑ k ∈ Finset.range (n + 3), gCoeff (n + 2 - k) *
            (Ring.choose (N - 2) k
              + (if k = 0 then 0 else 2 * Ring.choose (N - 2) (k - 1))
              + (if k ≤ 1 then 0 else Ring.choose (N - 2) (k - 2))) =
          ∑ k ∈ Finset.range (n + 3), gCoeff (n + 2 - k) * Ring.choose (N - 2) k
          + ∑ k ∈ Finset.range (n + 3),
              gCoeff (n + 2 - k) * (if k = 0 then 0 else 2 * Ring.choose (N - 2) (k - 1))
          + ∑ k ∈ Finset.range (n + 3),
              gCoeff (n + 2 - k) * (if k ≤ 1 then 0 else Ring.choose (N - 2) (k - 2)) := by
      simp [mul_add, Finset.sum_add_distrib]
    rw [hsplit]
    -- Reindex the k≥1 sum
    have hsum1 :
        ∑ k ∈ Finset.range (n + 3),
            gCoeff (n + 2 - k) * (if k = 0 then 0 else 2 * Ring.choose (N - 2) (k - 1)) =
          2 * ∑ k ∈ Finset.range (n + 2),
            gCoeff (n + 1 - k) * Ring.choose (N - 2) k := by
      rw [Finset.sum_range_succ']
      have h0 : gCoeff (n + 2 - 0) * (if (0 : ℕ) = 0 then 0 else 2 * Ring.choose (N - 2) (0 - 1)) = 0 := by
        simp
      rw [h0, add_zero]
      have hterm : ∀ k : ℕ,
          gCoeff (n + 2 - (k + 1)) * (if k + 1 = 0 then 0 else 2 * Ring.choose (N - 2) (k + 1 - 1)) =
            2 * (gCoeff (n + 1 - k) * Ring.choose (N - 2) k) := by
        intro k
        have e1 : n + 2 - (k + 1) = n + 1 - k := by omega
        have e2 : k + 1 - 1 = k := by omega
        have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
        simp [hk, e1, e2]
        ring
      simp_rw [hterm]
      exact (Finset.mul_sum (Finset.range (n + 2))
        (fun k : ℕ => gCoeff (n + 1 - k) * Ring.choose (N - 2) k) (2 : ℤ)).symm
    -- Reindex the k≥2 sum
    have hsum2 :
        ∑ k ∈ Finset.range (n + 3),
            gCoeff (n + 2 - k) * (if k ≤ 1 then 0 else Ring.choose (N - 2) (k - 2)) =
          ∑ k ∈ Finset.range (n + 1),
            gCoeff (n - k) * Ring.choose (N - 2) k := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hz0 : gCoeff (n + 2 - 0) * (if (0 : ℕ) ≤ 1 then 0 else Ring.choose (N - 2) (0 - 2)) = 0 := by
        simp
      have hz1 : gCoeff (n + 2 - 1) * (if (1 : ℕ) ≤ 1 then 0 else Ring.choose (N - 2) (1 - 2)) = 0 := by
        simp
      rw [hz0, hz1, add_zero, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e1 : n + 2 - (k + 1 + 1) = n - k := by omega
      have e2 : k + 1 + 1 - 2 = k := by omega
      have hk : ¬ k + 1 + 1 ≤ 1 := by omega
      simp [hk, e1, e2]
    rw [hsum1, hsum2]
    have hrng : n + 2 - 1 + 1 = n + 2 := by omega
    have hidx : ∀ k : ℕ, n + 2 - 1 - k = n + 1 - k := by intro k; omega
    simp_rw [hrng, hidx]
    -- 2 * middle - middle = middle
    have hcomb :
        ∑ k ∈ Finset.range (n + 3), gCoeff (n + 2 - k) * Ring.choose (N - 2) k
          + 2 * ∑ k ∈ Finset.range (n + 2), gCoeff (n + 1 - k) * Ring.choose (N - 2) k
          + ∑ k ∈ Finset.range (n + 1), gCoeff (n - k) * Ring.choose (N - 2) k
          - ∑ k ∈ Finset.range (n + 2), gCoeff (n + 1 - k) * Ring.choose (N - 2) k
        = ∑ k ∈ Finset.range (n + 3), gCoeff (n + 2 - k) * Ring.choose (N - 2) k
          + ∑ k ∈ Finset.range (n + 2), gCoeff (n + 1 - k) * Ring.choose (N - 2) k
          + ∑ k ∈ Finset.range (n + 1), gCoeff (n - k) * Ring.choose (N - 2) k := by
      ring
    rw [hcomb]
    -- Peel k = n+2 from the first sum (equals C(N-2, n+2))
    rw [Finset.sum_range_succ]
    have hn2 : n + 2 - (n + 2) = 0 := Nat.sub_self _
    simp only [hn2, gCoeff_zero, one_mul]
    -- Peel k = n+1 from the first two remaining sums
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hid1 : n + 2 - (n + 1) = 1 := by omega
    have hid0 : n + 1 - (n + 1) = 0 := Nat.sub_self _
    simp only [hid1, hid0]
    -- k = n+1 contributes (g1 + g0) C(N-2, n+1) = 0
    have hg10 : gCoeff 1 + gCoeff 0 = 0 := by simp [gCoeff]
    -- Peel k = n from all three remaining sums
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have hid2 : n + 2 - n = 2 := by omega
    have hid1' : n + 1 - n = 1 := by omega
    have hid00 : n - n = 0 := Nat.sub_self _
    simp only [hid2, hid1', hid00]
    have hg210 : gCoeff 2 + gCoeff 1 + gCoeff 0 = -1 := by simp [gCoeff]
    have hz : ∀ k ∈ Finset.range n,
        gCoeff (n + 2 - k) + gCoeff (n + 1 - k) + gCoeff (n - k) = 0 := by
      intro k hk
      simp only [Finset.mem_range] at hk
      have : 3 ≤ n + 2 - k := by omega
      have h := gCoeff_sum_three this
      have e1 : n + 2 - k - 1 = n + 1 - k := by omega
      have e2 : n + 2 - k - 2 = n - k := by omega
      simpa [e1, e2] using h
    have hrest :
        ∑ k ∈ Finset.range n, gCoeff (n + 2 - k) * Ring.choose (N - 2) k
          + ∑ k ∈ Finset.range n, gCoeff (n + 1 - k) * Ring.choose (N - 2) k
          + ∑ k ∈ Finset.range n, gCoeff (n - k) * Ring.choose (N - 2) k = 0 := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkz := hz k hk
      calc
        gCoeff (n + 2 - k) * Ring.choose (N - 2) k
          + gCoeff (n + 1 - k) * Ring.choose (N - 2) k
          + gCoeff (n - k) * Ring.choose (N - 2) k
            = (gCoeff (n + 2 - k) + gCoeff (n + 1 - k) + gCoeff (n - k))
                * Ring.choose (N - 2) k := by ring
        _ = 0 * Ring.choose (N - 2) k := by rw [hkz]
        _ = 0 := by simp
    have hcs : Ring.choose (N - 2) (n + 2) - Ring.choose (N - 2) n =
        Ring.choose (N - 1) (n + 2) - Ring.choose (N - 1) (n + 1) := by
      simpa using choose_sub_choose_eq N (n := n + 2) (Nat.succ_pos _)
    -- Normalize `1+n-(1+n)` appearing after `sum_range_succ`.
    simp only [Nat.sub_self]
    -- The peeled expression equals
    --   C(N-2,n+2) + (g₁+g₀) C(N-2,n+1) + (g₂+g₁+g₀) C(N-2,n) + rest
    -- with rest = 0, g₁+g₀ = 0 and g₂+g₁+g₀ = -1.
    trans Ring.choose (N - 2) (n + 2) - Ring.choose (N - 2) n
    · have hcollect :
          (∑ k ∈ Finset.range n, gCoeff (n + 2 - k) * Ring.choose (N - 2) k
            + ∑ k ∈ Finset.range n, gCoeff (n + 1 - k) * Ring.choose (N - 2) k
            + ∑ k ∈ Finset.range n, gCoeff (n - k) * Ring.choose (N - 2) k)
            + (gCoeff 1 + gCoeff 0) * Ring.choose (N - 2) (n + 1)
            + (gCoeff 2 + gCoeff 1 + gCoeff 0) * Ring.choose (N - 2) n
            + Ring.choose (N - 2) (n + 2)
          = Ring.choose (N - 2) (n + 2) - Ring.choose (N - 2) n := by
        rw [hrest, hg10, hg210]; ring
      convert hcollect using 1
      ring
    · exact hcs

lemma catalanTrue_eq_choose_sub (r : ℤ) {n : ℕ} (hn : 0 < n) :
    catalanTrue r n =
      Ring.choose (r + 2 * n - 1) n - Ring.choose (r + 2 * n - 1) (n - 1) := by
  simp [catalanTrue, hn.ne']

lemma S_eq_U (n : ℕ) (r : ℤ) :
    (Finset.range (n + 1)).sum (fun k => catalanTrue r k) = U n (r + 2 * n) := by
  induction n with
  | zero =>
    simp [U, catalanTrue, gCoeff]
  | succ n ih =>
    have hpos : 0 < n + 1 := Nat.succ_pos _
    rw [Finset.sum_range_succ, ih]
    have hU := U_sub_U (n + 1) (r + 2 * ((n + 1 : ℕ) : ℤ)) (Nat.succ_pos _)
    have hN : r + 2 * ((n + 1 : ℕ) : ℤ) - 2 = r + 2 * (n : ℤ) := by
      push_cast; ring
    simp only [Nat.succ_sub_succ_eq_sub, tsub_zero] at hU
    rw [hN] at hU
    have hcat := catalanTrue_eq_choose_sub r hpos
    simp only [Nat.add_sub_cancel] at hcat
    linarith [hU, hcat]

lemma aTrue_eq_U (m : ℤ) (n : ℕ) : aTrue m n = U n (n * (m + 2)) := by
  unfold aTrue
  split_ifs with hn
  · subst hn; simp [U, gCoeff]
  · rw [S_eq_U]
    congr 1
    ring

lemma a_gen_eq_aTrue_of_ne_neg_one (m : ℤ) (n : ℕ) (hm : m ≠ -1) :
    a_gen m n = aTrue m n := by
  unfold a_gen aTrue
  split_ifs with hn
  · rfl
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0, generalized_catalan_coefficient, catalanTrue]
    · have hden : m * n + k ≠ 0 := by
        intro h
        have hkmem : k ∈ Finset.range (n + 1) := hk
        have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkmem)
        have : m * (n : ℤ) = -k := by linarith
        have hm0 : m = -1 := by
          have hn0 : n ≠ 0 := fun h0 => by subst h0; omega
          have : m * (n : ℤ) = -1 * (n : ℤ) := by
            have hk_eq : (k : ℤ) = n := by
              have hmn : m * (n : ℤ) ≤ -1 := by
                have : (k : ℤ) ≥ 1 := by exact_mod_cast Nat.pos_of_ne_zero hk0
                linarith
              have hmn' : m * (n : ℤ) ≥ -n := by
                have : (k : ℤ) ≤ n := by exact_mod_cast hkle
                linarith
              have hnpos : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
              have hm_le : m ≤ -1 := by nlinarith
              have hm_ge : m ≥ -1 := by nlinarith
              have : m = -1 := le_antisymm hm_le hm_ge
              subst this
              nlinarith
            simpa [hk_eq]
          have hnpos : (n : ℤ) ≠ 0 := by exact_mod_cast hn0
          exact mul_right_cancel₀ hnpos this
        exact hm hm0
      rw [generalized_catalan_eq_diff _ _ hden]
      rfl

lemma a_gen_neg_one (n : ℕ) (hn : n ≠ 0) : a_gen (-1) n = aTrue (-1) n + 1 := by
  unfold a_gen aTrue
  simp [hn]
  have hsplit := Finset.sum_erase_add (Finset.range (n + 1))
    (fun k => generalized_catalan_coefficient (-n) k) (Finset.self_mem_range_succ n)
  have hsplit' := Finset.sum_erase_add (Finset.range (n + 1))
    (fun k => catalanTrue (-n) k) (Finset.self_mem_range_succ n)
  rw [← hsplit, ← hsplit']
  have heq : ∀ k ∈ (Finset.range (n + 1)).erase n,
      generalized_catalan_coefficient (-n) k = catalanTrue (-n) k := by
    intro k hk
    have hkne : k ≠ n := (Finset.mem_erase.mp hk).1
    by_cases hk0 : k = 0
    · simp [hk0, generalized_catalan_coefficient, catalanTrue]
    · have hden : (-n : ℤ) + k ≠ 0 := by
        intro h; apply hkne; exact_mod_cast (Int.neg_inj.mp (by linarith) : (k : ℤ) = n)
      rw [generalized_catalan_eq_diff _ _ hden]; rfl
  have hsum : ∑ k ∈ (Finset.range (n + 1)).erase n,
      generalized_catalan_coefficient (-n) k =
      ∑ k ∈ (Finset.range (n + 1)).erase n, catalanTrue (-n) k :=
    Finset.sum_congr rfl heq
  have hlast_gen : generalized_catalan_coefficient (-n) n = 0 := by
    unfold generalized_catalan_coefficient
    simp [hn]
  have hlast_true : catalanTrue (-n) n = -1 := by
    unfold catalanTrue
    simp [hn]
    have hN : (-(n : ℤ) + 2 * n - 1) = n - 1 := by ring
    rw [hN]
    have h0 : Ring.choose ((n : ℤ) - 1) n = 0 := by
      rw [show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by
            rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one],
          Ring.choose_natCast]
      exact Nat.cast_eq_zero.mpr
        (Nat.choose_eq_zero_of_lt (Nat.sub_lt (Nat.pos_of_ne_zero hn) (by decide)))
    have h1 : Ring.choose ((n : ℤ) - 1) (n - 1) = 1 := by
      rw [show (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by
            rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn), Nat.cast_one],
          Ring.choose_natCast]
      simp
    rw [h0, h1]; norm_num
  linarith

-- ═══════════════════════════════════════════════════════════════════════
-- Section 2: Power series realisation of `U` and the Wolstenholme lift
-- ═══════════════════════════════════════════════════════════════════════

/-- Generating series `∑ gCoeff j • X^j`. -/
noncomputable def gSeries : PowerSeries ℤ :=
  PowerSeries.mk fun j => gCoeff j

lemma coeff_gSeries (j : ℕ) : (PowerSeries.coeff j) gSeries = gCoeff j :=
  PowerSeries.coeff_mk _ _

lemma U_eq_coeff (s : ℕ) (t : ℤ) :
    U s t = (PowerSeries.coeff s) (gSeries * PowerSeries.binomialSeries ℤ t) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (PowerSeries.coeff i) gSeries *
      (PowerSeries.coeff j) (PowerSeries.binomialSeries ℤ t)) s]
  unfold U
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [coeff_gSeries, PowerSeries.binomialSeries_coeff]

/-- Integer coefficients `φ_p(k) = binom(p,k)/p` for `0 < k < p`, else 0. -/
def phiCoeff (p k : ℕ) : ℤ :=
  if 0 < k ∧ k < p then (p.choose k : ℤ) / p else 0

lemma p_dvd_choose {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    (p : ℤ) ∣ (p.choose k : ℤ) := by
  have h := hp.dvd_choose_self (Nat.ne_zero_of_lt hk) hkp
  exact_mod_cast h

lemma phiCoeff_mul (p k : ℕ) (hp : p.Prime) :
    (p : ℤ) * phiCoeff p k =
      if 0 < k ∧ k < p then (p.choose k : ℤ) else 0 := by
  unfold phiCoeff
  split_ifs with h
  · have hdvd := p_dvd_choose hp h.1 h.2
    exact Int.mul_ediv_cancel' hdvd
  · simp

lemma phiCoeff_eq_choose_div (p k : ℕ) (hk : 0 < k) (hkp : k < p) :
    phiCoeff p k = (p.choose k : ℤ) / p := by
  simp [phiCoeff, hk, hkp]

lemma phiCoeff_zero (p : ℕ) : phiCoeff p 0 = 0 := by simp [phiCoeff]

lemma phiCoeff_self (p : ℕ) : phiCoeff p p = 0 := by simp [phiCoeff]

lemma phiCoeff_eq_zero_of_ge {p k : ℕ} (h : p ≤ k) : phiCoeff p k = 0 := by
  unfold phiCoeff
  simp [show ¬ k < p by omega]

/-- Power series of `Φ_p`. -/
noncomputable def phiSeries (p : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => phiCoeff p k

lemma coeff_phiSeries (p k : ℕ) : (PowerSeries.coeff k) (phiSeries p) = phiCoeff p k :=
  PowerSeries.coeff_mk _ _

lemma coeff_phiSeries_eq_zero_of_ge {p k : ℕ} (h : p ≤ k) :
    (PowerSeries.coeff k) (phiSeries p) = 0 := by
  rw [coeff_phiSeries, phiCoeff_eq_zero_of_ge h]

lemma ringChoose_nat (n k : ℕ) : Ring.choose (n : ℤ) k = n.choose k :=
  Ring.choose_natCast (R := ℤ) n k

lemma ringChoose_eq_zero_of_lt {n k : ℕ} (h : n < k) : Ring.choose (n : ℤ) k = 0 := by
  rw [ringChoose_nat]
  exact Nat.cast_eq_zero.mpr (Nat.choose_eq_zero_of_lt h)

/-- `(1+X)^p = 1 + X^p + p • Φ_p` as power series. -/
lemma binomialSeries_prime (p : ℕ) (hp : p.Prime) :
    PowerSeries.binomialSeries ℤ (p : ℤ) =
      1 + (PowerSeries.X : PowerSeries ℤ) ^ p + PowerSeries.C (p : ℤ) * phiSeries p := by
  ext n
  simp only [PowerSeries.binomialSeries_coeff, map_add, PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul, coeff_phiSeries]
  by_cases hn0 : n = 0
  · subst n
    have hp0 : ¬ 0 = p := hp.ne_zero.symm
    simp [phiCoeff, hp0]
  by_cases hnp : n = p
  · subst n
    simp [phiCoeff, hp.ne_zero, ringChoose_nat, Nat.choose_self]
  · simp [hnp, hn0]
    by_cases hlt : n < p
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      rw [phiCoeff_eq_choose_div p n hnpos hlt]
      have hdvd := p_dvd_choose hp hnpos hlt
      rw [Int.mul_ediv_cancel' hdvd, ringChoose_nat]
    · have hgt : p < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hnp)
      rw [phiCoeff_eq_zero_of_ge (le_of_lt hgt)]
      simp [ringChoose_eq_zero_of_lt hgt]

-- Period-6 correction: `3 * ∑_{k≡r} binom(n,k) = 2^n + cubeCorrShift r n`.
def cubeCorr (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 2 | 1 => 1 | 2 => -1 | 3 => -2 | 4 => -1 | 5 => 1 | _ => 0

lemma cubeCorr_mod (n : ℕ) :
    cubeCorr n =
      if n % 6 = 0 then (2 : ℤ)
      else if n % 6 = 1 then 1
      else if n % 6 = 2 then -1
      else if n % 6 = 3 then -2
      else if n % 6 = 4 then -1
      else 1 := by
  have hlt : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  interval_cases h : n % 6 <;> simp [cubeCorr, h]

lemma cubeCorr_rec (n : ℕ) : cubeCorr (n + 2) = cubeCorr (n + 1) - cubeCorr n := by
  have h0 : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  have h1 : (n + 1) % 6 = (n % 6 + 1) % 6 := Nat.add_mod _ _ _
  have h2 : (n + 2) % 6 = (n % 6 + 2) % 6 := Nat.add_mod _ _ _
  interval_cases h : n % 6 <;> simp [cubeCorr_mod, h1, h2, h]

/-- `∑_{k≡r (mod 3), k≤n} binom(n,k)`. -/
def chooseMod3 (n r : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if k % 3 = r % 3 then (n.choose k : ℤ) else 0

lemma add_mod_three_succ (j r : ℕ) :
    ((j + 1) % 3 = r % 3) ↔ (j % 3 = (r + 2) % 3) := by
  have h1 : (j + 1) % 3 = (j % 3 + 1) % 3 := Nat.add_mod _ _ _
  have h2 : (r + 2) % 3 = (r % 3 + 2) % 3 := Nat.add_mod _ _ _
  have hj : j % 3 < 3 := Nat.mod_lt j (by norm_num)
  have hr : r % 3 < 3 := Nat.mod_lt r (by norm_num)
  omega

lemma choose_succ_int (n k : ℕ) (hk : 0 < k) :
    ((n + 1).choose k : ℤ) = n.choose k + n.choose (k - 1) := by
  have hk' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  rw [hk', Nat.choose_succ_succ]
  push_cast; ring

lemma chooseMod3_mod (n r : ℕ) : chooseMod3 n r = chooseMod3 n (r % 3) := by
  unfold chooseMod3
  simp [Nat.mod_mod]

lemma chooseMod3_succ (n r : ℕ) :
    chooseMod3 (n + 1) r = chooseMod3 n r + chooseMod3 n ((r + 2) % 3) := by
  unfold chooseMod3
  have hr : ((r + 2) % 3) % 3 = (r + 2) % 3 := Nat.mod_mod _ _
  simp_rw [hr]
  rw [Finset.sum_range_succ']
  have hterm : ∀ k : ℕ,
      (if (k + 1) % 3 = r % 3 then ((n + 1).choose (k + 1) : ℤ) else 0) =
        (if (k + 1) % 3 = r % 3 then (n.choose k : ℤ) else 0) +
        (if (k + 1) % 3 = r % 3 then (n.choose (k + 1) : ℤ) else 0) := by
    intro k
    have hch : ((n + 1).choose (k + 1) : ℤ) =
        (n.choose k : ℤ) + (n.choose (k + 1) : ℤ) := by
      simp [Nat.choose_succ_succ]
    split_ifs with hk
    · exact hch
    · rfl
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  have hfirst :
      ∑ k ∈ Finset.range (n + 1),
          (if (k + 1) % 3 = r % 3 then (n.choose k : ℤ) else 0) =
        ∑ k ∈ Finset.range (n + 1),
          (if k % 3 = (r + 2) % 3 then (n.choose k : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k + 1) % 3 = r % 3
    · have hk' : k % 3 = (r + 2) % 3 := (add_mod_three_succ k r).mp hk
      simp [hk, hk']
    · have hk' : ¬ k % 3 = (r + 2) % 3 := mt (add_mod_three_succ k r).mpr hk
      simp [hk, hk']
  have h0 : ((n + 1).choose 0 : ℤ) = 1 := by simp
  have hsecond :
      ∑ k ∈ Finset.range (n + 1),
          (if (k + 1) % 3 = r % 3 then (n.choose (k + 1) : ℤ) else 0) =
        (∑ k ∈ Finset.range (n + 1),
          (if k % 3 = r % 3 then (n.choose k : ℤ) else 0)) -
        (if (0 : ℕ) % 3 = r % 3 then (1 : ℤ) else 0) := by
    have hsum := Finset.sum_range_succ'
      (fun j => if j % 3 = r % 3 then (n.choose j : ℤ) else 0) n
    have htail :
        ∑ k ∈ Finset.range n,
            (if (k + 1) % 3 = r % 3 then (n.choose (k + 1) : ℤ) else 0) =
          (∑ j ∈ Finset.range (n + 1),
            (if j % 3 = r % 3 then (n.choose j : ℤ) else 0)) -
          (if (0 : ℕ) % 3 = r % 3 then (n.choose 0 : ℤ) else 0) := by
      linarith [hsum]
    rw [Finset.sum_range_succ]
    have hlast : (n.choose (n + 1) : ℤ) = 0 := by
      simp [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]
    have : (if (n + 1) % 3 = r % 3 then (n.choose (n + 1) : ℤ) else 0) = 0 := by
      simp [hlast]
    rw [this, add_zero, htail]
    simp
  have hz :
      (if (0 : ℕ) % 3 = r % 3 then ((n + 1).choose 0 : ℤ) else 0) =
        if (0 : ℕ) % 3 = r % 3 then (1 : ℤ) else 0 := by
    simp [h0]
  rw [hz, hfirst, hsecond]
  ring

lemma cubeCorr_add_three (n : ℕ) : cubeCorr (n + 3) = -cubeCorr n := by
  have h0 : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  have h3 : (n + 3) % 6 = (n % 6 + 3) % 6 := Nat.add_mod _ _ _
  interval_cases h : n % 6 <;> simp [cubeCorr_mod, h3, h]

/-- The period-6 correction attached to residue class `r`. -/
def cubeCorrShift (r n : ℕ) : ℤ :=
  if r % 3 = 0 then cubeCorr n
  else if r % 3 = 1 then cubeCorr (n + 4)
  else cubeCorr (n + 2)

lemma cubeCorrShift_succ (r n : ℕ) :
    cubeCorrShift r n + cubeCorrShift (r + 2) n = cubeCorrShift r (n + 1) := by
  have hr : r % 3 < 3 := Nat.mod_lt r (by norm_num)
  have h2 : (r + 2) % 3 = (r % 3 + 2) % 3 := Nat.add_mod _ _ _
  interval_cases h : r % 3
  · -- r ≡ 0: cubeCorr n + cubeCorr (n+2) = cubeCorr (n+1)
    simp [cubeCorrShift, h, h2]
    have := cubeCorr_rec n
    linarith
  · -- r ≡ 1: cubeCorr (n+4) + cubeCorr n = cubeCorr (n+5)
    simp [cubeCorrShift, h, h2]
    -- cubeCorr (n+5) = cubeCorr (n+4) - cubeCorr (n+3) and cubeCorr (n+3) = -cubeCorr n
    have h54 : cubeCorr (n + 5) = cubeCorr (n + 4) - cubeCorr (n + 3) := by
      simpa [Nat.add_assoc] using cubeCorr_rec (n + 3)
    have h3 : cubeCorr (n + 3) = -cubeCorr n := cubeCorr_add_three n
    linarith
  · -- r ≡ 2: cubeCorr (n+2) + cubeCorr (n+4) = cubeCorr (n+3)
    simp [cubeCorrShift, h, h2]
    have h42 : cubeCorr (n + 4) = cubeCorr (n + 3) - cubeCorr (n + 2) := by
      simpa [Nat.add_assoc] using cubeCorr_rec (n + 2)
    linarith

lemma chooseMod3_formula (n r : ℕ) :
    3 * chooseMod3 n r = (2 : ℤ) ^ n + cubeCorrShift r n := by
  induction n generalizing r with
  | zero =>
    unfold chooseMod3 cubeCorrShift
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
      Nat.cast_one, Nat.zero_mod]
    have hr : r % 3 < 3 := Nat.mod_lt r (by norm_num)
    interval_cases h : r % 3 <;> simp [h, cubeCorr_mod]
  | succ n ih =>
    have hmod : cubeCorrShift ((r + 2) % 3) n = cubeCorrShift (r + 2) n := by
      unfold cubeCorrShift
      simp
    rw [chooseMod3_succ, mul_add, ih, ih, hmod]
    have hs := cubeCorrShift_succ r n
    have hpow : (2 : ℤ) ^ n + (2 : ℤ) ^ n = (2 : ℤ) ^ (n + 1) := by
      rw [pow_succ]; ring
    linarith [hs, hpow]

lemma chooseMod3_eq_of_mod (n r₁ r₂ : ℕ) (h : r₁ % 3 = r₂ % 3) :
    chooseMod3 n r₁ = chooseMod3 n r₂ := by
  unfold chooseMod3
  simp [h]

/-- Interior residue sum `∑_{1 ≤ k ≤ n-1, k ≡ r} binom(n,k)`. -/
def chooseMod3Interior (n r : ℕ) : ℤ :=
  chooseMod3 n r
    - (if (0 : ℕ) % 3 = r % 3 then (1 : ℤ) else 0)
    - (if n % 3 = r % 3 then (1 : ℤ) else 0)

lemma chooseMod3_interior_eq (n r : ℕ) (hn : 0 < n) :
    chooseMod3Interior n r =
      ∑ k ∈ Finset.Icc 1 (n - 1),
        if k % 3 = r % 3 then (n.choose k : ℤ) else 0 := by
  unfold chooseMod3Interior chooseMod3
  have hsplit := Finset.sum_range_succ'
    (fun k => if k % 3 = r % 3 then (n.choose k : ℤ) else 0) n
  -- ∑_{k=0}^n = f(0) + ∑_{k=0}^{n-1} f(k+1)
  rw [Finset.sum_range_succ] -- peel k = n
  have hself : (n.choose n : ℤ) = 1 := by simp
  have hrng : Finset.range n = insert 0 (Finset.Icc 1 (n - 1)) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hdisj : (0 : ℕ) ∉ Finset.Icc 1 (n - 1) := by
    simp [Finset.mem_Icc]
  rw [hrng, Finset.sum_insert hdisj]
  simp [hself]
  ring

lemma prime_ge_five_mod_six {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hlt : p % 6 < 6 := Nat.mod_lt p (by norm_num)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have h3 : p % 3 ≠ 0 := by
    intro h
    exact three_not_dvd_of_prime_ge_five hp hp5 (Nat.dvd_of_mod_eq_zero h)
  omega

/-- For a prime `p ≥ 5`, the three interior residue sums of `binom(p,·)` equal `(2^p-2)/3`. -/
lemma chooseMod3_interior_prime {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (r : ℕ) :
    chooseMod3Interior p r = ((2 : ℤ) ^ p - 2) / 3 := by
  have hform := chooseMod3_formula p r
  have h6 := prime_ge_five_mod_six hp hp5
  have hgoal : cubeCorrShift r p
      - (if (0 : ℕ) % 3 = r % 3 then (3 : ℤ) else 0)
      - (if p % 3 = r % 3 then (3 : ℤ) else 0) = -2 := by
    unfold cubeCorrShift
    rcases h6 with h6 | h6
    · have hp3 : p % 3 = 1 := by omega
      have hc0 : cubeCorr p = 1 := by simp [cubeCorr_mod, h6]
      have hc1 : cubeCorr (p + 4) = 1 := by
        have : (p + 4) % 6 = 5 := by omega
        simp [cubeCorr_mod, this]
      have hc2 : cubeCorr (p + 2) = -2 := by
        have : (p + 2) % 6 = 3 := by omega
        simp [cubeCorr_mod, this]
      have hr : r % 3 < 3 := Nat.mod_lt r (by norm_num)
      interval_cases hr' : r % 3 <;> simp [hr', hp3, hc0, hc1, hc2]
    · have hp3 : p % 3 = 2 := by omega
      have hc0 : cubeCorr p = 1 := by simp [cubeCorr_mod, h6]
      have hc1 : cubeCorr (p + 4) = -2 := by
        have : (p + 4) % 6 = 3 := by omega
        simp [cubeCorr_mod, this]
      have hc2 : cubeCorr (p + 2) = 1 := by
        have : (p + 2) % 6 = 1 := by omega
        simp [cubeCorr_mod, this]
      have hr : r % 3 < 3 := Nat.mod_lt r (by norm_num)
      interval_cases hr' : r % 3 <;> simp [hr', hp3, hc0, hc1, hc2]
  have hinter : 3 * chooseMod3Interior p r = (2 : ℤ) ^ p - 2 := by
    unfold chooseMod3Interior
    have hb0 : (3 : ℤ) * (if (0 : ℕ) % 3 = r % 3 then (1 : ℤ) else 0) =
        if (0 : ℕ) % 3 = r % 3 then (3 : ℤ) else 0 := by
      split_ifs <;> simp
    have hbp : (3 : ℤ) * (if p % 3 = r % 3 then (1 : ℤ) else 0) =
        if p % 3 = r % 3 then (3 : ℤ) else 0 := by
      split_ifs <;> simp
    linarith [hform, hgoal, hb0, hbp]
  have h3ne : (3 : ℤ) ≠ 0 := by norm_num
  exact Int.eq_ediv_of_mul_eq_right h3ne hinter

lemma three_mul_chooseMod3Interior {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (r : ℕ) :
    3 * chooseMod3Interior p r = (2 : ℤ) ^ p - 2 := by
  have h := chooseMod3_interior_prime hp hp5 r
  have hdvd : (3 : ℤ) ∣ (2 : ℤ) ^ p - 2 := by
    have : (2 : ℤ) ^ p ≡ 2 [ZMOD 3] := by
      have h2 : (2 : ℤ) ≡ -1 [ZMOD 3] := by decide
      have hp2 : (2 : ℤ) ^ p ≡ (-1 : ℤ) ^ p [ZMOD 3] := h2.pow p
      have hneg : (-1 : ℤ) ^ p = -1 := Odd.neg_one_pow (hp.odd_of_ne_two (by omega))
      have : (-1 : ℤ) ≡ 2 [ZMOD 3] := by decide
      rw [hneg] at hp2
      exact hp2.trans this
    have hdvd' := Int.modEq_iff_dvd.mp this
    -- hdvd' : 3 ∣ 2 - 2^p
    have : (2 : ℤ) - 2 ^ p = -((2 : ℤ) ^ p - 2) := by ring
    rw [this] at hdvd'
    exact dvd_neg.mp hdvd'
  rw [h, Int.mul_ediv_cancel' hdvd]

lemma ringChoose_symm_nat (N k : ℕ) (hk : k ≤ N) :
    Ring.choose (N : ℤ) k = Ring.choose (N : ℤ) (N - k) := by
  rw [ringChoose_nat, ringChoose_nat, Nat.choose_symm hk]

lemma U_double (n : ℕ) : U n ((2 * n : ℕ) : ℤ) = 1 := by
  induction n with
  | zero => simp [U, gCoeff]
  | succ n ih =>
    have hpos : 0 < n + 1 := Nat.succ_pos _
    have hU := U_sub_U (n + 1) ((2 * (n + 1) : ℕ) : ℤ) hpos
    have hN : ((2 * (n + 1) : ℕ) : ℤ) - 2 = ((2 * n : ℕ) : ℤ) := by
      push_cast; ring
    simp only [Nat.succ_sub_succ_eq_sub, tsub_zero] at hU
    rw [hN] at hU
    have hsym : Ring.choose (((2 * (n + 1) : ℕ) : ℤ) - 1) (n + 1) =
        Ring.choose (((2 * (n + 1) : ℕ) : ℤ) - 1) n := by
      have hcast : ((2 * (n + 1) : ℕ) : ℤ) - 1 = ((2 * n + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [hcast]
      have hk : n + 1 ≤ 2 * n + 1 := by omega
      convert ringChoose_symm_nat (2 * n + 1) (n + 1) hk using 2
      omega
    linarith [hU, ih, hsym]

lemma sub_mod_eq_zero_iff (a b : ℕ) (hba : b ≤ a) :
    (a - b) % 3 = 0 ↔ a % 3 = b % 3 := by
  constructor
  · intro h
    have hsum : a = (a - b) + b := (Nat.sub_add_cancel hba).symm
    rw [hsum, Nat.add_mod, h]
    simp
  · intro h
    have hsum : ((a - b) + b) % 3 = a % 3 := by
      rw [Nat.sub_add_cancel hba]
    rw [Nat.add_mod, h] at hsum
    have : ((a - b) % 3 + b % 3) % 3 = b % 3 := hsum
    have hb : b % 3 < 3 := Nat.mod_lt b (by norm_num)
    have ha : (a - b) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega

lemma sum_range_choose_int (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) = (2 : ℤ) ^ n := by
  simpa using congrArg (fun m : ℕ => (m : ℤ)) (Nat.sum_range_choose n)

lemma sum_Icc_choose_int (p : ℕ) (hp : 0 < p) :
    ∑ j ∈ Finset.Icc 1 (p - 1), (p.choose j : ℤ) = (2 : ℤ) ^ p - 2 := by
  have htot := sum_range_choose_int p
  have hrng : Finset.range (p + 1) = insert p (insert 0 (Finset.Icc 1 (p - 1))) := by
    ext k; simp [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0i : (0 : ℕ) ∉ Finset.Icc 1 (p - 1) := by simp [Finset.mem_Icc]
  have hpi : p ∉ insert 0 (Finset.Icc 1 (p - 1)) := by
    simp [Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hrng, Finset.sum_insert hpi, Finset.sum_insert h0i] at htot
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at htot
  linarith

lemma chooseMod3Interior_mod (n r : ℕ) :
    chooseMod3Interior n r = chooseMod3Interior n (r % 3) := by
  unfold chooseMod3Interior chooseMod3
  simp [Nat.mod_mod]

lemma chooseMod3Interior_Icc (n r : ℕ) (hn : 0 < n) :
    chooseMod3Interior n r =
      ∑ k ∈ Finset.Icc 1 (n - 1),
        if k % 3 = r % 3 then (n.choose k : ℤ) else 0 :=
  chooseMod3_interior_eq n r hn

lemma gCoeff_eq_neg_add_three {k : ℕ} (hk : k ≠ 0) :
    gCoeff k = -1 + 3 * (if k % 3 = 0 then (1 : ℤ) else 0) := by
  rw [gCoeff_pos hk]
  split_ifs <;> simp

/-- Weighted sum appearing in `[X^{pM}] g Φ`. -/
lemma sum_choose_mul_gCoeff {p M : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (hM : 0 < M) :
    ∑ j ∈ Finset.Icc 1 (p - 1), (p.choose j : ℤ) * gCoeff (p * M - j) = 0 := by
  have hp0 : 0 < p := hp.pos
  have hterm : ∀ j ∈ Finset.Icc 1 (p - 1),
      (p.choose j : ℤ) * gCoeff (p * M - j) =
        -(p.choose j : ℤ) +
          3 * (if j % 3 = (p * M) % 3 then (p.choose j : ℤ) else 0) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hjm : j ≤ p * M := by
      have : p ≤ p * M := Nat.le_mul_of_pos_right p hM
      omega
    have hpos : p * M - j ≠ 0 := by
      have : j < p * M := by
        have : j < p := by omega
        have : p ≤ p * M := Nat.le_mul_of_pos_right p hM
        omega
      omega
    rw [gCoeff_eq_neg_add_three hpos]
    have hiff : (p * M - j) % 3 = 0 ↔ (p * M) % 3 = j % 3 :=
      sub_mod_eq_zero_iff (p * M) j hjm
    have hiff' : (p * M - j) % 3 = 0 ↔ j % 3 = (p * M) % 3 := by
      rw [hiff]; exact eq_comm
    simp only [mul_add, mul_neg, mul_one]
    by_cases hdiv : (p * M - j) % 3 = 0
    · have : j % 3 = (p * M) % 3 := hiff'.mp hdiv
      simp [hdiv, this]
      ring
    · have : j % 3 ≠ (p * M) % 3 := mt hiff'.mpr hdiv
      simp [hdiv, this]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hneg : ∑ j ∈ Finset.Icc 1 (p - 1), (-(p.choose j : ℤ)) = -((2 : ℤ) ^ p - 2) := by
    rw [Finset.sum_neg_distrib, sum_Icc_choose_int p hp0]
  have hind :
      ∑ j ∈ Finset.Icc 1 (p - 1),
          3 * (if j % 3 = (p * M) % 3 then (p.choose j : ℤ) else 0) =
        3 * chooseMod3Interior p (p * M) := by
    have hI := chooseMod3Interior_Icc p (p * M) hp0
    rw [hI, Finset.mul_sum]
  rw [hneg, hind, three_mul_chooseMod3Interior hp hp5 (p * M)]
  ring

/-- Finite-sum coefficient of `g Φ` at degree `pM`. -/
def gPhiCoeff (p M : ℕ) : ℤ :=
  if M = 0 then 0
  else ∑ k ∈ Finset.Icc 1 (p - 1), gCoeff (p * M - k) * phiCoeff p k

lemma gPhiCoeff_eq_zero {p M : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    gPhiCoeff p M = 0 := by
  unfold gPhiCoeff
  split_ifs with hM
  · rfl
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    have hdiv : ∀ k ∈ Finset.Icc 1 (p - 1),
        phiCoeff p k = (p.choose k : ℤ) / p := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      exact phiCoeff_eq_choose_div p k (by omega) (by omega)
    rw [Finset.sum_congr rfl fun k hk => by rw [hdiv k hk]]
    have hmul :
        (p : ℤ) * ∑ k ∈ Finset.Icc 1 (p - 1),
            gCoeff (p * M - k) * ((p.choose k : ℤ) / p) =
          ∑ k ∈ Finset.Icc 1 (p - 1), (p.choose k : ℤ) * gCoeff (p * M - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have hdvd := p_dvd_choose hp (by omega : 0 < k) (by omega : k < p)
      rw [mul_left_comm, Int.mul_ediv_cancel' hdvd]
      ring
    have hsum0 := sum_choose_mul_gCoeff hp hp5 hMpos
    have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hprod :
        (p : ℤ) * ∑ k ∈ Finset.Icc 1 (p - 1),
            gCoeff (p * M - k) * ((p.choose k : ℤ) / p) = 0 := by
      rw [hmul]
      simpa [mul_comm] using hsum0
    exact (Int.mul_eq_zero.mp hprod).resolve_left hpne

/-- `Yp = X^p + p Φ`. -/
noncomputable def Yp (p : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ p + PowerSeries.C (p : ℤ) * phiSeries p

lemma binomial_eq_one_add_Yp (p : ℕ) (hp : p.Prime) :
    PowerSeries.binomialSeries ℤ (p : ℤ) = 1 + Yp p := by
  rw [binomialSeries_prime p hp]
  simp only [Yp]
  abel

lemma constantCoeff_Yp (p : ℕ) (hp : 0 < p) :
    PowerSeries.constantCoeff (Yp p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  unfold Yp
  rw [map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul, coeff_phiSeries]
  have : ¬ 0 = p := Ne.symm (Nat.ne_of_gt hp)
  simp [this, phiCoeff_zero]

lemma binomialSeries_nat_mul_p (p B : ℕ) (hp : p.Prime) :
    PowerSeries.binomialSeries ℤ ((p : ℤ) * B) = (1 + Yp p) ^ B := by
  have hcast : ((p * B : ℕ) : ℤ) = (p : ℤ) * (B : ℤ) := by
    simp [Nat.cast_mul]
  have h1 := PowerSeries.binomialSeries_nat (R := ℤ) (A := ℤ) (p * B)
  rw [← hcast, h1, pow_mul]
  have h2 : (1 + PowerSeries.X) ^ p = 1 + Yp p := by
    have h := PowerSeries.binomialSeries_nat (R := ℤ) (A := ℤ) p
    rw [← h, binomial_eq_one_add_Yp p hp]
  rw [h2]

lemma sum_choose_mul_gCoeff_id {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    ∑ j ∈ Finset.Icc 1 (p - 1), (p.choose j : ℤ) * gCoeff j = 0 := by
  -- same as sum_choose_mul_gCoeff with residue 0 (g_j instead of g_{p-j})
  have hp0 : 0 < p := hp.pos
  have hterm : ∀ j ∈ Finset.Icc 1 (p - 1),
      (p.choose j : ℤ) * gCoeff j =
        -(p.choose j : ℤ) + 3 * (if j % 3 = 0 then (p.choose j : ℤ) else 0) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have : j ≠ 0 := by omega
    rw [gCoeff_eq_neg_add_three this]
    simp [mul_add]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hneg : ∑ j ∈ Finset.Icc 1 (p - 1), (-(p.choose j : ℤ)) = -((2 : ℤ) ^ p - 2) := by
    rw [Finset.sum_neg_distrib, sum_Icc_choose_int p hp0]
  have hind :
      ∑ j ∈ Finset.Icc 1 (p - 1),
          3 * (if j % 3 = 0 then (p.choose j : ℤ) else 0) =
        3 * chooseMod3Interior p 0 := by
    have hI := chooseMod3Interior_Icc p 0 hp0
    rw [hI, Finset.mul_sum]
  rw [hneg, hind, three_mul_chooseMod3Interior hp hp5 0]
  ring

lemma U_p_p {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) : U p p = 0 := by
  unfold U
  -- U p p = ∑_{j=0}^p g_j C(p, p-j) = ∑ g_j C(p,j)
  have hre : ∑ j ∈ Finset.range (p + 1), gCoeff j * Ring.choose (p : ℤ) (p - j) =
      ∑ j ∈ Finset.range (p + 1), gCoeff j * Ring.choose (p : ℤ) j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_range] at hj
    have : p - j ≤ p := Nat.sub_le _ _
    rw [ringChoose_nat, ringChoose_nat, Nat.choose_symm (Nat.lt_succ_iff.mp hj)]
  rw [hre]
  have hpne : p ≠ 0 := hp.ne_zero
  have hgpen : gCoeff p = -1 := by
    have : p % 3 ≠ 0 := by
      intro h
      exact three_not_dvd_of_prime_ge_five hp hp5 (Nat.dvd_of_mod_eq_zero h)
    simp [gCoeff, hpne, this]
  have hsum :
      ∑ j ∈ Finset.range (p + 1), gCoeff j * Ring.choose (p : ℤ) j =
        1 + (∑ j ∈ Finset.Icc 1 (p - 1), (p.choose j : ℤ) * gCoeff j) + gCoeff p := by
    have hrng : Finset.range (p + 1) = insert p (insert 0 (Finset.Icc 1 (p - 1))) := by
      ext k; simp [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    have h0i : (0 : ℕ) ∉ Finset.Icc 1 (p - 1) := by simp
    have hpi : p ∉ insert 0 (Finset.Icc 1 (p - 1)) := by
      simp [Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrng, Finset.sum_insert hpi, Finset.sum_insert h0i]
    simp [gCoeff_zero, ringChoose_nat, mul_comm]
    abel
  rw [hsum, sum_choose_mul_gCoeff_id hp hp5, hgpen]
  ring

lemma gCoeff_pow_mul {p j : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    gCoeff (p * j) = gCoeff j :=
  gCoeff_mul_of_not_dvd_three (three_not_dvd_of_prime_ge_five hp hp5)

/-- The t = 0 term of the binomial expansion: `[X^{pA}] g (1+X^p)^B = U A B`. -/
lemma coeff_g_expand_binomial (p A : ℕ) (B : ℤ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (PowerSeries.coeff (p * A))
        (gSeries * PowerSeries.expand p hp.ne_zero (PowerSeries.binomialSeries ℤ B)) =
      U A B := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (PowerSeries.coeff i) gSeries *
        (PowerSeries.coeff j)
          (PowerSeries.expand p hp.ne_zero (PowerSeries.binomialSeries ℤ B))) (p * A)]
  have hp0 : 0 < p := hp.pos
  have hterm : ∀ i ∈ Finset.range (p * A + 1),
      (PowerSeries.coeff i) gSeries *
        (PowerSeries.coeff (p * A - i))
          (PowerSeries.expand p hp.ne_zero (PowerSeries.binomialSeries ℤ B)) =
        if p ∣ (p * A - i) then
          gCoeff i * Ring.choose B ((p * A - i) / p)
        else 0 := by
    intro i hi
    rw [coeff_gSeries]
    by_cases hdiv : p ∣ (p * A - i)
    · obtain ⟨m, hm⟩ := hdiv
      have hexp :
          (PowerSeries.coeff (p * A - i))
              (PowerSeries.expand p hp.ne_zero (PowerSeries.binomialSeries ℤ B)) =
            (PowerSeries.coeff m) (PowerSeries.binomialSeries ℤ B) := by
        rw [hm]
        simpa using
          (PowerSeries.coeff_expand_mul (R := ℤ) p hp.ne_zero
            (PowerSeries.binomialSeries ℤ B) m)
      have hdiv' : p ∣ p * A - i := ⟨m, hm⟩
      rw [hexp, PowerSeries.binomialSeries_coeff]
      simp [hdiv', hm, Nat.mul_div_right m hp0]
    · have hexp :
          (PowerSeries.coeff (p * A - i))
              (PowerSeries.expand p hp.ne_zero (PowerSeries.binomialSeries ℤ B)) = 0 := by
        simpa using
          (PowerSeries.coeff_expand_of_not_dvd (R := ℤ) p hp.ne_zero
            (PowerSeries.binomialSeries ℤ B) hdiv)
      simp [hdiv, hexp]
  rw [Finset.sum_congr rfl hterm]
  have hdvd_iff : ∀ i, i ≤ p * A → (p ∣ p * A - i ↔ p ∣ i) := by
    intro i hi
    constructor
    · intro h
      have hA : p ∣ p * A := dvd_mul_right p A
      have := Nat.dvd_sub hA h
      simpa [Nat.sub_sub_self hi] using this
    · intro h
      exact Nat.dvd_sub (dvd_mul_right p A) h
  have hre1 :
      ∑ i ∈ Finset.range (p * A + 1),
          (if p ∣ (p * A - i) then gCoeff i * Ring.choose B ((p * A - i) / p) else 0) =
        ∑ i ∈ Finset.range (p * A + 1),
          (if p ∣ i then gCoeff i * Ring.choose B ((p * A - i) / p) else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have hi' : i ≤ p * A := Nat.lt_succ_iff.mp hi
    simp [hdvd_iff i hi']
  have himg : ((Finset.range (p * A + 1)).filter (p ∣ ·)) =
      (Finset.range (A + 1)).image (fun j => p * j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨hi, hdiv⟩
      obtain ⟨j, rfl⟩ := hdiv
      refine ⟨j, ?_, rfl⟩
      have : p * j ≤ p * A := Nat.le_of_lt_succ hi
      exact Nat.lt_succ_iff.mpr (Nat.le_of_mul_le_mul_left this hp0)
    · intro ⟨j, hj, hji⟩
      subst hji
      constructor
      · have : j ≤ A := Nat.lt_succ_iff.mp hj
        have : p * j ≤ p * A := Nat.mul_le_mul_left p this
        omega
      · exact dvd_mul_right _ _
  have hre2 :
      ∑ i ∈ Finset.range (p * A + 1),
          (if p ∣ i then gCoeff i * Ring.choose B ((p * A - i) / p) else 0) =
        ∑ j ∈ Finset.range (A + 1), gCoeff (p * j) * Ring.choose B (A - j) := by
    rw [← Finset.sum_filter, himg, Finset.sum_image]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      have hsub : p * A - p * j = p * (A - j) := (Nat.mul_sub_left_distrib p A j).symm
      rw [hsub, Nat.mul_div_right _ hp0]
    · intro x _ y _ hxy
      exact Nat.mul_left_cancel hp0 hxy
  rw [hre1, hre2]
  unfold U
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gCoeff_pow_mul hp hp5]

lemma coeff_one_add_X_add_X_sq (k : ℕ) :
    (PowerSeries.coeff k) ((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2) =
      (if k = 0 then (1 : ℤ) else 0) + (if k = 1 then 1 else 0) +
        (if k = 2 then 1 else 0) := by
  rw [map_add, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

lemma gSeries_mul_cyclotomic :
    gSeries * ((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2) =
      (1 : PowerSeries ℤ) - PowerSeries.X ^ 2 := by
  ext n
  have hlhs : (PowerSeries.coeff n)
      (gSeries * ((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2)) =
      gCoeff n
        + (if n = 0 then 0 else gCoeff (n - 1))
        + (if n ≤ 1 then 0 else gCoeff (n - 2)) := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (PowerSeries.coeff i) gSeries *
          (PowerSeries.coeff j)
            ((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2)) n]
    match n with
    | 0 =>
      simp [coeff_gSeries, coeff_one_add_X_add_X_sq, gCoeff]
    | 1 =>
      simp [Finset.sum_range_succ, coeff_gSeries, coeff_one_add_X_add_X_sq, gCoeff]
    | k + 2 =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have hz : ∀ i ∈ Finset.range k,
          (PowerSeries.coeff i) gSeries *
            (PowerSeries.coeff (k + 2 - i))
              ((1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2) = 0 := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [coeff_gSeries, coeff_one_add_X_add_X_sq]
        have hne0 : k + 2 - i ≠ 0 := by omega
        have hne1 : k + 2 - i ≠ 1 := by omega
        have hne2 : k + 2 - i ≠ 2 := by omega
        simp [hne0, hne1, hne2]
      rw [Finset.sum_eq_zero hz, zero_add]
      rw [coeff_gSeries, coeff_gSeries, coeff_gSeries, coeff_one_add_X_add_X_sq,
        coeff_one_add_X_add_X_sq, coeff_one_add_X_add_X_sq]
      simp [Nat.sub_self, show k + 2 - (k + 1) = 1 by omega,
        show k + 2 - k = 2 by omega]
      ring
  have hrhs : (PowerSeries.coeff n) ((1 : PowerSeries ℤ) - PowerSeries.X ^ 2) =
      if n = 0 then (1 : ℤ) else if n = 2 then (-1 : ℤ) else 0 := by
    rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    by_cases h0 : n = 0
    · simp [h0]
    · by_cases h2 : n = 2
      · simp [h0, h2]
      · simp [h0, h2]
  rw [hlhs, hrhs]
  exact g_window n

-- ═══════════════════════════════════════════════════════════════════════
-- Section 3: Polynomial structure of Φ and the k = 1 congruence
-- ═══════════════════════════════════════════════════════════════════════

/-- `φ_p` as a polynomial (degree at most `p-1`). -/
noncomputable def phiPoly (p : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range p, Polynomial.C (phiCoeff p k) * Polynomial.X ^ k

lemma coeff_phiPoly (p k : ℕ) : (phiPoly p).coeff k = phiCoeff p k := by
  unfold phiPoly
  rw [Polynomial.finset_sum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k ∈ Finset.range p
  · rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [hik.symm]
    · exact fun h => (h hk).elim
  · have hge : p ≤ k := by
      simp only [Finset.mem_range, not_lt] at hk; exact hk
    rw [Finset.sum_eq_zero, phiCoeff_eq_zero_of_ge hge]
    intro i hi
    have hne : i ≠ k := by
      simp only [Finset.mem_range] at hi; omega
    simp [hne.symm]

lemma phiPoly_natDegree_le (p : ℕ) (hp : 0 < p) : (phiPoly p).natDegree ≤ p - 1 := by
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le ?_
  intro k hk
  simp only [Finset.mem_range] at hk
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_pred_of_lt hk)

lemma phiSeries_eq_coe (p : ℕ) : (phiPoly p : PowerSeries ℤ) = phiSeries p := by
  ext n
  rw [Polynomial.coeff_coe, coeff_phiPoly, coeff_phiSeries]

/-- Residue sum of a coefficient function. -/
def coeffResidue (c : ℕ → ℤ) (bound r : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (bound + 1), if k % 3 = r % 3 then c k else 0

def polyResidue (f : Polynomial ℤ) (bound r : ℕ) : ℤ :=
  coeffResidue (fun k => f.coeff k) bound r

lemma p_mul_phiResidue {p : ℕ} (hp : p.Prime) (r : ℕ) :
    (p : ℤ) * coeffResidue (phiCoeff p) (p - 1) r = chooseMod3Interior p r := by
  have hp0 : 0 < p := hp.pos
  have hppred : p - 1 + 1 = p := Nat.sub_add_cancel hp0
  unfold coeffResidue
  rw [hppred, Finset.mul_sum]
  have hrange : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 (p - 1) := by simp
  rw [hrange, Finset.sum_insert h0]
  simp only [phiCoeff_zero, mul_zero, ite_self, zero_add]
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (p : ℤ) * (if k % 3 = r % 3 then phiCoeff p k else 0) =
        if k % 3 = r % 3 then (p.choose k : ℤ) else 0 := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk0 : 0 < k := by omega
    have hkp : k < p := by omega
    rw [phiCoeff_eq_choose_div p k hk0 hkp]
    split_ifs with h
    · exact Int.mul_ediv_cancel' (p_dvd_choose hp hk0 hkp)
    · simp
  rw [Finset.sum_congr rfl hterm, ← chooseMod3_interior_eq p r hp0]

lemma phiCoeff_residue_independent {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (r₁ r₂ : ℕ) :
    coeffResidue (phiCoeff p) (p - 1) r₁ = coeffResidue (phiCoeff p) (p - 1) r₂ := by
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_left_cancel₀ hpne
  rw [p_mul_phiResidue hp r₁, p_mul_phiResidue hp r₂,
    chooseMod3_interior_prime hp hp5 r₁, chooseMod3_interior_prime hp hp5 r₂]

lemma polyResidue_phiPoly (p r : ℕ) :
    polyResidue (phiPoly p) (p - 1) r = coeffResidue (phiCoeff p) (p - 1) r := by
  unfold polyResidue coeffResidue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [coeff_phiPoly]

lemma polyResidue_independent_phiPoly {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (r₁ r₂ : ℕ) :
    polyResidue (phiPoly p) (p - 1) r₁ = polyResidue (phiPoly p) (p - 1) r₂ := by
  rw [polyResidue_phiPoly, polyResidue_phiPoly, phiCoeff_residue_independent hp hp5]

/-- `1 + X + X^2`. -/
noncomputable def cyclo3 : Polynomial ℤ :=
  1 + Polynomial.X + Polynomial.X ^ 2

lemma coeff_cyclo3 (n : ℕ) :
    cyclo3.coeff n = if n ≤ 2 then (1 : ℤ) else 0 := by
  unfold cyclo3
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n = 1
    · simp [h0, h1]
    · by_cases h2 : n = 2
      · simp [h0, h1, h2]
      · simp [h0, h1, h2]; omega

lemma cyclo3_natDegree : cyclo3.natDegree = 2 := by
  apply le_antisymm
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
      simp [coeff_cyclo3]; omega
  · apply Polynomial.le_natDegree_of_ne_zero
    simp [coeff_cyclo3]

lemma cyclo3_monic : cyclo3.Monic := by
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff, cyclo3_natDegree]
  simp [coeff_cyclo3]

lemma cyclo3_coe :
    (cyclo3 : PowerSeries ℤ) = (1 : PowerSeries ℤ) + PowerSeries.X + PowerSeries.X ^ 2 := by
  ext n
  rw [Polynomial.coeff_coe, coeff_cyclo3, coeff_one_add_X_add_X_sq]
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n = 1
    · simp [h0, h1]
    · by_cases h2 : n = 2
      · simp [h0, h1, h2]
      · simp [h0, h1, h2]; omega

lemma coeff_linPoly (a b : ℤ) (k : ℕ) :
    (Polynomial.C a + Polynomial.C b * Polynomial.X).coeff k =
      if k = 0 then a else if k = 1 then b else 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X]
  by_cases h0 : k = 0
  · simp [h0]
  · by_cases h1 : k = 1
    · simp [h0, h1]
    · simp [h0, h1]; omega

lemma polyResidue_linPoly (a b : ℤ) (bound r : ℕ) (hb : 1 ≤ bound) :
    polyResidue (Polynomial.C a + Polynomial.C b * Polynomial.X) bound r =
      (if r % 3 = 0 then a else 0) + (if r % 3 = 1 then b else 0) := by
  unfold polyResidue coeffResidue
  let s := Finset.range (bound + 1)
  have hs01 : ({0, 1} : Finset ℕ) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [s]
    · simp [s]; omega
  have hrest : ∀ k ∈ s, k ∉ ({0, 1} : Finset ℕ) →
      (if k % 3 = r % 3 then
        (Polynomial.C a + Polynomial.C b * Polynomial.X).coeff k else 0) = 0 := by
    intro k _ hk
    have hk01 : k ≠ 0 ∧ k ≠ 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      exact hk
    rw [coeff_linPoly]; simp [hk01.1, hk01.2]
  rw [← Finset.sum_subset hs01 hrest]
  have hdisj : (0 : ℕ) ∉ ({1} : Finset ℕ) := by simp
  rw [Finset.sum_insert hdisj, Finset.sum_singleton, coeff_linPoly, coeff_linPoly]
  have hr : r % 3 < 3 := Nat.mod_lt r (by norm_num)
  interval_cases h : r % 3 <;> simp [h]

lemma coeff_cyclo3_mul (f : Polynomial ℤ) (n : ℕ) :
    (cyclo3 * f).coeff n =
      f.coeff n + (if n = 0 then 0 else f.coeff (n - 1)) +
        (if n ≤ 1 then 0 else f.coeff (n - 2)) := by
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => cyclo3.coeff i * f.coeff j) n]
  simp_rw [coeff_cyclo3]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (if i ≤ 2 then (1 : ℤ) else 0) * f.coeff (n - i) =
        if i ≤ 2 then f.coeff (n - i) else 0 := by
    intro i _; split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  match n with
  | 0 => simp
  | 1 => simp [Finset.sum_range_succ]
  | n + 2 =>
    have hsub : ({0, 1, 2} : Finset ℕ) ⊆ Finset.range (n + 3) := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_range]
      omega
    have heq :
        ∑ i ∈ Finset.range (n + 3), (if i ≤ 2 then f.coeff (n + 2 - i) else 0) =
          f.coeff (n + 2) + f.coeff (n + 1) + f.coeff n := by
      have hzero : ∀ i ∈ Finset.range (n + 3) \ {0, 1, 2},
          (if i ≤ 2 then f.coeff (n + 2 - i) else 0) = 0 := by
        intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hi
        have : ¬ i ≤ 2 := by omega
        simp [this]
      rw [← Finset.sum_sdiff hsub, Finset.sum_eq_zero hzero, zero_add]
      simp [Finset.mem_insert, Finset.mem_singleton]
      ring
    rw [heq]
    simp

lemma polyResidue_sum_all (f : Polynomial ℤ) (N : ℕ) :
    polyResidue f N 0 + polyResidue f N 1 + polyResidue f N 2 =
      ∑ k ∈ Finset.range (N + 1), f.coeff k := by
  unfold polyResidue coeffResidue
  simp only [Nat.zero_mod, Nat.reduceMod]
  have hpart : ∀ k, (if k % 3 = 0 then f.coeff k else 0) +
      (if k % 3 = 1 then f.coeff k else 0) +
      (if k % 3 = 2 then f.coeff k else 0) = f.coeff k := by
    intro k
    have hk : k % 3 < 3 := Nat.mod_lt k (by norm_num)
    interval_cases h : k % 3 <;> simp [h]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => hpart k

/-- Shifted residue sum, used to expand `polyResidue (cyclo3 * f)`. -/
lemma residue_shift (f : Polynomial ℤ) (N s r : ℕ)
    (hf : ∀ k, N < k → f.coeff k = 0) (hs : s ≤ 2) :
    ∑ n ∈ Finset.range (N + 3),
        (if n % 3 = r % 3 then (if s ≤ n then f.coeff (n - s) else 0) else 0) =
      ∑ k ∈ Finset.range (N + 1),
        if (k + s) % 3 = r % 3 then f.coeff k else 0 := by
  have hsub : Finset.Icc s (s + N) ⊆ Finset.range (N + 3) := by
    intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  rw [← Finset.sum_sdiff hsub]
  have hz : ∀ n ∈ Finset.range (N + 3) \ Finset.Icc s (s + N),
      (if n % 3 = r % 3 then (if s ≤ n then f.coeff (n - s) else 0) else 0) = 0 := by
    intro n hn
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with ⟨hnN, hfail⟩
    rcases hfail with hlt | hgt
    · simp [show ¬ s ≤ n by omega]
    · have : s ≤ n := by omega
      have : N < n - s := by omega
      simp [this, hf _ this]
  rw [Finset.sum_eq_zero hz, zero_add]
  refine Finset.sum_bij (fun n _ => n - s) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb heq
    simp only [Finset.mem_Icc] at ha hb
    have := congrArg (fun x => x + s) heq
    simpa [Nat.sub_add_cancel ha.1, Nat.sub_add_cancel hb.1] using this
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨k + s, ?_, Nat.add_sub_cancel _ _⟩
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have hns : s ≤ n := hn.1
    have hmod : n % 3 = (n - s + s) % 3 := by rw [Nat.sub_add_cancel hns]
    simp [hns, hmod]

noncomputable def phiQuot (p : ℕ) : Polynomial ℤ :=
  phiPoly p /ₘ cyclo3

lemma polyResidue_add (f g : Polynomial ℤ) (N r : ℕ) :
    polyResidue (f + g) N r = polyResidue f N r + polyResidue g N r := by
  unfold polyResidue coeffResidue
  simp only [Polynomial.coeff_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma polyResidue_bound_eq (f : Polynomial ℤ) (N M r : ℕ) (hNM : N ≤ M)
    (hf : ∀ k, N < k → f.coeff k = 0) :
    polyResidue f M r = polyResidue f N r := by
  unfold polyResidue coeffResidue
  have hsub : Finset.range (N + 1) ⊆ Finset.range (M + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.add_le_add_right hNM 1)
  rw [← Finset.sum_sdiff hsub]
  have hz : ∀ k ∈ Finset.range (M + 1) \ Finset.range (N + 1),
      (if k % 3 = r % 3 then f.coeff k else 0) = 0 := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hk
    have : N < k := Nat.succ_le_iff.mp hk.2
    simp [hf k this]
  rw [Finset.sum_eq_zero hz, zero_add]

lemma polyResidue_mul_cyclo3 (f : Polynomial ℤ) (N r : ℕ)
    (hf : ∀ k, N < k → f.coeff k = 0) :
    polyResidue (cyclo3 * f) (N + 2) r =
      ∑ k ∈ Finset.range (N + 1), f.coeff k := by
  unfold polyResidue coeffResidue
  have hN : N + 2 + 1 = N + 3 := by omega
  rw [hN]
  simp_rw [coeff_cyclo3_mul]
  have hsplit :
      ∑ n ∈ Finset.range (N + 3),
          (if n % 3 = r % 3 then
            f.coeff n + (if n = 0 then (0 : ℤ) else f.coeff (n - 1)) +
              (if n ≤ 1 then 0 else f.coeff (n - 2)) else 0) =
        ∑ n ∈ Finset.range (N + 3),
            (if n % 3 = r % 3 then (if 0 ≤ n then f.coeff (n - 0) else 0) else 0) +
          ∑ n ∈ Finset.range (N + 3),
            (if n % 3 = r % 3 then (if 1 ≤ n then f.coeff (n - 1) else 0) else 0) +
          ∑ n ∈ Finset.range (N + 3),
            (if n % 3 = r % 3 then (if 2 ≤ n then f.coeff (n - 2) else 0) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hm : n % 3 = r % 3
    · simp only [hm, ↓reduceIte, Nat.sub_zero, zero_le]
      by_cases h0 : n = 0
      · simp [h0]
      · by_cases h1 : n ≤ 1
        · have hn1 : n = 1 := le_antisymm h1 (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0))
          simp [h0, hn1]
        · have : 2 ≤ n := by omega
          simp [h0, h1, this]
    · simp [hm]
  rw [hsplit, residue_shift f N 0 r hf (by decide),
    residue_shift f N 1 r hf (by decide),
    residue_shift f N 2 r hf (by decide)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : k % 3 < 3 := Nat.mod_lt k (by norm_num)
  have h1m : (k + 1) % 3 = (k % 3 + 1) % 3 := Nat.add_mod _ _ _
  have h2m : (k + 2) % 3 = (k % 3 + 2) % 3 := Nat.add_mod _ _ _
  have hr : r % 3 < 3 := Nat.mod_lt r (by norm_num)
  interval_cases h : k % 3 <;> simp [h, h1m, h2m] <;>
    (interval_cases hr' : r % 3 <;> simp [hr'])

lemma phiPoly_eq_cyclo_mul {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    phiPoly p = cyclo3 * phiQuot p := by
  have hmon := cyclo3_monic
  have hsplit := Polynomial.modByMonic_add_div (phiPoly p) hmon
  unfold phiQuot
  set R := phiPoly p %ₘ cyclo3 with hRdef
  set Q := phiPoly p /ₘ cyclo3 with hQdef
  have hRdeg : R.degree < ↑(2 : ℕ) := by
    have hlt := Polynomial.degree_modByMonic_lt (phiPoly p) hmon
    have hdeg : cyclo3.degree = ↑(2 : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hmon.ne_zero, cyclo3_natDegree]
    rwa [hdeg] at hlt
  have hRle : R.degree ≤ ↑(1 : ℕ) := by
    match hRd : R.degree with
    | ⊥ => simp
    | some d =>
      have : d < 2 := by
        rw [hRd] at hRdeg
        exact WithBot.coe_lt_coe.mp hRdeg
      exact WithBot.coe_le_coe.mpr (Nat.lt_succ_iff.mp this)
  have hRform : R = Polynomial.C (R.coeff 1) * Polynomial.X + Polynomial.C (R.coeff 0) :=
    Polynomial.eq_X_add_C_of_degree_le_one hRle
  set a := R.coeff 0
  set b := R.coeff 1
  have hR : R = Polynomial.C a + Polynomial.C b * Polynomial.X := by
    rw [hRform, add_comm, mul_comm]
  have hp0 : 0 < p := hp.pos
  have hQhigh : ∀ k, p - 1 < k → Q.coeff k = 0 := by
    intro k hk
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    by_cases hQ0 : Q = 0
    · rw [hQ0, Polynomial.natDegree_zero]
      omega
    · have hmul : (cyclo3 * Q).natDegree = cyclo3.natDegree + Q.natDegree :=
        Polynomial.natDegree_mul hmon.ne_zero hQ0
      have heq : cyclo3 * Q = phiPoly p - R := by
        rw [← hsplit]; abel
      have hndR : R.natDegree ≤ 1 :=
        (Polynomial.natDegree_le_iff_degree_le (n := 1)).mpr hRle
      have hndR' : R.natDegree ≤ p - 1 := hndR.trans (by omega)
      have hprod : (cyclo3 * Q).natDegree ≤ p - 1 := by
        rw [heq]
        exact (Polynomial.natDegree_sub_le _ _).trans
          (sup_le (phiPoly_natDegree_le p hp0) hndR')
      have hbound : 2 + Q.natDegree ≤ p - 1 := by
        rw [hmul, cyclo3_natDegree] at hprod
        exact hprod
      omega
  have hresR : ∀ r, polyResidue R (p + 1) r =
      (if r % 3 = 0 then a else 0) + (if r % 3 = 1 then b else 0) := by
    intro r
    rw [hR, polyResidue_linPoly a b (p + 1) r (by omega)]
  have hresQ : ∀ r, polyResidue (cyclo3 * Q) (p + 1) r =
      ∑ k ∈ Finset.range p, Q.coeff k := by
    intro r
    have : p + 1 = p - 1 + 2 := by omega
    rw [this, polyResidue_mul_cyclo3 Q (p - 1) r hQhigh]
    simp [Nat.sub_add_cancel hp0]
  have hresP : ∀ r, polyResidue (phiPoly p) (p + 1) r =
      polyResidue (phiPoly p) (p - 1) r := by
    intro r
    refine polyResidue_bound_eq _ (p - 1) (p + 1) r (by omega) ?_
    intro k hk
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (phiPoly_natDegree_le p hp0) hk)
  have hid : phiPoly p = R + cyclo3 * Q := hsplit.symm
  have hσ : ∀ r, polyResidue (cyclo3 * Q) (p + 1) r =
      polyResidue (cyclo3 * Q) (p + 1) 0 := by
    intro r; rw [hresQ, hresQ]
  have hadd : ∀ r, polyResidue (phiPoly p) (p + 1) r =
      polyResidue R (p + 1) r + polyResidue (cyclo3 * Q) (p + 1) r := by
    intro r; rw [hid, polyResidue_add]
  have hs : ∀ r₁ r₂, polyResidue (phiPoly p) (p - 1) r₁ =
      polyResidue (phiPoly p) (p - 1) r₂ :=
    fun r₁ r₂ => polyResidue_independent_phiPoly hp hp5 r₁ r₂
  have hmod0 : (0 : ℕ) % 3 = 0 := rfl
  have hmod1 : (1 : ℕ) % 3 = 1 := rfl
  have hmod2 : (2 : ℕ) % 3 = 2 := rfl
  have ha0 : a = 0 := by
    have e0 := hadd 0
    have e2 := hadd 2
    rw [hresP 0, hresR 0, hσ 0] at e0
    rw [hresP 2, hresR 2, hσ 2] at e2
    simp only [hmod0, hmod2, Nat.reduceEqDiff, ite_true, ite_false] at e0 e2
    have heq : polyResidue (phiPoly p) (p - 1) 0 = polyResidue (phiPoly p) (p - 1) 2 :=
      hs 0 2
    linarith
  have hb0 : b = 0 := by
    have e1 := hadd 1
    have e2 := hadd 2
    rw [hresP 1, hresR 1, hσ 1] at e1
    rw [hresP 2, hresR 2, hσ 2] at e2
    simp only [hmod1, hmod2, Nat.reduceEqDiff, ite_true, ite_false] at e1 e2
    have heq : polyResidue (phiPoly p) (p - 1) 1 = polyResidue (phiPoly p) (p - 1) 2 :=
      hs 1 2
    linarith
  rw [hid, hR, ha0, hb0]
  simp

lemma oneMinusXSq_coe :
    ((1 - Polynomial.X ^ 2 : Polynomial ℤ) : PowerSeries ℤ) =
      (1 : PowerSeries ℤ) - PowerSeries.X ^ 2 := by
  simp [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_one]

lemma gSeries_mul_cyclo3_coe :
    gSeries * (cyclo3 : PowerSeries ℤ) =
      ((1 - Polynomial.X ^ 2 : Polynomial ℤ) : PowerSeries ℤ) := by
  rw [cyclo3_coe, gSeries_mul_cyclotomic, oneMinusXSq_coe]

lemma phiPoly_coeff_pred {p : ℕ} (hp : 1 < p) : (phiPoly p).coeff (p - 1) = 1 := by
  have hp0 : 0 < p := by omega
  have h1 : 0 < p - 1 := by omega
  have h2 : p - 1 < p := Nat.sub_lt hp0 (by decide)
  rw [coeff_phiPoly, phiCoeff_eq_choose_div p (p - 1) h1 h2]
  have hch : p.choose (p - 1) = p := by
    rw [← Nat.choose_symm (Nat.sub_le p 1), Nat.sub_sub_self (Nat.one_le_of_lt hp),
      Nat.choose_one_right]
  rw [hch, ← Int.natCast_ediv, Nat.div_self hp0, Int.natCast_one]

lemma phiPoly_natDegree_eq {p : ℕ} (hp : 1 < p) : (phiPoly p).natDegree = p - 1 := by
  apply le_antisymm (phiPoly_natDegree_le p (by omega))
  apply Polynomial.le_natDegree_of_ne_zero
  rw [phiPoly_coeff_pred hp]
  norm_num

lemma phiQuot_mul {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    cyclo3 * phiQuot p = phiPoly p := (phiPoly_eq_cyclo_mul hp hp5).symm

lemma phiQuot_natDegree_le {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    (phiQuot p).natDegree ≤ p - 3 := by
  have hp3 : 3 ≤ p := by omega
  by_cases hQ : phiQuot p = 0
  · simp [hQ]
  · have hmul : (cyclo3 * phiQuot p).natDegree =
        cyclo3.natDegree + (phiQuot p).natDegree :=
      Polynomial.natDegree_mul cyclo3_monic.ne_zero hQ
    have : (phiPoly p).natDegree = p - 1 := phiPoly_natDegree_eq (by omega)
    rw [phiQuot_mul hp hp5, this, cyclo3_natDegree] at hmul
    omega

lemma phiQuot_coeff_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (phiQuot p).coeff 0 = 0 := by
  have h0 : cyclo3.coeff 0 * (phiQuot p).coeff 0 = (phiPoly p).coeff 0 := by
    rw [← Polynomial.mul_coeff_zero, phiQuot_mul hp hp5]
  rw [coeff_phiPoly, phiCoeff_zero, coeff_cyclo3] at h0
  simpa using h0

lemma phiSeries_eq_cyclo_mul_quot {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    phiSeries p = (cyclo3 : PowerSeries ℤ) * (phiQuot p : PowerSeries ℤ) := by
  rw [← phiSeries_eq_coe, ← Polynomial.coe_mul, phiQuot_mul hp hp5]

/-- Polynomial representative of `g Φ^t` for `t ≥ 1`. -/
noncomputable def gPhiPowPoly (p t : ℕ) : Polynomial ℤ :=
  (1 - Polynomial.X ^ 2) * cyclo3 ^ (t - 1) * (phiQuot p) ^ t

lemma coeff_zero_pow_poly (f : Polynomial ℤ) (n : ℕ) :
    (f ^ n).coeff 0 = f.coeff 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Polynomial.mul_coeff_zero, ih, pow_succ]

lemma gPhiPowPoly_series {p t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (ht : 1 ≤ t) :
    (gPhiPowPoly p t : PowerSeries ℤ) = gSeries * phiSeries p ^ t := by
  unfold gPhiPowPoly
  rw [Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_pow]
  rw [phiSeries_eq_cyclo_mul_quot hp hp5, mul_pow]
  have hcy : (cyclo3 : PowerSeries ℤ) ^ t =
      (cyclo3 : PowerSeries ℤ) ^ (t - 1) * (cyclo3 : PowerSeries ℤ) := by
    rw [← pow_succ, Nat.sub_add_cancel ht]
  rw [hcy]
  have hre : gSeries * ((cyclo3 : PowerSeries ℤ) ^ (t - 1) * cyclo3 *
      (phiQuot p : PowerSeries ℤ) ^ t) =
      (gSeries * (cyclo3 : PowerSeries ℤ)) *
        (cyclo3 : PowerSeries ℤ) ^ (t - 1) * (phiQuot p : PowerSeries ℤ) ^ t := by
    ring
  rw [hre, gSeries_mul_cyclo3_coe]
  try ring

lemma gPhiPowPoly_natDegree_le {p t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (ht : 1 ≤ t) :
    (gPhiPowPoly p t).natDegree ≤ t * (p - 1) := by
  unfold gPhiPowPoly
  have h1 : (1 - Polynomial.X ^ 2 : Polynomial ℤ).natDegree ≤ 2 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp [Polynomial.natDegree_one]
  have h2 : (cyclo3 ^ (t - 1)).natDegree ≤ 2 * (t - 1) := by
    refine Polynomial.natDegree_pow_le.trans ?_
    rw [cyclo3_natDegree, mul_comm]
  have h3 : ((phiQuot p) ^ t).natDegree ≤ t * (p - 3) := by
    refine Polynomial.natDegree_pow_le.trans ?_
    exact Nat.mul_le_mul_left t (phiQuot_natDegree_le hp hp5)
  have h12 : ((1 - Polynomial.X ^ 2) * cyclo3 ^ (t - 1)).natDegree ≤
      2 + 2 * (t - 1) :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add h1 h2)
  refine Polynomial.natDegree_mul_le.trans ?_
  have hsum : 2 + 2 * (t - 1) + t * (p - 3) = t * (p - 1) := by
    have hp3 : 3 ≤ p := by omega
    have h2t : 2 + 2 * (t - 1) = 2 * t := by
      have := Nat.sub_add_cancel ht
      omega
    have h23 : 2 + (p - 3) = p - 1 := by omega
    rw [h2t, Nat.mul_comm 2 t, ← Nat.mul_add, h23]
  exact (Nat.add_le_add h12 h3).trans hsum.le

/-- `[X^{p M}] g Φ^t`. For `t = 0` this is `g_M`. -/
noncomputable def gPhiPowCoeff (p t M : ℕ) : ℤ :=
  if t = 0 then gCoeff M else (gPhiPowPoly p t).coeff (p * M)

lemma gPhiPowCoeff_eq_series {p t M : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    gPhiPowCoeff p t M =
      (PowerSeries.coeff (p * M)) (gSeries * phiSeries p ^ t) := by
  unfold gPhiPowCoeff
  split_ifs with ht
  · subst ht
    simp [coeff_gSeries, gCoeff_pow_mul hp hp5]
  · have ht1 : 1 ≤ t := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ht)
    rw [← Polynomial.coeff_coe, gPhiPowPoly_series hp hp5 ht1]

lemma gPhiPowCoeff_zero_left (p M : ℕ) : gPhiPowCoeff p 0 M = gCoeff M := by
  simp [gPhiPowCoeff]

lemma gPhiPowCoeff_zero_of_M_zero {p t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5)
    (ht : 1 ≤ t) : gPhiPowCoeff p t 0 = 0 := by
  have ht0 : t ≠ 0 := Nat.pos_iff_ne_zero.mp ht
  unfold gPhiPowCoeff
  simp only [ht0, ↓reduceIte, mul_zero]
  have hQ0 : (phiQuot p).coeff 0 = 0 := phiQuot_coeff_zero p hp hp5
  have hpow : ((phiQuot p) ^ t).coeff 0 = 0 := by
    rw [coeff_zero_pow_poly, hQ0, zero_pow ht0]
  unfold gPhiPowPoly
  rw [Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero, hpow]
  simp

lemma gPhiPowCoeff_eq_zero_of_ge {p t M : ℕ} (hp : p.Prime) (hp5 : p ≥ 5)
    (ht : 1 ≤ t) (hM : t ≤ M) : gPhiPowCoeff p t M = 0 := by
  have ht0 : t ≠ 0 := Nat.pos_iff_ne_zero.mp ht
  unfold gPhiPowCoeff
  simp only [ht0, ↓reduceIte]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt (gPhiPowPoly_natDegree_le hp hp5 ht) ?_
  have : t * (p - 1) < p * M := by
    have h1 : t * (p - 1) < t * p := by
      have : p - 1 < p := Nat.sub_lt hp.pos (by decide)
      exact Nat.mul_lt_mul_of_pos_left this ht
    have h2 : t * p ≤ M * p := Nat.mul_le_mul_right p hM
    have h3 : t * p = p * t := Nat.mul_comm _ _
    have h4 : M * p = p * M := Nat.mul_comm _ _
    omega
  exact this

lemma expand_one_add_X_pow (p n : ℕ) (hp0 : p ≠ 0) :
    PowerSeries.expand p hp0 ((1 + PowerSeries.X : PowerSeries ℤ) ^ n) =
      (1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ n := by
  rw [map_pow, map_add, map_one, PowerSeries.expand_X]

lemma expand_binomialSeries_nat (p n : ℕ) (hp0 : p ≠ 0) :
    PowerSeries.expand p hp0 (PowerSeries.binomialSeries ℤ (n : ℤ)) =
      (1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ n := by
  have h := PowerSeries.binomialSeries_nat (R := ℤ) (A := ℤ) n
  rw [h, expand_one_add_X_pow]

lemma one_add_Yp_eq (p : ℕ) :
    (1 + Yp p) =
      (1 + (PowerSeries.X : PowerSeries ℤ) ^ p) +
        PowerSeries.C (p : ℤ) * phiSeries p := by
  simp [Yp]
  abel

lemma C_pow_int (a : ℤ) (n : ℕ) :
    (PowerSeries.C a : PowerSeries ℤ) ^ n = PowerSeries.C (a ^ n) :=
  (map_pow (PowerSeries.C : ℤ →+* PowerSeries ℤ) a n).symm

lemma intCast_powerSeries (a : ℤ) : (a : PowerSeries ℤ) = PowerSeries.C a := by
  simp [← PowerSeries.algebraMap_eq]

lemma natCast_powerSeries (n : ℕ) :
    (n : PowerSeries ℤ) = PowerSeries.C (n : ℤ) := by
  simp [intCast_powerSeries]

lemma coeff_mul_C (f : PowerSeries ℤ) (n : ℕ) (a : ℤ) :
    (PowerSeries.coeff n) (f * PowerSeries.C a) =
      a * (PowerSeries.coeff n) f := by
  rw [mul_comm, PowerSeries.coeff_C_mul]

lemma one_add_Yp_pow (p B : ℕ) :
    (1 + Yp p) ^ B =
      ∑ t ∈ Finset.range (B + 1),
        (1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ (B - t) *
          (PowerSeries.C (p : ℤ) * phiSeries p) ^ t *
            (B.choose t : PowerSeries ℤ) := by
  rw [one_add_Yp_eq, add_pow]
  refine (Finset.sum_bij (fun m _ => B - m) ?_ ?_ ?_ ?_).symm
  · intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  · intro a ha b hb heq
    simp only [Finset.mem_range] at ha hb
    have := congrArg (fun x => B - x) heq
    simpa [Nat.sub_sub_self (Nat.lt_succ_iff.mp ha),
      Nat.sub_sub_self (Nat.lt_succ_iff.mp hb)] using this
  · intro t ht
    simp only [Finset.mem_range] at ht
    refine ⟨B - t, ?_, Nat.sub_sub_self (Nat.lt_succ_iff.mp ht)⟩
    simp only [Finset.mem_range]
    omega
  · intro m hm
    simp only [Finset.mem_range] at hm
    have hch : (B.choose (B - m) : PowerSeries ℤ) = (B.choose m : PowerSeries ℤ) := by
      rw [Nat.choose_symm (Nat.lt_succ_iff.mp hm)]
    simp [hch, Nat.sub_sub_self (Nat.lt_succ_iff.mp hm)]

lemma coeff_g_phi_expand (p A t Bt : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (PowerSeries.coeff (p * A))
        ((gSeries * phiSeries p ^ t) *
          (1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ Bt) =
      ∑ M ∈ Finset.range (A + 1),
        gPhiPowCoeff p t M * Ring.choose (Bt : ℤ) (A - M) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hexpand :
      (1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ Bt =
        PowerSeries.expand p hp0 (PowerSeries.binomialSeries ℤ (Bt : ℤ)) :=
    (expand_binomialSeries_nat p Bt hp0).symm
  rw [hexpand, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (PowerSeries.coeff i) (gSeries * phiSeries p ^ t) *
        (PowerSeries.coeff j)
          (PowerSeries.expand p hp0 (PowerSeries.binomialSeries ℤ (Bt : ℤ))))
      (p * A)]
  have hterm : ∀ i ∈ Finset.range (p * A + 1),
      (PowerSeries.coeff i) (gSeries * phiSeries p ^ t) *
        (PowerSeries.coeff (p * A - i))
          (PowerSeries.expand p hp0 (PowerSeries.binomialSeries ℤ (Bt : ℤ))) =
        if p ∣ i then
          gPhiPowCoeff p t (i / p) * Ring.choose (Bt : ℤ) ((p * A - i) / p)
        else 0 := by
    intro i hi
    by_cases hdiv : p ∣ i
    · obtain ⟨M, hM⟩ := hdiv
      have hdiv2 : p ∣ p * A - i := by
        refine Nat.dvd_sub (dvd_mul_right p A) ?_
        exact ⟨M, hM⟩
      obtain ⟨m, hm⟩ := hdiv2
      have hexp :
          (PowerSeries.coeff (p * A - i))
              (PowerSeries.expand p hp0 (PowerSeries.binomialSeries ℤ (Bt : ℤ))) =
            Ring.choose (Bt : ℤ) m := by
        rw [hm]
        have h1 := PowerSeries.coeff_expand_mul (R := ℤ) p hp0
            (PowerSeries.binomialSeries ℤ (Bt : ℤ)) m
        simpa using h1.trans (PowerSeries.binomialSeries_coeff (Bt : ℤ) m)
      have hiM : i / p = M := by rw [hM, Nat.mul_div_right _ hp.pos]
      have hmdiv : (p * A - i) / p = m := by rw [hm, Nat.mul_div_right _ hp.pos]
      have hser : (PowerSeries.coeff i) (gSeries * phiSeries p ^ t) =
          gPhiPowCoeff p t M := by
        rw [hM, gPhiPowCoeff_eq_series hp hp5]
      have hpos : p ∣ i := ⟨M, hM⟩
      rw [if_pos hpos, hser, hiM, hexp, hmdiv]
    · have hi' : i ≤ p * A := by
        simp only [Finset.mem_range] at hi; exact Nat.lt_succ_iff.mp hi
      have hnd : ¬ p ∣ (p * A - i) := by
        intro h
        have h' := Nat.dvd_sub (dvd_mul_right p A) h
        rw [Nat.sub_sub_self hi'] at h'
        exact hdiv h'
      have hexp :
          (PowerSeries.coeff (p * A - i))
              (PowerSeries.expand p hp0 (PowerSeries.binomialSeries ℤ (Bt : ℤ))) =
            0 := by
        simpa using
          (PowerSeries.coeff_expand_of_not_dvd (R := ℤ) p hp0
            (PowerSeries.binomialSeries ℤ (Bt : ℤ)) hnd)
      rw [if_neg hdiv, hexp, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have himg : ((Finset.range (p * A + 1)).filter (p ∣ ·)) =
      (Finset.range (A + 1)).image (fun M => p * M) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨hi, hdiv⟩
      obtain ⟨M, rfl⟩ := hdiv
      refine ⟨M, ?_, rfl⟩
      have : p * M ≤ p * A := Nat.le_of_lt_succ hi
      exact Nat.lt_succ_iff.mpr (Nat.le_of_mul_le_mul_left this hp.pos)
    · intro ⟨M, hM, hi⟩
      subst hi
      constructor
      · have : M ≤ A := Nat.lt_succ_iff.mp hM
        have : p * M ≤ p * A := Nat.mul_le_mul_left p this
        omega
      · exact dvd_mul_right _ _
  rw [← Finset.sum_filter, himg, Finset.sum_image]
  · refine Finset.sum_congr rfl fun M hM => ?_
    simp only [Finset.mem_range] at hM
    have hsub : p * A - p * M = p * (A - M) :=
      (Nat.mul_sub_left_distrib p A M).symm
    rw [Nat.mul_div_right _ hp.pos, hsub, Nat.mul_div_right _ hp.pos]
  · intro x _ y _ hxy
    exact Nat.mul_left_cancel hp.pos hxy

/-- Binomial expansion of `U(pA, pB)` for nonnegative `B`. -/
lemma U_mul_p_expand (p A B : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    U (p * A) ((p * B : ℕ) : ℤ) =
      ∑ t ∈ Finset.range (B + 1),
        (p : ℤ) ^ t * (B.choose t : ℤ) *
          ∑ M ∈ Finset.range (A + 1),
            gPhiPowCoeff p t M * Ring.choose ((B : ℤ) - t) (A - M) := by
  have hU := U_eq_coeff (p * A) ((p * B : ℕ) : ℤ)
  have hcast : ((p * B : ℕ) : ℤ) = (p : ℤ) * (B : ℤ) := by simp
  rw [hU, hcast, binomialSeries_nat_mul_p p B hp, one_add_Yp_pow]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at ht
  have htle : t ≤ B := Nat.lt_succ_iff.mp ht
  have hCp : (PowerSeries.C (p : ℤ) * phiSeries p) ^ t =
      PowerSeries.C ((p : ℤ) ^ t) * phiSeries p ^ t := by
    rw [mul_pow, C_pow_int]
  have hscale :
      (PowerSeries.coeff (p * A))
          (gSeries *
            ((1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ (B - t) *
              (PowerSeries.C (p : ℤ) * phiSeries p) ^ t *
                (B.choose t : PowerSeries ℤ))) =
        (p : ℤ) ^ t * (B.choose t : ℤ) *
          (PowerSeries.coeff (p * A))
            ((gSeries * phiSeries p ^ t) *
              (1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ (B - t)) := by
    rw [hCp, natCast_powerSeries]
    have hCmul : PowerSeries.C ((p : ℤ) ^ t) * PowerSeries.C (B.choose t : ℤ) =
        PowerSeries.C ((p : ℤ) ^ t * (B.choose t : ℤ)) :=
      (map_mul (PowerSeries.C : ℤ →+* PowerSeries ℤ) _ _).symm
    have hz :
        gSeries *
            ((1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ (B - t) *
              (PowerSeries.C ((p : ℤ) ^ t) * phiSeries p ^ t) *
                PowerSeries.C (B.choose t : ℤ)) =
          ((gSeries * phiSeries p ^ t) *
              (1 + (PowerSeries.X : PowerSeries ℤ) ^ p) ^ (B - t)) *
            PowerSeries.C ((p : ℤ) ^ t * (B.choose t : ℤ)) := by
      rw [← hCmul]
      ring
    rw [hz, PowerSeries.coeff_mul_C]
    ring
  rw [hscale, coeff_g_phi_expand p A t (B - t) hp hp5]
  refine congrArg (fun s => (p : ℤ) ^ t * (B.choose t : ℤ) * s)
    (Finset.sum_congr rfl fun M _ => ?_)
  rw [Nat.cast_sub htle]

lemma gPhiPowCoeff_one {p M : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    gPhiPowCoeff p 1 M = 0 := by
  by_cases hM : M = 0
  · subst hM
    exact gPhiPowCoeff_zero_of_M_zero hp hp5 (by decide)
  · exact gPhiPowCoeff_eq_zero_of_ge hp hp5 (by decide) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hM))

lemma gPhiPowCoeff_two {p M : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    gPhiPowCoeff p 2 M = 0 := by
  by_cases hM0 : M = 0
  · subst hM0
    exact gPhiPowCoeff_zero_of_M_zero hp hp5 (by decide)
  by_cases hM2 : 2 ≤ M
  · exact gPhiPowCoeff_eq_zero_of_ge hp hp5 (by decide) hM2
  have hM1 : M = 1 := by omega
  subst hM1
  have hexp := U_mul_p_expand p 1 2 hp hp5
  have hU : U (p * 1) ((p * 2 : ℕ) : ℤ) = 1 := by
    have h := U_double p
    convert h using 2
    · ring
    · push_cast; ring
  rw [show Finset.range (2 + 1) = Finset.range 3 from rfl,
      show Finset.range (1 + 1) = Finset.range 2 from rfl] at hexp
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add] at hexp
  have ht0 :
      (p : ℤ) ^ 0 * (Nat.choose 2 0 : ℤ) *
        ∑ M ∈ Finset.range 2,
          gPhiPowCoeff p 0 M * Ring.choose (((2 : ℕ) : ℤ) - (0 : ℕ)) (1 - M) = 1 := by
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
      gPhiPowCoeff_zero_left, Nat.cast_zero, sub_zero]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [gCoeff, Ring.choose_zero_right, Ring.choose_one_right]
  have ht1 :
      (p : ℤ) ^ 1 * (Nat.choose 2 1 : ℤ) *
        ∑ M ∈ Finset.range 2,
          gPhiPowCoeff p 1 M * Ring.choose (((2 : ℕ) : ℤ) - (1 : ℕ)) (1 - M) = 0 := by
    simp [gPhiPowCoeff_one hp hp5]
  have ht2 :
      (p : ℤ) ^ 2 * (Nat.choose 2 2 : ℤ) *
        ∑ M ∈ Finset.range 2,
          gPhiPowCoeff p 2 M * Ring.choose (((2 : ℕ) : ℤ) - (2 : ℕ)) (1 - M) =
        (p : ℤ) ^ 2 * gPhiPowCoeff p 2 1 := by
    simp only [Nat.choose_self, Nat.cast_one, mul_one]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    have hc0 : gPhiPowCoeff p 2 0 = 0 :=
      gPhiPowCoeff_zero_of_M_zero hp hp5 (by decide)
    simp [hc0, Ring.choose_zero_right]
  rw [ht0, ht1, ht2] at hexp
  have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.ne_zero)
  have : (p : ℤ) ^ 2 * gPhiPowCoeff p 2 1 = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hp2

lemma inner_sum_t_le_two {p A B t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5)
    (ht : t = 1 ∨ t = 2) :
    ∑ M ∈ Finset.range (A + 1),
        gPhiPowCoeff p t M * Ring.choose ((B : ℤ) - t) (A - M) = 0 := by
  refine Finset.sum_eq_zero fun M _ => ?_
  have : gPhiPowCoeff p t M = 0 := by
    rcases ht with rfl | rfl
    · exact gPhiPowCoeff_one hp hp5
    · exact gPhiPowCoeff_two hp hp5
  simp [this]

lemma U_mul_p_mod_p3 (p A B : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ℤ) ^ 3 ∣ U (p * A) ((p * B : ℕ) : ℤ) - U A B := by
  rw [U_mul_p_expand p A B hp hp5]
  -- isolate the `t = 0` term, which is `U A B`
  have h0 :
      (p : ℤ) ^ 0 * (B.choose 0 : ℤ) *
        ∑ M ∈ Finset.range (A + 1),
          gPhiPowCoeff p 0 M * Ring.choose ((B : ℤ) - 0) (A - M) = U A B := by
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
      gPhiPowCoeff_zero_left, sub_zero]
    unfold U
    refine Finset.sum_congr rfl fun M hM => ?_
    simp only [Finset.mem_range] at hM
    rfl
  -- rewrite the big sum as t=0 plus the rest
  have hsplit :
      ∑ t ∈ Finset.range (B + 1),
          (p : ℤ) ^ t * (B.choose t : ℤ) *
            ∑ M ∈ Finset.range (A + 1),
              gPhiPowCoeff p t M * Ring.choose ((B : ℤ) - t) (A - M) =
        U A B +
          ∑ t ∈ Finset.Icc 1 B,
            (p : ℤ) ^ t * (B.choose t : ℤ) *
              ∑ M ∈ Finset.range (A + 1),
                gPhiPowCoeff p t M * Ring.choose ((B : ℤ) - t) (A - M) := by
    have hr : Finset.range (B + 1) = insert 0 (Finset.Icc 1 B) := by
      ext t
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have h0i : (0 : ℕ) ∉ Finset.Icc 1 B := by simp
    rw [hr, Finset.sum_insert h0i]
    simp only [Nat.cast_zero] at h0 ⊢
    rw [h0]
  rw [hsplit, add_sub_cancel_left]
  refine Finset.dvd_sum fun t ht => ?_
  simp only [Finset.mem_Icc] at ht
  by_cases ht12 : t = 1 ∨ t = 2
  · rw [inner_sum_t_le_two (B := B) hp hp5 ht12]
    simp
  · have ht3 : 3 ≤ t := by omega
    have hpow : (p : ℤ) ^ 3 ∣ (p : ℤ) ^ t :=
      pow_dvd_pow (p : ℤ) ht3
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpow _) _

lemma U_mul_p_modEq (p A B : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    U (p * A) ((p * B : ℕ) : ℤ) ≡ U A B [ZMOD (p : ℤ) ^ 3] := by
  rw [Int.modEq_iff_dvd, ← dvd_neg, neg_sub]
  exact U_mul_p_mod_p3 p A B hp hp5

/-- Binomial polynomial `X(X-1)...(X-k+1) / k!` over `ℚ`. -/
noncomputable def binomPoly (k : ℕ) : Polynomial ℚ :=
  Polynomial.C (k.factorial : ℚ)⁻¹ * descPochhammer ℚ k

lemma binomPoly_natDegree_le (k : ℕ) : (binomPoly k).natDegree ≤ k := by
  unfold binomPoly
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  exact (descPochhammer_natDegree (R := ℚ) k).le

lemma descPochhammer_eval_choose (x : ℤ) (k : ℕ) :
    (descPochhammer ℤ k).eval x = (k.factorial : ℤ) * Ring.choose x k := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (R := ℤ) x k
  rw [nsmul_eq_mul, ← Polynomial.eval_eq_smeval] at h
  exact h

lemma binomPoly_eval_int (x : ℤ) (k : ℕ) :
    (binomPoly k).eval (x : ℚ) = Int.cast (Ring.choose x k) := by
  have h := descPochhammer_eval_choose x k
  have hk : (k.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  unfold binomPoly
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  have hmap : (descPochhammer ℤ k).map (Int.castRingHom ℚ) = descPochhammer ℚ k :=
    descPochhammer_map (Int.castRingHom ℚ) k
  have heval : (descPochhammer ℚ k).eval (x : ℚ) =
      Int.cast ((descPochhammer ℤ k).eval x) := by
    rw [← hmap, Polynomial.eval_map, Polynomial.eval₂_at_intCast]
    rfl
  rw [heval, h, Int.cast_mul]
  field_simp [hk]
  rw [Int.cast_natCast]

lemma binomPoly_eval_nat (n k : ℕ) :
    (binomPoly k).eval (n : ℚ) = Int.cast (n.choose k : ℤ) := by
  have h := binomPoly_eval_int (n : ℤ) k
  rw [Int.cast_natCast] at h
  rw [h, ringChoose_nat]

lemma ringChoose_cast_rat (x : ℤ) (k : ℕ) :
    Ring.choose (x : ℚ) k = Int.cast (Ring.choose x k) :=
  (Ring.map_choose (Int.castRingHom ℚ) x k).symm

lemma Upoly_eval_aux (A : ℕ) (B : ℤ) :
    (∑ j ∈ Finset.range (A + 1),
        Polynomial.C (Int.cast (gCoeff j)) * binomPoly (A - j)).eval (B : ℚ) =
      Int.cast (U A B) := by
  unfold U
  rw [Polynomial.eval_finset_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, binomPoly_eval_int, Int.cast_mul]

noncomputable def Upoly (A : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (A + 1), Polynomial.C (Int.cast (gCoeff j)) * binomPoly (A - j)

lemma Upoly_eval (A : ℕ) (B : ℤ) : (Upoly A).eval (B : ℚ) = Int.cast (U A B) :=
  Upoly_eval_aux A B

lemma Upoly_natDegree_le (A : ℕ) : (Upoly A).natDegree ≤ A := by
  unfold Upoly
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  exact (binomPoly_natDegree_le (A - j)).trans (Nat.sub_le _ _)

noncomputable def Upoly_scale (p A : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (p * A + 1),
    Polynomial.C (Int.cast (gCoeff j)) *
      (binomPoly (p * A - j)).comp (Polynomial.C (p : ℚ) * Polynomial.X)

lemma Upoly_scale_eval (p A : ℕ) (B : ℤ) :
    (Upoly_scale p A).eval (B : ℚ) = Int.cast (U (p * A) ((p : ℤ) * B)) := by
  unfold Upoly_scale U
  rw [Polynomial.eval_finset_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  have hinner : (Polynomial.C (p : ℚ) * Polynomial.X).eval (B : ℚ) =
      (p : ℚ) * (B : ℚ) := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hinner]
  have harg : (p : ℚ) * (B : ℚ) = Int.cast ((p : ℤ) * B) := by
    rw [Int.cast_mul]; rfl
  rw [harg, binomPoly_eval_int, Int.cast_mul]

lemma Upoly_scale_natDegree_le (p A : ℕ) : (Upoly_scale p A).natDegree ≤ p * A := by
  unfold Upoly_scale
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_comp_le.trans ?_
  have h1 : (binomPoly (p * A - j)).natDegree ≤ p * A - j := binomPoly_natDegree_le _
  have h2 : (Polynomial.C (p : ℚ) * Polynomial.X).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    simp
  have : (p * A - j) * 1 ≤ p * A := by
    rw [mul_one]; exact Nat.sub_le _ _
  exact le_trans (Nat.mul_le_mul h1 h2) this

/-- `Δ^k f (0)` via Mathlib's forward difference. -/
def mahlerCoeff (f : ℕ → ℤ) (k : ℕ) : ℤ :=
  (fwdDiff (1 : ℕ))^[k] f 0

lemma mahlerCoeff_eq (f : ℕ → ℤ) (k : ℕ) :
    mahlerCoeff f k =
      ∑ i ∈ Finset.range (k + 1),
        ((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ)) * f i := by
  unfold mahlerCoeff
  have h := fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) f k 0
  simpa [nsmul_eq_mul, one_nsmul, zero_add] using h

lemma mahlerCoeff_dvd {f : ℕ → ℤ} {m : ℤ} (hf : ∀ n : ℕ, m ∣ f n) (k : ℕ) :
    m ∣ mahlerCoeff f k := by
  rw [mahlerCoeff_eq]
  refine Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hf i) _

lemma discrete_taylor_nat (f : ℕ → ℤ) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * mahlerCoeff f k := by
  have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) f n 0
  unfold mahlerCoeff
  simpa [nsmul_eq_mul, one_nsmul, zero_add, mul_comm] using h

lemma poly_eq_of_eval_le {P Q : Polynomial ℚ} {d : ℕ}
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (h : ∀ n : ℕ, n ≤ d → P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq' P Q
    ((Finset.range (d + 1)).image (fun n : ℕ => (n : ℚ))) ?_ ?_
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact h n (Nat.lt_succ_iff.mp hn)
  · have hcard : ((Finset.range (d + 1)).image (fun n : ℕ => (n : ℚ))).card = d + 1 := by
      rw [Finset.card_image_of_injective]
      · simp
      · exact Nat.cast_injective
    have hmax : max P.natDegree Q.natDegree ≤ d := sup_le hP hQ
    omega

/-- If `P` interpolates an `m`-divisible sequence on `ℕ` and has degree `≤ d`,
then `P(B)` is the image of an integer divisible by `m`. -/
lemma mahler_extension (f : ℕ → ℤ) (d : ℕ) (m : ℤ) (P : Polynomial ℚ)
    (hPdeg : P.natDegree ≤ d)
    (hPeval : ∀ n : ℕ, P.eval (n : ℚ) = Int.cast (f n))
    (hf : ∀ n : ℕ, m ∣ f n) (B : ℤ) :
    ∃ z : ℤ, P.eval (B : ℚ) = Int.cast z ∧ m ∣ z := by
  set Q : Polynomial ℚ :=
    ∑ k ∈ Finset.range (d + 1), Polynomial.C (Int.cast (mahlerCoeff f k)) * binomPoly k
    with hQdef
  have hQdeg : Q.natDegree ≤ d := by
    rw [hQdef]
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    refine Finset.sup_le ?_
    intro k hk
    simp only [Finset.mem_range] at hk
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((binomPoly_natDegree_le k).trans (Nat.lt_succ_iff.mp hk))
  have hQeval : ∀ n : ℕ, n ≤ d → Q.eval (n : ℚ) = Int.cast (f n) := by
    intro n hn
    rw [hQdef, Polynomial.eval_finset_sum]
    have hterm : ∀ k ∈ Finset.range (d + 1),
        (Polynomial.C (Int.cast (mahlerCoeff f k) : ℚ) * binomPoly k).eval (n : ℚ) =
          (mahlerCoeff f k : ℚ) * (n.choose k : ℚ) := by
      intro k _
      rw [Polynomial.eval_mul, Polynomial.eval_C, binomPoly_eval_nat]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hterm]
    have hsub : Finset.range (n + 1) ⊆ Finset.range (d + 1) := by
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    have hsum :
        ∑ k ∈ Finset.range (d + 1), (mahlerCoeff f k : ℚ) * (n.choose k : ℚ) =
          ∑ k ∈ Finset.range (n + 1), (mahlerCoeff f k : ℚ) * (n.choose k : ℚ) := by
      rw [← Finset.sum_sdiff hsub]
      have hz : ∀ k ∈ Finset.range (d + 1) \ Finset.range (n + 1),
          (mahlerCoeff f k : ℚ) * (n.choose k : ℚ) = 0 := by
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hk
        have : n.choose k = 0 := Nat.choose_eq_zero_of_lt hk.2
        simp [this]
      rw [Finset.sum_eq_zero hz, zero_add]
    rw [hsum]
    have hT := congrArg (fun z : ℤ => (z : ℚ)) (discrete_taylor_nat f n)
    simp only [Int.cast_sum, Int.cast_mul] at hT
    refine Eq.trans ?_ hT.symm
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    push_cast
    rfl
  have hPQ : P = Q :=
    poly_eq_of_eval_le hPdeg hQdeg fun n hn => (hPeval n).trans (hQeval n hn).symm
  refine ⟨∑ k ∈ Finset.range (d + 1), mahlerCoeff f k * Ring.choose B k, ?_, ?_⟩
  · rw [hPQ, hQdef, Polynomial.eval_finset_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, binomPoly_eval_int, Int.cast_mul]
  · refine Finset.dvd_sum fun k _ =>
      dvd_mul_of_dvd_left (mahlerCoeff_dvd hf k) _

/-- `k=1` congruence for an arbitrary integer upper index. -/
lemma U_mul_p_mod_p3_int (p A : ℕ) (B : ℤ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ℤ) ^ 3 ∣ U (p * A) ((p : ℤ) * B) - U A B := by
  set f : ℕ → ℤ := fun n => U (p * A) ((p : ℤ) * n) - U A n
  set P : Polynomial ℚ := Upoly_scale p A - Upoly A
  have hPdeg : P.natDegree ≤ p * A := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (sup_le (Upoly_scale_natDegree_le p A)
        ((Upoly_natDegree_le A).trans (Nat.le_mul_of_pos_left A hp.pos)))
  have hPeval : ∀ n : ℕ, P.eval (n : ℚ) = Int.cast (f n) := by
    intro n
    rw [Polynomial.eval_sub]
    have hs := Upoly_scale_eval p A (n : ℤ)
    have hu := Upoly_eval A (n : ℤ)
    rw [Int.cast_natCast] at hs hu
    rw [hs, hu, Int.cast_sub]
  have hf : ∀ n : ℕ, (p : ℤ) ^ 3 ∣ f n := by
    intro n
    simpa [f] using U_mul_p_mod_p3 p A n hp hp5
  obtain ⟨z, hz, hzdvd⟩ := mahler_extension f (p * A) ((p : ℤ) ^ 3) P hPdeg hPeval hf B
  have hPB : P.eval (B : ℚ) = Int.cast (U (p * A) ((p : ℤ) * B) - U A B) := by
    rw [Polynomial.eval_sub, Upoly_scale_eval, Upoly_eval, Int.cast_sub]
  have hzeq : U (p * A) ((p : ℤ) * B) - U A B = z := by
    apply Int.cast_injective (α := ℚ)
    rw [← hPB, hz]
  rwa [hzeq]

lemma U_mul_p_modEq_int (p A : ℕ) (B : ℤ) (hp : p.Prime) (hp5 : p ≥ 5) :
    U (p * A) ((p : ℤ) * B) ≡ U A B [ZMOD (p : ℤ) ^ 3] := by
  rw [Int.modEq_iff_dvd, ← dvd_neg, neg_sub]
  exact U_mul_p_mod_p3_int p A B hp hp5

lemma aTrue_mul_p (m : ℤ) (p n : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    aTrue m (n * p) ≡ aTrue m n [ZMOD (p : ℤ) ^ 3] := by
  rw [aTrue_eq_U, aTrue_eq_U]
  have h := U_mul_p_modEq_int p n (n * (m + 2)) hp hp5
  have hA : n * p = p * n := Nat.mul_comm _ _
  rw [hA]
  convert h using 2
  push_cast; ring

lemma a_gen_congr_of_aTrue {m : ℤ} {N₁ N₂ : ℕ} {mod : ℤ}
    (hN₁ : N₁ ≠ 0) (hN₂ : N₂ ≠ 0)
    (h : aTrue m N₁ ≡ aTrue m N₂ [ZMOD mod]) :
    a_gen m N₁ ≡ a_gen m N₂ [ZMOD mod] := by
  by_cases hm : m = -1
  · subst hm
    rw [a_gen_neg_one N₁ hN₁, a_gen_neg_one N₂ hN₂]
    exact h.add rfl
  · rw [a_gen_eq_aTrue_of_ne_neg_one _ _ hm, a_gen_eq_aTrue_of_ne_neg_one _ _ hm]
    exact h

/-- Scaling polynomial: `B ↦ U(cA, cB)`. -/
noncomputable def Upoly_scale_pow (c A : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (c * A + 1),
    Polynomial.C (Int.cast (gCoeff j)) *
      (binomPoly (c * A - j)).comp (Polynomial.C (c : ℚ) * Polynomial.X)

lemma Upoly_scale_pow_eval (c A : ℕ) (B : ℤ) :
    (Upoly_scale_pow c A).eval (B : ℚ) = Int.cast (U (c * A) ((c : ℤ) * B)) := by
  unfold Upoly_scale_pow U
  rw [Polynomial.eval_finset_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  have hinner : (Polynomial.C (c : ℚ) * Polynomial.X).eval (B : ℚ) =
      (c : ℚ) * (B : ℚ) := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [hinner]
  have harg : (c : ℚ) * (B : ℚ) = Int.cast ((c : ℤ) * B) := by
    rw [Int.cast_mul]; rfl
  rw [harg, binomPoly_eval_int, Int.cast_mul]

lemma Upoly_scale_pow_natDegree_le (c A : ℕ) :
    (Upoly_scale_pow c A).natDegree ≤ c * A := by
  unfold Upoly_scale_pow
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_comp_le.trans ?_
  have h1 : (binomPoly (c * A - j)).natDegree ≤ c * A - j := binomPoly_natDegree_le _
  have h2 : (Polynomial.C (c : ℚ) * Polynomial.X).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    simp
  have : (c * A - j) * 1 ≤ c * A := by
    rw [mul_one]; exact Nat.sub_le _ _
  exact le_trans (Nat.mul_le_mul h1 h2) this

-- ═══════════════════════════════════════════════════════════════════════
-- Section 4: Antisymmetry of `g Φ^t` and the lift to `p^{3k}`
-- ═══════════════════════════════════════════════════════════════════════

lemma phiCoeff_symm {p k : ℕ} (hk : k ≤ p) :
    phiCoeff p k = phiCoeff p (p - k) := by
  by_cases h0 : k = 0
  · subst h0; simp [phiCoeff]
  by_cases hp0 : k = p
  · subst hp0; simp [phiCoeff]
  have hk0 : 0 < k := Nat.pos_of_ne_zero h0
  have hkp : k < p := Nat.lt_of_le_of_ne hk hp0
  have hpk0 : 0 < p - k := Nat.sub_pos_of_lt hkp
  have hpkp : p - k < p := Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le k) hkp) hk0
  rw [phiCoeff_eq_choose_div p k hk0 hkp, phiCoeff_eq_choose_div p (p - k) hpk0 hpkp,
    Nat.choose_symm hk]

lemma reflect_phiPoly (p : ℕ) :
    Polynomial.reflect p (phiPoly p) = phiPoly p := by
  ext i
  rw [Polynomial.coeff_reflect, coeff_phiPoly, coeff_phiPoly]
  by_cases hi : i ≤ p
  · rw [Polynomial.revAt_le hi, phiCoeff_symm hi]
  · have : p < i := Nat.lt_of_not_ge hi
    rw [Polynomial.revAt_eq_self_of_lt this, phiCoeff_eq_zero_of_ge (le_of_lt this)]

lemma reflect_cyclo3 : Polynomial.reflect 2 cyclo3 = cyclo3 := by
  ext i
  rw [Polynomial.coeff_reflect, coeff_cyclo3]
  by_cases hi : i ≤ 2
  · rw [Polynomial.revAt_le hi, coeff_cyclo3]
    have : 2 - i ≤ 2 := Nat.sub_le _ _
    simp [hi, this]
  · have : 2 < i := Nat.lt_of_not_ge hi
    rw [Polynomial.revAt_eq_self_of_lt this, coeff_cyclo3, if_neg hi]

lemma reflect_one_sub_X_sq :
    Polynomial.reflect 2 (1 - Polynomial.X ^ 2 : Polynomial ℤ) = -(1 - Polynomial.X ^ 2) := by
  ext i
  rw [Polynomial.coeff_reflect, Polynomial.coeff_neg, Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X_pow]
  by_cases hi : i ≤ 2
  · rw [Polynomial.revAt_le hi]
    have h2i : 2 - i = 0 ↔ i = 2 := by omega
    have h2i2 : 2 - i = 2 ↔ i = 0 := by omega
    by_cases h0 : i = 0
    · subst h0; simp
    · by_cases h1 : i = 1
      · subst h1; simp
      · have : i = 2 := by omega
        subst this; simp
  · have : 2 < i := Nat.lt_of_not_ge hi
    rw [Polynomial.revAt_eq_self_of_lt this]
    simp [hi]
    omega

lemma reflect_phiQuot {p : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    Polynomial.reflect (p - 2) (phiQuot p) = phiQuot p := by
  have hmul := phiQuot_mul hp hp5
  have hφ : Polynomial.reflect p (phiPoly p) = phiPoly p := reflect_phiPoly p
  have h2 : 2 + (p - 2) = p := by omega
  have hdc : cyclo3.natDegree ≤ 2 := cyclo3_natDegree.le
  have hdQ : (phiQuot p).natDegree ≤ p - 2 :=
    (phiQuot_natDegree_le hp hp5).trans (by omega)
  have : Polynomial.reflect (2 + (p - 2)) (cyclo3 * phiQuot p) =
      Polynomial.reflect 2 cyclo3 * Polynomial.reflect (p - 2) (phiQuot p) :=
    Polynomial.reflect_mul cyclo3 (phiQuot p) hdc hdQ
  rw [h2, hmul, hφ, reflect_cyclo3] at this
  exact (mul_right_inj' cyclo3_monic.ne_zero).mp (this.symm.trans hmul.symm)

lemma one_sub_X_sq_natDegree_le :
    (1 - Polynomial.X ^ 2 : Polynomial ℤ).natDegree ≤ 2 :=
  (Polynomial.natDegree_sub_le _ _).trans (by simp)

lemma reflect_cyclo3_pow (n : ℕ) :
    Polynomial.reflect (2 * n) (cyclo3 ^ n) = cyclo3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : (cyclo3 ^ n).natDegree ≤ 2 * n := by
      refine (Polynomial.natDegree_pow_le).trans ?_
      rw [cyclo3_natDegree, Nat.mul_comm]
    have hmul := Polynomial.reflect_mul (cyclo3 ^ n) cyclo3 hd cyclo3_natDegree.le
    have : 2 * n + 2 = 2 * (n + 1) := by omega
    rw [pow_succ, ← this, hmul, ih, reflect_cyclo3]

lemma reflect_phiQuot_pow {p n : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) :
    Polynomial.reflect (n * (p - 2)) ((phiQuot p) ^ n) = (phiQuot p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : ((phiQuot p) ^ n).natDegree ≤ n * (p - 2) := by
      refine (Polynomial.natDegree_pow_le).trans ?_
      exact Nat.mul_le_mul_left n ((phiQuot_natDegree_le hp hp5).trans (by omega))
    have hd1 : (phiQuot p).natDegree ≤ p - 2 :=
      (phiQuot_natDegree_le hp hp5).trans (by omega)
    have hmul := Polynomial.reflect_mul ((phiQuot p) ^ n) (phiQuot p) hd hd1
    have : n * (p - 2) + (p - 2) = (n + 1) * (p - 2) := by ring
    rw [pow_succ, ← this, hmul, ih, reflect_phiQuot hp hp5]

lemma reflect_gPhiPowPoly {p t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5) (ht : 1 ≤ t) :
    Polynomial.reflect (t * p) (gPhiPowPoly p t) = - gPhiPowPoly p t := by
  unfold gPhiPowPoly
  have hsum : 2 + 2 * (t - 1) + t * (p - 2) = t * p := by
    have : 2 + 2 * (t - 1) = 2 * t := by omega
    rw [this, Nat.mul_sub_left_distrib, Nat.mul_comm t 2]
    have hle : 2 * t ≤ t * p := by
      rw [Nat.mul_comm t p]
      exact Nat.mul_le_mul_right t (by omega : 2 ≤ p)
    omega
  have hdc : (cyclo3 ^ (t - 1)).natDegree ≤ 2 * (t - 1) := by
    refine (Polynomial.natDegree_pow_le).trans ?_
    rw [cyclo3_natDegree, Nat.mul_comm]
  have hdQ : ((phiQuot p) ^ t).natDegree ≤ t * (p - 2) := by
    refine (Polynomial.natDegree_pow_le).trans ?_
    exact Nat.mul_le_mul_left t ((phiQuot_natDegree_le hp hp5).trans (by omega))
  have h12 : ((1 - Polynomial.X ^ 2) * cyclo3 ^ (t - 1)).natDegree ≤ 2 + 2 * (t - 1) :=
    (Polynomial.natDegree_mul_le).trans (Nat.add_le_add one_sub_X_sq_natDegree_le hdc)
  have hmul :=
    Polynomial.reflect_mul ((1 - Polynomial.X ^ 2) * cyclo3 ^ (t - 1)) ((phiQuot p) ^ t)
      h12 hdQ
  have hmul1 :=
    Polynomial.reflect_mul (1 - Polynomial.X ^ 2) (cyclo3 ^ (t - 1))
      one_sub_X_sq_natDegree_le hdc
  rw [← hsum, hmul, hmul1, reflect_one_sub_X_sq,
    reflect_cyclo3_pow (t - 1), reflect_phiQuot_pow hp hp5]
  ring

lemma gPhiPowCoeff_anti {p t M : ℕ} (hp : p.Prime) (hp5 : p ≥ 5)
    (ht : 1 ≤ t) (hM : M ≤ t) :
    gPhiPowCoeff p t (t - M) = - gPhiPowCoeff p t M := by
  have ht0 : t ≠ 0 := Nat.pos_iff_ne_zero.mp ht
  unfold gPhiPowCoeff
  simp only [ht0, ↓reduceIte]
  have hrefl := reflect_gPhiPowPoly (p := p) (t := t) hp hp5 ht
  have hle : p * M ≤ t * p := by
    rw [Nat.mul_comm t p]
    exact Nat.mul_le_mul_left p hM
  have hcoeff :
      (Polynomial.reflect (t * p) (gPhiPowPoly p t)).coeff (p * M) =
        (gPhiPowPoly p t).coeff (t * p - p * M) := by
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le hle]
  rw [hrefl, Polynomial.coeff_neg] at hcoeff
  have hsub : t * p - p * M = p * (t - M) := by
    rw [Nat.mul_comm t p, ← Nat.mul_sub_left_distrib]
  rw [hsub] at hcoeff
  linarith

lemma gPhiPowCoeff_mid {p t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5)
    (ht : 1 ≤ t) (he : Even t) :
    gPhiPowCoeff p t (t / 2) = 0 := by
  have hM : t / 2 ≤ t := Nat.div_le_self _ _
  have hanti := gPhiPowCoeff_anti hp hp5 ht hM
  have h2 : t - t / 2 = t / 2 := by
    have := Nat.two_mul_div_two_of_even he
    omega
  rw [h2] at hanti
  linarith

lemma ringChoose_succ_mul (N : ℤ) (K : ℕ) :
    (K + 1 : ℤ) * Ring.choose N (K + 1) = (N - K) * Ring.choose N K := by
  have h := ringChoose_mul_succ N (k := K + 1) (Nat.succ_pos _)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
  linarith

lemma ringChoose_ratio_prod (N : ℤ) (K δ : ℕ) :
    Ring.choose N (K + δ) * ∏ j ∈ Finset.range δ, (K + j + 1 : ℤ) =
      Ring.choose N K * ∏ j ∈ Finset.range δ, (N - K - j) := by
  induction δ with
  | zero => simp
  | succ δ ih =>
    set P : ℤ := ∏ j ∈ Finset.range δ, (K + j + 1 : ℤ)
    set Q : ℤ := ∏ j ∈ Finset.range δ, (N - K - j)
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    change Ring.choose N (K + (δ + 1)) * (P * (K + δ + 1)) =
      Ring.choose N K * (Q * (N - K - δ))
    have hsc := ringChoose_succ_mul N (K + δ)
    have hsc' : (K + δ + 1 : ℤ) * Ring.choose N (K + δ + 1) =
        (N - K - δ) * Ring.choose N (K + δ) := by
      convert hsc using 2 <;> simp [Nat.cast_add, add_assoc] <;> ring
    have hK : K + (δ + 1) = K + δ + 1 := by omega
    rw [hK]
    calc
      Ring.choose N (K + δ + 1) * (P * (K + δ + 1))
          = (Ring.choose N (K + δ + 1) * (K + δ + 1)) * P := by ring
      _ = ((K + δ + 1 : ℤ) * Ring.choose N (K + δ + 1)) * P := by ring
      _ = ((N - K - δ) * Ring.choose N (K + δ)) * P := by rw [hsc']
      _ = (Ring.choose N (K + δ) * P) * (N - K - δ) := by ring
      _ = (Ring.choose N K * Q) * (N - K - δ) := by
          have : Ring.choose N (K + δ) * P = Ring.choose N K * Q := ih
          rw [this]
      _ = Ring.choose N K * (Q * (N - K - δ)) := by ring

lemma p_dvd_pow_mul {p r : ℕ} {α : ℤ} (hr : 0 < r) :
    (p : ℤ) ∣ (p : ℤ) ^ r * α :=
  dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.pos_iff_ne_zero.mp hr)) _

lemma not_p_dvd_sub_of_not_dvd {p r : ℕ} {α a : ℤ} (hr : 0 < r)
    (ha : ¬ (p : ℤ) ∣ a) :
    ¬ (p : ℤ) ∣ (p : ℤ) ^ r * α - a := by
  intro h
  have hpα : (p : ℤ) ∣ (p : ℤ) ^ r * α := p_dvd_pow_mul (α := α) hr
  have : a = (p : ℤ) ^ r * α - ((p : ℤ) ^ r * α - a) := by ring
  exact ha (this ▸ dvd_sub hpα h)

lemma int_not_dvd_of_abs_lt {p : ℕ} {a : ℤ} (hp : 0 < p)
    (ha0 : a ≠ 0) (halt : |a| < p) : ¬ (p : ℤ) ∣ a := by
  intro ⟨c, hc⟩
  have hc0 : c ≠ 0 := fun hz => ha0 (by simp [hc, hz])
  have : (p : ℤ) ≤ |a| := by
    rw [hc, abs_mul, Int.abs_natCast]
    have : (1 : ℤ) ≤ |c| := Int.one_le_abs hc0
    nlinarith
  linarith

/-- The monic polynomial `∏_{j=0}^{δ-1} (X - (M+j))`. -/
noncomputable def intervalPoly (M δ : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.range δ, (Polynomial.X - Polynomial.C ((M + j : ℕ) : ℤ))

lemma intervalPoly_eval (M δ : ℕ) (x : ℤ) :
    (intervalPoly M δ).eval x = ∏ j ∈ Finset.range δ, (x - (M + j : ℕ)) := by
  unfold intervalPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

lemma intervalPoly_eval_sub_dvd (M δ : ℕ) (x y : ℤ) :
    x - y ∣ (intervalPoly M δ).eval x - (intervalPoly M δ).eval y :=
  Polynomial.sub_dvd_eval_sub x y _

/-- `p^r` divides `g(p^r u) - g(p^r v)` for any integer-coefficient polynomial `g`. -/
lemma eval_scale_pow_sub_dvd (g : Polynomial ℤ) (p r : ℕ) (u v : ℤ) (hr : 0 < r) :
    (p : ℤ) ^ r ∣ g.eval ((p : ℤ) ^ r * u) - g.eval ((p : ℤ) ^ r * v) := by
  have h := Polynomial.sub_dvd_eval_sub ((p : ℤ) ^ r * u) ((p : ℤ) ^ r * v) g
  have : (p : ℤ) ^ r ∣ (p : ℤ) ^ r * u - (p : ℤ) ^ r * v := by
    rw [← mul_sub]
    exact dvd_mul_right _ _
  exact dvd_trans this h

lemma nat_pow_mul_eq {p r i : ℕ} (hi : i ≤ r) :
    p ^ i * p ^ (r - i) = p ^ r := by
  rw [← pow_add, Nat.add_sub_cancel' hi]

/-- Decomposition used to read the base-`p` digits of `p^r α - s`. -/
lemma nat_pow_mul_sub_decomp {p r i α s : ℕ}
    (hp : 0 < p) (hi : i ≤ r) (hs : s ≤ p ^ i) (hα : 1 ≤ α) :
    p ^ r * α - s = p ^ i * (p ^ (r - i) * α - 1) + (p ^ i - s) := by
  have hpr : p ^ i * p ^ (r - i) = p ^ r := nat_pow_mul_eq hi
  have hge1 : 1 ≤ p ^ (r - i) * α := by
    have : 1 ≤ p ^ (r - i) := Nat.one_le_pow (r - i) p hp
    exact one_le_mul this hα
  have hpi_le : p ^ i ≤ p ^ r * α := by
    rw [← hpr, mul_assoc]
    exact Nat.le_mul_of_pos_right _ hge1
  have hleft : p ^ i * (p ^ (r - i) * α - 1) = p ^ r * α - p ^ i := by
    rw [Nat.mul_sub_left_distrib, mul_one, ← mul_assoc, hpr]
  have hdecomp : p ^ r * α - s = (p ^ r * α - p ^ i) + (p ^ i - s) :=
    (Nat.sub_add_sub_cancel hpi_le hs).symm
  rw [hdecomp, hleft]

lemma nat_pow_mul_sub_mod {p r i α s : ℕ}
    (hp : 0 < p) (hir : i ≤ r) (hs : 0 < s) (hsp : s ≤ p ^ i) (hα : 1 ≤ α) :
    (p ^ r * α - s) % p ^ i = p ^ i - s := by
  rw [nat_pow_mul_sub_decomp hp hir hsp hα, Nat.add_comm, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt]
  exact Nat.sub_lt (pow_pos hp i) hs

lemma cast_nat_sub_int {n t : ℕ} (h : t ≤ n) :
    ((n : ℤ) - (t : ℤ)) = ((n - t : ℕ) : ℤ) :=
  (Nat.cast_sub h).symm

/-- The two products in `ringChoose_ratio_prod` are evaluations of `intervalPoly`. -/
lemma intervalPoly_eval_pow_sub (M δ : ℕ) (p r c : ℕ) :
    (intervalPoly M δ).eval ((p : ℤ) ^ r * (c : ℤ)) =
      ∏ j ∈ Finset.range δ, ((p : ℤ) ^ r * (c : ℤ) - (M + j : ℕ)) :=
  intervalPoly_eval M δ _

lemma interval_prod_reindex (M δ : ℕ) (x : ℤ) :
    ∏ j ∈ Finset.range δ, (x - (M + (δ - 1 - j) : ℕ)) =
      ∏ j ∈ Finset.range δ, (x - (M + j : ℕ)) := by
  simpa using
    (Finset.prod_range_reflect (fun j => x - (M + j : ℕ)) δ)

/-- `p^r α - a` is never divisible by `p` when `0 < a < p`. -/
lemma not_p_dvd_pow_mul_sub {p r α a : ℕ} (hp : p.Prime) (hr : 0 < r)
    (ha0 : 0 < a) (hap : a < p) :
    ¬ (p : ℤ) ∣ (p : ℤ) ^ r * (α : ℤ) - (a : ℤ) := by
  refine not_p_dvd_sub_of_not_dvd hr ?_
  refine int_not_dvd_of_abs_lt hp.pos ?_ ?_
  · exact_mod_cast (Nat.pos_iff_ne_zero.mp ha0)
  · rw [Int.abs_natCast]
    exact_mod_cast hap

/-- The numerator product `Q` is coprime to `p`. -/
lemma interval_prod_coprime_p {p r α M δ : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hM : 1 ≤ M) (hMp : M + δ - 1 < p) (hδ : 0 < δ) :
    IsCoprime ((p : ℤ) ^ r)
      (∏ j ∈ Finset.range δ, ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ))) := by
  have hpI : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (p : ℤ)
      (∏ j ∈ Finset.range δ, ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ))) := by
    refine IsCoprime.prod_right ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    have ha0 : 0 < M + j := Nat.add_pos_left hM j
    have hap : M + j < p := by
      have : M + j ≤ M + (δ - 1) := Nat.add_le_add_left (Nat.le_pred_of_lt hj) _
      have h' : M + (δ - 1) = M + δ - 1 := by omega
      omega
    exact (hpI.coprime_iff_not_dvd).2 (not_p_dvd_pow_mul_sub hp hr ha0 hap)
  exact hcop.pow_left

lemma le_pow_mul_of_lt_p {p r c a : ℕ} (hp : 0 < p) (hr : 0 < r)
    (hc : 1 ≤ c) (ha : a < p) : a ≤ p ^ r * c := by
  have h1 : a < p := ha
  have h2 : p ≤ p ^ r := Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hr) p
  have h3 : p ≤ p ^ r * c := h2.trans (Nat.le_mul_of_pos_right _ hc)
  omega

lemma le_pow_mul_of_le_p {p r c a : ℕ} (hp : 0 < p) (hr : 0 < r)
    (hc : 1 ≤ c) (ha : a ≤ p) : a ≤ p ^ r * c := by
  have h2 : p ≤ p ^ r := Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hr) p
  have h3 : p ≤ p ^ r * c := h2.trans (Nat.le_mul_of_pos_right _ hc)
  omega

lemma cast_pow_mul_sub {p r β t : ℕ} (h : t ≤ p ^ r * β) :
    (((p ^ r * β : ℕ) : ℤ) - (t : ℤ)) = ((p ^ r * β - t : ℕ) : ℤ) :=
  (Nat.cast_sub h).symm

lemma alpha_le_beta_of_choose_le {p r α β t s : ℕ}
    (hs_lt : s < p ^ r)
    (ht : t ≤ p ^ r * β) (hs : s ≤ p ^ r * α)
    (hkle : p ^ r * α - s ≤ p ^ r * β - t) :
    α ≤ β := by
  by_contra h
  have hβα : β + 1 ≤ α := by omega
  have hL : ((p ^ r * α - s : ℕ) : ℤ) = (p ^ r * α : ℤ) - s := Nat.cast_sub hs
  have hR : ((p ^ r * β - t : ℕ) : ℤ) = (p ^ r * β : ℤ) - t := Nat.cast_sub ht
  have hleZ : (p ^ r * α : ℤ) - s ≤ (p ^ r * β : ℤ) - t := by
    rw [← hL, ← hR]; exact Nat.cast_le.mpr hkle
  have hmul : (p ^ r * (β + 1) : ℤ) ≤ (p ^ r * α : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_left (p ^ r) hβα
  have hsZ : (s : ℤ) < p ^ r := Nat.cast_lt.mpr hs_lt
  have htZ : (0 : ℤ) ≤ t := Nat.cast_nonneg _
  nlinarith

lemma nat_sub_pow_identity {p r α β t s : ℕ}
    (ht : t ≤ p ^ r * β) (hs : s ≤ p ^ r * α)
    (hkle : p ^ r * α - s ≤ p ^ r * β - t)
    (hαβ : α ≤ β) (hst : s ≤ t) :
    p ^ r * β - t - (p ^ r * α - s) = p ^ r * (β - α) - (t - s) := by
  apply (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℤ)))
  have hL : ((p ^ r * β - t : ℕ) : ℤ) = (p ^ r * β : ℤ) - t := Nat.cast_sub ht
  have hK : ((p ^ r * α - s : ℕ) : ℤ) = (p ^ r * α : ℤ) - s := Nat.cast_sub hs
  have h1 : ((p ^ r * β - t - (p ^ r * α - s) : ℕ) : ℤ) =
      (p ^ r * β : ℤ) - t - ((p ^ r * α : ℤ) - s) := by
    rw [Nat.cast_sub hkle, hL, hK]
  have heq : (p ^ r * β : ℤ) - t - ((p ^ r * α : ℤ) - s) =
      (p : ℤ) ^ r * ((β : ℤ) - α) - ((t : ℤ) - s) := by ring
  have hba : ((p ^ r * (β - α) : ℕ) : ℤ) = (p : ℤ) ^ r * ((β : ℤ) - α) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hαβ]
  have hsub : t - s ≤ p ^ r * (β - α) := by
    have hnn : (0 : ℤ) ≤ ((p ^ r * β - t - (p ^ r * α - s) : ℕ) : ℤ) :=
      Nat.cast_nonneg _
    have : ((t - s : ℕ) : ℤ) ≤ ((p ^ r * (β - α) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hst, hba]
      linarith [h1, heq, hnn]
    exact Nat.cast_le.mp this
  have h2 : ((p ^ r * (β - α) - (t - s) : ℕ) : ℤ) =
      (p : ℤ) ^ r * ((β : ℤ) - α) - ((t : ℤ) - s) := by
    rw [Nat.cast_sub hsub, hba, Nat.cast_sub hst]
  rw [h1, heq, h2]

/-- Kummer: `p^r` divides `C(p^r β - t, p^r α - s)` when `0 < s < t ≤ p`. -/
lemma choose_pow_sub_dvd {p r α β t s : ℕ} (hp : p.Prime)
    (hr : 0 < r) (htp : t ≤ p) (hs0 : 0 < s) (hst : s < t)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    (p : ℤ) ^ r ∣
      Ring.choose (((p ^ r * β : ℕ) : ℤ) - t) (p ^ r * α - s) := by
  have hp0 : 0 < p := hp.pos
  have ht_le : t ≤ p ^ r * β := le_pow_mul_of_le_p hp0 hr hβ htp
  have hs_lt : s < p := Nat.lt_of_lt_of_le hst htp
  have hs_le : s ≤ p ^ r * α := le_pow_mul_of_lt_p hp0 hr hα hs_lt
  set n : ℕ := p ^ r * β - t
  set k : ℕ := p ^ r * α - s
  have hncast : (((p ^ r * β : ℕ) : ℤ) - t) = (n : ℤ) := by
    simpa [n] using cast_pow_mul_sub ht_le
  rw [hncast]
  by_cases hkn : n < k
  · rw [ringChoose_eq_zero_of_lt hkn]
    exact dvd_zero _
  · have hkle : k ≤ n := Nat.le_of_not_gt hkn
    haveI : Fact p.Prime := ⟨hp⟩
    have hkpos : 0 < k := Nat.sub_pos_of_lt (lt_of_lt_of_le hs_lt
      ((Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hr) p).trans
        (Nat.le_mul_of_pos_right _ hα)))
    have hn0 : n ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt (lt_of_lt_of_le hkpos hkle))
    have hlog : Nat.log p n < n + r + 1 :=
      Nat.lt_trans (Nat.log_lt_self p hn0) (by omega)
    have hs_lt_pow : s < p ^ r :=
      lt_of_lt_of_le hs_lt (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hr) p)
    have hαβ : α ≤ β := alpha_le_beta_of_choose_le hs_lt_pow ht_le hs_le hkle
    have hst' : s ≤ t := Nat.le_of_lt hst
    have hnk : n - k = p ^ r * (β - α) - (t - s) :=
      nat_sub_pow_identity ht_le hs_le hkle hαβ hst'
    have hγ : 1 ≤ β - α := by
      have : α < β := by
        by_contra hne
        have heq : α = β := le_antisymm hαβ (Nat.le_of_not_gt (fun h => hne h))
        subst heq
        have : k ≤ n := hkle
        -- p^r α - s ≤ p^r α - t implies t ≤ s, contradiction
        have hs_le' : s ≤ p ^ r * α := hs_le
        have ht_le' : t ≤ p ^ r * α := ht_le
        omega
      omega
    have hMpos : 0 < t - s := Nat.sub_pos_of_lt hst
    have hMlt : t - s < p := Nat.lt_of_lt_of_le (Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le s) hst) hs0) htp
    have hcarries : ∀ i ∈ Finset.Ico 1 (r + 1),
        p ^ i ≤ k % p ^ i + (n - k) % p ^ i := by
      intro i hi
      simp only [Finset.mem_Ico] at hi
      have hi1 : 1 ≤ i := hi.1
      have hir : i ≤ r := Nat.lt_succ_iff.mp hi.2
      have hsp : s ≤ p ^ i := by
        have : p ≤ p ^ i :=
          Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hi1)) p
        omega
      have hMp : t - s ≤ p ^ i := by
        have : p ≤ p ^ i :=
          Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hi1)) p
        omega
      have hkmod : k % p ^ i = p ^ i - s :=
        nat_pow_mul_sub_mod hp0 hir hs0 hsp hα
      have hnkmod : (n - k) % p ^ i = p ^ i - (t - s) := by
        rw [hnk]
        exact nat_pow_mul_sub_mod hp0 hir hMpos hMp hγ
      rw [hkmod, hnkmod]
      have hpi_ge : p ≤ p ^ i :=
        Nat.le_self_pow (Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hi1)) p
      have ht_le_pi : t ≤ p ^ i := Nat.le_trans htp hpi_ge
      have hsum : p ^ i - s + (p ^ i - (t - s)) = p ^ i + (p ^ i - t) := by omega
      rw [hsum]
      exact Nat.le_add_right _ _
    have hval : r ≤ padicValNat p (n.choose k) := by
      rw [padicValNat_choose (p := p) hkle hlog]
      have hsub : Finset.Ico 1 (r + 1) ⊆
          (Finset.Ico 1 (n + r + 1)).filter
            (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
        refine ⟨⟨hi.1, ?_⟩, hcarries i (Finset.mem_Ico.mpr hi)⟩
        omega
      have hle := Finset.card_le_card hsub
      have hcard : #(Finset.Ico 1 (r + 1)) = r := by
        rw [Nat.card_Ico]; omega
      rw [hcard] at hle
      exact hle
    have hdiv : p ^ r ∣ n.choose k :=
      (padicValNat_dvd_iff_le (Nat.choose_ne_zero hkle)).mpr hval
    rw [ringChoose_nat]
    exact_mod_cast hdiv

/-- Difference of two binomials with the same high `p^r`-digits, for `t < p`. -/
lemma binom_diff_pow_dvd {p r α β t M : ℕ} (hp : p.Prime)
    (hr : 0 < r) (htp : t ≤ p) (hM : 1 ≤ M) (hM2 : 2 * M < t)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    (p : ℤ) ^ (2 * r) ∣
      Ring.choose (((p ^ r * β : ℕ) : ℤ) - t) (p ^ r * α - M) -
        Ring.choose (((p ^ r * β : ℕ) : ℤ) - t) (p ^ r * α - (t - M)) := by
  have hp0 : 0 < p := hp.pos
  have hδpos : 0 < t - 2 * M := Nat.sub_pos_of_lt hM2
  have hMt : M < t := by omega
  have hs : t - M < t := Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le _) hMt) hM
  have hs0 : 0 < t - M := Nat.sub_pos_of_lt hMt
  set N : ℤ := ((p ^ r * β : ℕ) : ℤ) - t
  set K2 : ℕ := p ^ r * α - (t - M)
  set δ : ℕ := t - 2 * M
  have hKsum : K2 + δ = p ^ r * α - M := by
    have h1 : t - M + (t - 2 * M) = t - M + t - 2 * M := by omega
    have : p ^ r * α - (t - M) + (t - 2 * M) = p ^ r * α - M := by
      have hle1 : t - M ≤ p ^ r * α :=
        le_pow_mul_of_lt_p hp0 hr hα (Nat.lt_of_lt_of_le hs htp)
      have hle2 : M ≤ p ^ r * α :=
        le_pow_mul_of_lt_p hp0 hr hα (Nat.lt_of_lt_of_le hMt htp)
      omega
    simpa [K2, δ] using this
  have hratio := ringChoose_ratio_prod N K2 δ
  rw [hKsum] at hratio
  set Qval : ℤ := ∏ j ∈ Finset.range δ, (K2 + j + 1 : ℤ)
  set Pval : ℤ := ∏ j ∈ Finset.range δ, (N - K2 - j)
  have hratio' : Ring.choose N (p ^ r * α - M) * Qval =
      Ring.choose N K2 * Pval := hratio
  -- Identify Pval, Qval with intervalPoly evaluations
  have hleK : t - M ≤ p ^ r * α :=
    le_pow_mul_of_lt_p hp0 hr hα (Nat.lt_of_lt_of_le hs htp)
  have hk2Z : (K2 : ℤ) = (p ^ r * α : ℤ) - ↑(t - M) := by
    simpa [K2] using (Nat.cast_sub hleK)
  have hidx : ∀ j ∈ Finset.range δ,
      t - M - 1 - j = M + (δ - 1 - j) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    omega
  have hQfac : ∀ j ∈ Finset.range δ,
      (K2 + j + 1 : ℤ) = (p : ℤ) ^ r * (α : ℤ) - (M + (δ - 1 - j) : ℕ) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjδ : j + 1 ≤ δ := by omega
    have htm : j + 1 ≤ t - M := by omega
    have hcast : ((M + (δ - 1 - j) : ℕ) : ℤ) = (t : ℤ) - M - 1 - j := by
      have hid := hidx j (Finset.mem_range.mpr hj)
      have htriple : ((t - M - 1 - j : ℕ) : ℤ) = (t : ℤ) - M - 1 - j := by
        have htmj : M + 1 + j ≤ t := by omega
        rw [show t - M - 1 - j = t - (M + 1 + j) from by omega]
        rw [Nat.cast_sub htmj, Nat.cast_add, Nat.cast_add, Nat.cast_one]
        ring
      rw [← hid]; exact htriple
    rw [hk2Z, Nat.cast_sub (Nat.le_of_lt hMt), hcast]
    push_cast
    ring
  have hQval : Qval =
      ∏ j ∈ Finset.range δ, ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ)) := by
    unfold Qval
    have h1 : ∏ j ∈ Finset.range δ, (K2 + j + 1 : ℤ) =
        ∏ j ∈ Finset.range δ,
          ((p : ℤ) ^ r * (α : ℤ) - (M + (δ - 1 - j) : ℕ)) :=
      Finset.prod_congr rfl hQfac
    rw [h1]
    exact interval_prod_reindex M δ ((p : ℤ) ^ r * (α : ℤ))
  have hPfac : ∀ j ∈ Finset.range δ,
      (N - K2 - j : ℤ) = (p : ℤ) ^ r * ((β : ℤ) - α) - (M + j : ℕ) := by
    intro j _hj
    have : (N - K2 - j : ℤ) =
        ((p ^ r * β : ℕ) : ℤ) - t - ((p ^ r * α : ℤ) - ↑(t - M)) - j := by
      simp [N, hk2Z]
    rw [this, Nat.cast_sub (Nat.le_of_lt hMt)]
    push_cast
    ring
  have hPval : Pval =
      (intervalPoly M δ).eval ((p : ℤ) ^ r * ((β : ℤ) - α)) := by
    unfold Pval
    rw [intervalPoly_eval]
    exact Finset.prod_congr rfl hPfac
  have hQval' : Qval =
      (intervalPoly M δ).eval ((p : ℤ) ^ r * (α : ℤ)) := by
    rw [hQval, intervalPoly_eval]
  have hPQ : (p : ℤ) ^ r ∣ Pval - Qval := by
    rw [hPval, hQval']
    exact eval_scale_pow_sub_dvd (intervalPoly M δ) p r ((β : ℤ) - α) (α : ℤ) hr
  -- Coprimality of Qval with p^r
  have hMp : M + δ - 1 < p := by
    have : M + δ - 1 = t - M - 1 := by omega
    omega
  have hQcop : IsCoprime ((p : ℤ) ^ r) Qval := by
    rw [hQval]
    exact interval_prod_coprime_p (α := α) hp hr hM hMp hδpos
  -- p^r divides the second binomial
  have hC2 : (p : ℤ) ^ r ∣ Ring.choose N K2 := by
    unfold N K2
    exact choose_pow_sub_dvd hp hr htp hs0 hs hα hβ
  -- Glue: Qval * (C1 - C2) = C2 * (Pval - Qval)
  have hiden : Qval * (Ring.choose N (p ^ r * α - M) - Ring.choose N K2) =
      Ring.choose N K2 * (Pval - Qval) := by
    linarith [hratio']
  have hpow : (p : ℤ) ^ (2 * r) = (p : ℤ) ^ r * (p : ℤ) ^ r := by
    rw [pow_mul, pow_two]; ring
  have hmul : (p : ℤ) ^ (2 * r) ∣
      Ring.choose N K2 * (Pval - Qval) := by
    rw [hpow]
    exact mul_dvd_mul hC2 hPQ
  have hQdvd : (p : ℤ) ^ (2 * r) ∣
      Qval * (Ring.choose N (p ^ r * α - M) - Ring.choose N K2) := by
    rwa [hiden]
  have hcop2 : IsCoprime ((p : ℤ) ^ (2 * r)) Qval := by
    rw [hpow]
    exact hQcop.mul_left hQcop
  exact hcop2.dvd_of_dvd_mul_left hQdvd

lemma choose_scale_self_dvd {p r B : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    (p : ℤ) ^ (r - 1) ∣ Ring.choose ((p ^ r * B : ℕ) : ℤ) p := by
  rw [ringChoose_nat]
  by_cases hB : B = 0
  · subst hB
    rw [mul_zero, Nat.choose_eq_zero_of_lt hp.pos]
    simp
  · have hdesc : (p ^ r * B).descFactorial p =
        p.factorial * (p ^ r * B).choose p :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    have hprod : (p ^ r * B).descFactorial p =
        ∏ i ∈ Finset.range p, (p ^ r * B - i) :=
      Nat.descFactorial_eq_prod_range _ _
    have h0mem : 0 ∈ Finset.range p := by
      simp only [Finset.mem_range]; exact hp.pos
    have hpr : p ^ r ∣ (p ^ r * B).descFactorial p := by
      rw [hprod]
      have hfac : p ^ r ∣ p ^ r * B - 0 := by
        simpa using (dvd_mul_right (p ^ r) B)
      exact dvd_trans hfac (Finset.dvd_prod_of_mem (fun i => p ^ r * B - i) h0mem)
    have hfacp : p.factorial = p * (p - 1).factorial :=
      (Nat.mul_factorial_pred hp.ne_zero).symm
    by_cases hr1 : r = 1
    · subst hr1; simp
    · have hr1pos : 0 < r - 1 := by omega
      have hcop : Nat.Coprime p (p - 1).factorial := by
        rw [hp.coprime_iff_not_dvd]
        intro h
        have hle : p ≤ p - 1 := (hp.dvd_factorial).mp h
        have : 2 ≤ p := hp.two_le
        omega
      have hcop' : Nat.Coprime (p ^ (r - 1)) (p - 1).factorial :=
        (Nat.coprime_pow_left_iff hr1pos p _).mpr hcop
      have hpow : p ^ r = p * p ^ (r - 1) := by
        cases r with
        | zero => omega
        | succ r => rw [pow_succ, Nat.add_sub_cancel, mul_comm]
      have h1 : p * p ^ (r - 1) ∣
          p * (p - 1).factorial * (p ^ r * B).choose p := by
        rw [← hfacp, ← hdesc, ← hpow]
        exact hpr
      have h2 : p ^ (r - 1) ∣ (p - 1).factorial * (p ^ r * B).choose p :=
        Nat.dvd_of_mul_dvd_mul_left hp.pos (by
          convert h1 using 1 <;> ring)
      have hch : p ^ (r - 1) ∣ (p ^ r * B).choose p :=
        hcop'.dvd_of_dvd_mul_left h2
      exact_mod_cast hch

lemma choose_scale_pow_dvd {p r B t : ℕ} (hp : p.Prime)
    (hr : 0 < r) (ht0 : 0 < t) (htp : t < p) :
    (p : ℤ) ^ r ∣ Ring.choose ((p ^ r * B : ℕ) : ℤ) t := by
  rw [ringChoose_nat]
  by_cases hB : B = 0
  · subst hB
    rw [mul_zero, Nat.choose_eq_zero_of_lt ht0]
    simp
  · have hdesc : (p ^ r * B).descFactorial t =
        t.factorial * (p ^ r * B).choose t :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    have hprod : (p ^ r * B).descFactorial t =
        ∏ i ∈ Finset.range t, (p ^ r * B - i) :=
      Nat.descFactorial_eq_prod_range _ _
    have h0mem : 0 ∈ Finset.range t := by
      simp only [Finset.mem_range]; exact ht0
    have hpr : p ^ r ∣ (p ^ r * B).descFactorial t := by
      rw [hprod]
      have hfac : p ^ r ∣ p ^ r * B - 0 := by
        simpa using (dvd_mul_right (p ^ r) B)
      exact dvd_trans hfac (Finset.dvd_prod_of_mem (fun i => p ^ r * B - i) h0mem)
    have hcop : Nat.Coprime (p ^ r) t.factorial := by
      refine (Nat.coprime_pow_left_iff hr p t.factorial).mpr ?_
      rw [hp.coprime_iff_not_dvd]
      intro h
      have : p ≤ t := (hp.dvd_factorial).mp h
      omega
    have hch : p ^ r ∣ (p ^ r * B).choose t :=
      hcop.dvd_of_dvd_mul_left (hdesc ▸ hpr)
    exact_mod_cast hch

lemma inner_sum_restrict {p A t : ℕ} (B : ℤ) (hp : p.Prime) (hp5 : p ≥ 5)
    (ht : 1 ≤ t) (hA : t - 1 ≤ A) :
    ∑ M ∈ Finset.range (A + 1),
        gPhiPowCoeff p t M * Ring.choose (B - ↑t) (A - M) =
      ∑ M ∈ Finset.Icc 1 (t - 1),
        gPhiPowCoeff p t M * Ring.choose (B - ↑t) (A - M) := by
  have hsub : Finset.Icc 1 (t - 1) ⊆ Finset.range (A + 1) := by
    intro M hM
    simp only [Finset.mem_Icc, Finset.mem_range] at hM ⊢
    omega
  rw [← Finset.sum_subset hsub]
  intro M hM hnot
  have h0 : gPhiPowCoeff p t 0 = 0 := gPhiPowCoeff_zero_of_M_zero hp hp5 ht
  simp only [Finset.mem_Icc, Finset.mem_range, not_and, not_le] at hM hnot
  by_cases hM0 : M = 0
  · subst hM0; simp [h0]
  · have hMt : t ≤ M := by omega
    simp [gPhiPowCoeff_eq_zero_of_ge hp hp5 ht hMt]

/-- Pair the inner sum using antisymmetry of `gPhiPowCoeff`. -/
lemma inner_sum_pair {p A t : ℕ} (B : ℤ) (hp : p.Prime) (hp5 : p ≥ 5)
    (ht : 1 ≤ t) (hA : t - 1 ≤ A) :
    ∑ M ∈ Finset.range (A + 1),
        gPhiPowCoeff p t M * Ring.choose (B - ↑t) (A - M) =
      ∑ M ∈ (Finset.Icc 1 (t - 1)).filter (fun M => 2 * M < t),
        gPhiPowCoeff p t M *
          (Ring.choose (B - ↑t) (A - M) -
           Ring.choose (B - ↑t) (A - (t - M))) := by
  rw [inner_sum_restrict B hp hp5 ht hA]
  set S := Finset.Icc 1 (t - 1)
  set F := S.filter (fun M => 2 * M < t)
  set G := S.filter (fun M => t < 2 * M)
  set Mid := S.filter (fun M => 2 * M = t)
  have hdisjFG : Disjoint F G := by
    refine Finset.disjoint_filter.mpr ?_
    intro _ _ hF hG; omega
  have hdisjMid : Disjoint (F ∪ G) Mid := by
    refine Finset.disjoint_left.mpr ?_
    intro M hFG hMid
    simp only [F, G, Mid, Finset.mem_union, Finset.mem_filter] at hFG hMid
    omega
  have hdecomp : S = F ∪ G ∪ Mid := by
    ext M
    simp only [S, F, G, Mid, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hmid0 : ∑ M ∈ Mid,
      gPhiPowCoeff p t M * Ring.choose (B - ↑t) (A - M) = 0 := by
    refine Finset.sum_eq_zero fun M hM => ?_
    simp only [Mid, S, Finset.mem_filter, Finset.mem_Icc] at hM
    have he : Even t := ⟨M, by omega⟩
    have hMeq : M = t / 2 := by omega
    rw [hMeq, gPhiPowCoeff_mid hp hp5 ht he, zero_mul]
  rw [hdecomp, Finset.sum_union hdisjMid, hmid0, add_zero, Finset.sum_union hdisjFG]
  have hGsum :
      ∑ M ∈ G, gPhiPowCoeff p t M * Ring.choose (B - ↑t) (A - M) =
        ∑ M ∈ F, gPhiPowCoeff p t (t - M) *
          Ring.choose (B - ↑t) (A - (t - M)) := by
    refine Finset.sum_nbij' (fun M => t - M) (fun M => t - M) ?_ ?_ ?_ ?_ ?_
    · intro M hM
      simp only [G, F, S, Finset.mem_filter, Finset.mem_Icc] at hM ⊢
      omega
    · intro M hM
      simp only [G, F, S, Finset.mem_filter, Finset.mem_Icc] at hM ⊢
      omega
    · intro M hM
      simp only [G, S, Finset.mem_filter, Finset.mem_Icc] at hM
      have : M ≤ t := by omega
      exact Nat.sub_sub_self this
    · intro M hM
      simp only [F, S, Finset.mem_filter, Finset.mem_Icc] at hM
      have : M ≤ t := by omega
      exact Nat.sub_sub_self this
    · intro M hM
      simp only [G, S, Finset.mem_filter, Finset.mem_Icc] at hM
      have h1 : t - (t - M) = M := Nat.sub_sub_self (by omega)
      simp [h1]
  rw [hGsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun M hM => ?_
  simp only [F, S, Finset.mem_filter, Finset.mem_Icc] at hM
  have hanti := gPhiPowCoeff_anti hp hp5 ht (by omega : M ≤ t)
  rw [hanti]
  ring

lemma inner_sum_pow_dvd {p r α β t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5)
    (hr : 0 < r) (ht3 : 3 ≤ t) (htp : t ≤ p)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    (p : ℤ) ^ (2 * r) ∣
      ∑ M ∈ Finset.range (p ^ r * α + 1),
        gPhiPowCoeff p t M *
          Ring.choose (((p ^ r * β : ℕ) : ℤ) - t) (p ^ r * α - M) := by
  have ht : 1 ≤ t := by omega
  have hA : t - 1 ≤ p ^ r * α := by
    have : t - 1 < p := by omega
    exact le_pow_mul_of_lt_p hp.pos hr hα this
  rw [inner_sum_pair (((p ^ r * β : ℕ) : ℤ)) hp hp5 ht hA]
  refine Finset.dvd_sum fun M hM => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hM
  have hM1 : 1 ≤ M := hM.1.1
  have hM2 : 2 * M < t := hM.2
  exact dvd_mul_of_dvd_right
    (binom_diff_pow_dvd hp hr htp hM1 hM2 hα hβ) _

lemma U_zero_right {n : ℕ} (hn : 0 < n) : U n 0 = gCoeff n := by
  unfold U
  have hterm : ∀ j ∈ Finset.range (n + 1),
      gCoeff j * Ring.choose (0 : ℤ) (n - j) =
        if j = n then gCoeff n else 0 := by
    intro j hj
    by_cases h : j = n
    · subst h; simp [Ring.choose_zero_right]
    · have : 0 < n - j := by
        simp only [Finset.mem_range] at hj; omega
      rw [if_neg h, ringChoose_zero_of_neg this, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp [hn]

-- ═══════════════════════════════════════════════════════════════════════
-- Middle-range helpers: `p < t < 3(r+1)`
-- ═══════════════════════════════════════════════════════════════════════

lemma three_mul_succ_le_pow {p r : ℕ} (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    3 * (r + 1) ≤ p ^ r := by
  have hp : 5 ≤ p := hp5
  induction r, hr using Nat.le_induction with
  | base =>
    have : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
    omega
  | succ r hr ih =>
    have h1 : p ^ (r + 1) = p ^ r * p := pow_succ _ _
    have h2 : 3 * (r + 1) * 5 ≤ p ^ r * p := Nat.mul_le_mul ih hp
    have h3 : 3 * (r + 1 + 1) ≤ 3 * (r + 1) * 5 := by omega
    exact h3.trans (h1 ▸ h2)

lemma le_pow_mul_of_lt_pow {p r c a : ℕ} (hc : 1 ≤ c) (ha : a < p ^ r) :
    a ≤ p ^ r * c :=
  (Nat.le_of_lt ha).trans (Nat.le_mul_of_pos_right _ hc)

lemma padicValNat_le_of_dvd {p a b : ℕ} [Fact p.Prime]
    (h : a ∣ b) (hb : b ≠ 0) :
    padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).mp (dvd_trans pow_padicValNat_dvd h)

lemma padicValNat_prod {ι : Type*} [DecidableEq ι] {p : ℕ} [Fact p.Prime]
    (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self _ _)
    have hs0 : (∏ i ∈ s, f i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [padicValNat.mul ha0 hs0, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

lemma factorial_eq_prod_Icc (n : ℕ) :
    n.factorial = ∏ i ∈ Finset.Icc 1 n, i := by
  rw [Nat.factorial_eq_prod_range_add_one]
  refine Finset.prod_nbij' (fun i => i + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro i _hi
    simp
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    exact Nat.sub_add_cancel hi.1
  · intro i _hi; rfl

lemma padicValNat_factorial_eq_sum {p n : ℕ} [Fact p.Prime] :
    padicValNat p n.factorial = ∑ i ∈ Finset.Icc 1 n, padicValNat p i := by
  have hf : ∀ i ∈ Finset.Icc 1 n, i ≠ 0 := by
    intro i hi; simp only [Finset.mem_Icc] at hi; omega
  rw [factorial_eq_prod_Icc, padicValNat_prod _ _ hf]

lemma padicValNat_pow_mul_sub {p r α a : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hα : 1 ≤ α) (ha0 : 0 < a) (ha : a < p ^ r) :
    padicValNat p (p ^ r * α - a) = padicValNat p a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : a ≤ p ^ r * α := le_pow_mul_of_lt_pow hα ha
  have hpos : 0 < p ^ r * α - a := Nat.sub_pos_of_lt (lt_of_lt_of_le ha
    (Nat.le_mul_of_pos_right _ hα))
  have hn0 : p ^ r * α - a ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  have hvlt : padicValNat p a < r := by
    have hdiv : p ^ padicValNat p a ∣ a := pow_padicValNat_dvd
    have hle' : p ^ padicValNat p a ≤ a := Nat.le_of_dvd ha0 hdiv
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp (lt_of_le_of_lt hle' ha)
  have hdiv : p ^ padicValNat p a ∣ p ^ r * α - a := by
    have h1 : p ^ padicValNat p a ∣ p ^ r * α :=
      dvd_trans (pow_dvd_pow p (Nat.le_of_lt hvlt)) (dvd_mul_right _ _)
    have h2 : p ^ padicValNat p a ∣ a := pow_padicValNat_dvd
    exact Nat.dvd_sub h1 h2
  have hnot : ¬ p ^ (padicValNat p a + 1) ∣ p ^ r * α - a := by
    intro h
    have hpr : p ^ (padicValNat p a + 1) ∣ p ^ r * α :=
      dvd_trans (pow_dvd_pow p (Nat.succ_le_of_lt hvlt)) (dvd_mul_right _ _)
    have : p ^ (padicValNat p a + 1) ∣ a := by
      have hsub : p ^ (padicValNat p a + 1) ∣
          p ^ r * α - (p ^ r * α - a) := Nat.dvd_sub hpr h
      rwa [Nat.sub_sub_self hle] at hsub
    exact (pow_succ_padicValNat_not_dvd (Nat.pos_iff_ne_zero.mp ha0)) this
  apply le_antisymm
  · by_contra h
    have : padicValNat p a + 1 ≤ padicValNat p (p ^ r * α - a) := by omega
    exact hnot ((padicValNat_dvd_iff_le hn0).mpr this)
  · exact (padicValNat_dvd_iff_le hn0).mp hdiv

lemma padicValInt_pow_mul_sub {p r α a : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hα : 1 ≤ α) (ha0 : 0 < a) (ha : a < p ^ r) :
    padicValInt p ((p : ℤ) ^ r * (α : ℤ) - (a : ℤ)) = padicValNat p a := by
  have hle : a ≤ p ^ r * α := le_pow_mul_of_lt_pow hα ha
  have hz : ((p : ℤ) ^ r * (α : ℤ) - (a : ℤ)) =
      ((p ^ r * α - a : ℕ) : ℤ) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_sub hle]
  rw [padicValInt, hz, Int.natAbs_natCast, padicValNat_pow_mul_sub hp hr hα ha0 ha]

lemma padicValInt_prod {ι : Type*} [DecidableEq ι] {p : ℕ} [Fact p.Prime]
    (s : Finset ι) (f : ι → ℤ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValInt p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValInt p (f i) := by
  induction s using Finset.induction with
  | empty => simp [padicValInt]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self _ _)
    have hs0 : (∏ i ∈ s, f i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [padicValInt.mul ha0 hs0, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `p^{r - v_p(t)}` divides `C(p^r B, t)` when `0 < t < p^r`. -/
lemma choose_scale_val_dvd {p r B t : ℕ} (hp : p.Prime) (hr : 0 < r)
    (ht0 : 0 < t) (ht : t < p ^ r) :
    (p : ℤ) ^ (r - padicValNat p t) ∣ Ring.choose ((p ^ r * B : ℕ) : ℤ) t := by
  rw [ringChoose_nat]
  by_cases hB : B = 0
  · subst hB
    rw [mul_zero, Nat.choose_eq_zero_of_lt ht0]
    simp
  · haveI : Fact p.Prime := ⟨hp⟩
    have hBpos : 1 ≤ B := Nat.pos_of_ne_zero hB
    have htle : t ≤ p ^ r * B := le_pow_mul_of_lt_pow hBpos ht
    have hch0 : (p ^ r * B).choose t ≠ 0 := Nat.choose_ne_zero htle
    have hdesc : (p ^ r * B).descFactorial t =
        t.factorial * (p ^ r * B).choose t :=
      Nat.descFactorial_eq_factorial_mul_choose _ _
    have hprod : (p ^ r * B).descFactorial t =
        ∏ i ∈ Finset.range t, (p ^ r * B - i) :=
      Nat.descFactorial_eq_prod_range _ _
    have hf : ∀ i ∈ Finset.range t, p ^ r * B - i ≠ 0 := by
      intro i hi
      simp only [Finset.mem_range] at hi
      have : i < p ^ r * B := lt_of_lt_of_le hi htle
      exact Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt this)
    have hval_desc : padicValNat p ((p ^ r * B).descFactorial t) =
        ∑ i ∈ Finset.range t, padicValNat p (p ^ r * B - i) := by
      rw [hprod, padicValNat_prod _ _ hf]
    have h0mem : 0 ∈ Finset.range t := by
      simp only [Finset.mem_range]; exact ht0
    have hval0 : padicValNat p (p ^ r * B - 0) = r + padicValNat p B := by
      simp only [Nat.sub_zero]
      rw [padicValNat.mul (pow_ne_zero r hp.ne_zero) hB, padicValNat.prime_pow]
    have hvali : ∀ i ∈ Finset.range t, i ≠ 0 →
        padicValNat p (p ^ r * B - i) = padicValNat p i := by
      intro i hi hi0
      simp only [Finset.mem_range] at hi
      exact padicValNat_pow_mul_sub hp hr hBpos (Nat.pos_of_ne_zero hi0)
        (lt_trans hi ht)
    have hsum : ∑ i ∈ Finset.range t, padicValNat p (p ^ r * B - i) =
        r + padicValNat p B + ∑ i ∈ (Finset.range t).erase 0, padicValNat p i := by
      have hsplit :=
        (Finset.sum_erase_add (s := Finset.range t)
          (f := fun i => padicValNat p (p ^ r * B - i)) h0mem).symm
      rw [hsplit, hval0]
      have hrest :
          ∑ i ∈ (Finset.range t).erase 0, padicValNat p (p ^ r * B - i) =
            ∑ i ∈ (Finset.range t).erase 0, padicValNat p i :=
        Finset.sum_congr rfl fun i hi => by
          have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
          have hir : i ∈ Finset.range t := (Finset.mem_erase.mp hi).2
          exact hvali i hir hi0
      rw [hrest]
      ac_rfl
    have herase : ∑ i ∈ (Finset.range t).erase 0, padicValNat p i =
        ∑ i ∈ Finset.Icc 1 (t - 1), padicValNat p i := by
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext i
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
      omega
    have hfac : padicValNat p t.factorial =
        padicValNat p t + padicValNat p (t - 1).factorial := by
      have htne : t ≠ 0 := Nat.pos_iff_ne_zero.mp ht0
      rw [← Nat.mul_factorial_pred htne]
      rw [padicValNat.mul htne (Nat.factorial_ne_zero _)]
    have hmul : padicValNat p ((p ^ r * B).descFactorial t) =
        padicValNat p t.factorial + padicValNat p ((p ^ r * B).choose t) := by
      rw [hdesc, padicValNat.mul (Nat.factorial_ne_zero _) hch0]
    have hv1 : padicValNat p (t - 1).factorial =
        ∑ i ∈ Finset.Icc 1 (t - 1), padicValNat p i :=
      padicValNat_factorial_eq_sum
    have hveq : padicValNat p ((p ^ r * B).choose t) =
        r + padicValNat p B - padicValNat p t := by
      have := hmul
      rw [hval_desc, hsum, herase, hfac, hv1] at this
      -- this: r + v(B) + v((t-1)!) = (v(t) + v((t-1)!)) + v(choose)
      have hcancel : r + padicValNat p B + padicValNat p (t - 1).factorial =
          padicValNat p t + padicValNat p (t - 1).factorial
            + padicValNat p ((p ^ r * B).choose t) := by
        convert this using 1
        · rw [hv1]
        · rw [hv1]
      omega
    have : r - padicValNat p t ≤ padicValNat p ((p ^ r * B).choose t) := by
      omega
    exact_mod_cast (padicValNat_dvd_iff_le hch0).mpr this

/-- Kummer carries for `C(p^r β - t, p^r α - s)` at every level `i` with `t ≤ p^i`. -/
lemma choose_pow_sub_carry {p r α β t s i : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hs0 : 0 < s) (hst : s < t) (hti : t ≤ p ^ i)
    (hir : i ≤ r) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hkle : p ^ r * α - s ≤ p ^ r * β - t) :
    p ^ i ≤ (p ^ r * α - s) % p ^ i +
      ((p ^ r * β - t) - (p ^ r * α - s)) % p ^ i := by
  have hp0 : 0 < p := hp.pos
  have hs_lt_pow : s < p ^ r :=
    lt_of_lt_of_le (lt_of_lt_of_le hst hti) (Nat.pow_le_pow_right hp0 hir)
  have ht_le : t ≤ p ^ r * β :=
    (hti.trans (Nat.pow_le_pow_right hp0 hir)).trans (Nat.le_mul_of_pos_right _ hβ)
  have hs_le : s ≤ p ^ r * α := le_pow_mul_of_lt_pow hα hs_lt_pow
  have hαβ : α ≤ β := alpha_le_beta_of_choose_le hs_lt_pow ht_le hs_le hkle
  have hst' : s ≤ t := Nat.le_of_lt hst
  have hnk : (p ^ r * β - t) - (p ^ r * α - s) =
      p ^ r * (β - α) - (t - s) :=
    nat_sub_pow_identity ht_le hs_le hkle hαβ hst'
  have hγ : 1 ≤ β - α := by
    have : α < β := by
      by_contra hne
      have heq : α = β := le_antisymm hαβ (Nat.le_of_not_gt (fun h => hne h))
      subst heq
      omega
    omega
  have hMpos : 0 < t - s := Nat.sub_pos_of_lt hst
  have hsp : s ≤ p ^ i := Nat.le_trans (Nat.le_of_lt hst) hti
  have hMp : t - s ≤ p ^ i := Nat.le_trans (Nat.sub_le t s) hti
  have hkmod : (p ^ r * α - s) % p ^ i = p ^ i - s :=
    nat_pow_mul_sub_mod hp0 hir hs0 hsp hα
  have hnkmod : ((p ^ r * β - t) - (p ^ r * α - s)) % p ^ i = p ^ i - (t - s) := by
    rw [hnk]
    exact nat_pow_mul_sub_mod hp0 hir hMpos hMp hγ
  rw [hkmod, hnkmod]
  omega

lemma choose_pow_sub_val_dvd {p r α β t s : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hs0 : 0 < s) (hst : s < t) (htpr : t < p ^ r)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    (p : ℤ) ^ ((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card ∣
      Ring.choose (((p ^ r * β : ℕ) : ℤ) - t) (p ^ r * α - s) := by
  have hp0 : 0 < p := hp.pos
  have ht_le : t ≤ p ^ r * β := le_pow_mul_of_lt_pow hβ htpr
  have hs_lt_pow : s < p ^ r := lt_trans hst htpr
  have hs_le : s ≤ p ^ r * α := le_pow_mul_of_lt_pow hα hs_lt_pow
  set n : ℕ := p ^ r * β - t
  set k : ℕ := p ^ r * α - s
  have hncast : (((p ^ r * β : ℕ) : ℤ) - t) = (n : ℤ) := by
    simpa [n] using cast_pow_mul_sub ht_le
  rw [hncast]
  by_cases hkn : n < k
  · rw [ringChoose_eq_zero_of_lt hkn]
    exact dvd_zero _
  · have hkle : k ≤ n := Nat.le_of_not_gt hkn
    haveI : Fact p.Prime := ⟨hp⟩
    have hkpos : 0 < k := Nat.sub_pos_of_lt (lt_of_lt_of_le hs_lt_pow
      (Nat.le_mul_of_pos_right _ hα))
    have hn0 : n ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt (lt_of_lt_of_le hkpos hkle))
    have hlog : Nat.log p n < n + r + 1 :=
      Nat.lt_trans (Nat.log_lt_self p hn0) (by omega)
    have hcarries : ∀ i ∈ (Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i),
        p ^ i ≤ k % p ^ i + (n - k) % p ^ i := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      have hi1 : 1 ≤ i := hi.1.1
      have hir : i ≤ r := Nat.lt_succ_iff.mp hi.1.2
      have hti : t ≤ p ^ i := hi.2
      simpa [n, k] using
        choose_pow_sub_carry (p := p) (r := r) (α := α) (β := β) (t := t)
          (s := s) (i := i) hp hr hs0 hst hti hir hα hβ (by simpa [n, k] using hkle)
    have hval : ((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card ≤
        padicValNat p (n.choose k) := by
      rw [padicValNat_choose (p := p) hkle hlog]
      have hsub : (Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i) ⊆
          (Finset.Ico 1 (n + r + 1)).filter
            (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i) := by
        intro i hi
        have hcar := hcarries i hi
        simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
        refine ⟨⟨hi.1.1, ?_⟩, hcar⟩
        omega
      exact Finset.card_le_card hsub
    have hdiv : p ^ ((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card ∣
        n.choose k :=
      (padicValNat_dvd_iff_le (Nat.choose_ne_zero hkle)).mpr hval
    rw [ringChoose_nat]
    exact_mod_cast hdiv

/-- Identity `Q (C1 - C2) = C2 (P - Q)` and `p^r ∣ P - Q`, for `t < p^r`. -/
lemma binom_diff_identity {p r α β t M : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hM : 1 ≤ M) (hM2 : 2 * M < t) (htpr : t < p ^ r)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    let N : ℤ := ((p ^ r * β : ℕ) : ℤ) - t
    let K2 : ℕ := p ^ r * α - (t - M)
    let δ : ℕ := t - 2 * M
    let Qval : ℤ := ∏ j ∈ Finset.range δ, (K2 + j + 1 : ℤ)
    let Pval : ℤ := ∏ j ∈ Finset.range δ, (N - K2 - j)
    Qval * (Ring.choose N (p ^ r * α - M) - Ring.choose N K2) =
      Ring.choose N K2 * (Pval - Qval) ∧
    (p : ℤ) ^ r ∣ Pval - Qval ∧
    Qval = ∏ j ∈ Finset.range δ, ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ)) ∧
    Qval ≠ 0 := by
  have hp0 : 0 < p := hp.pos
  have hδpos : 0 < t - 2 * M := Nat.sub_pos_of_lt hM2
  have hMt : M < t := by omega
  have hs : t - M < t := Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le _) hMt) hM
  have hs0 : 0 < t - M := Nat.sub_pos_of_lt hMt
  set N : ℤ := ((p ^ r * β : ℕ) : ℤ) - t
  set K2 : ℕ := p ^ r * α - (t - M)
  set δ : ℕ := t - 2 * M
  have hleK : t - M ≤ p ^ r * α := le_pow_mul_of_lt_pow hα (lt_trans hs htpr)
  have hleM : M ≤ p ^ r * α := le_pow_mul_of_lt_pow hα (lt_trans hMt htpr)
  have hKsum : K2 + δ = p ^ r * α - M := by
    have : p ^ r * α - (t - M) + (t - 2 * M) = p ^ r * α - M := by omega
    simpa [K2, δ] using this
  have hratio := ringChoose_ratio_prod N K2 δ
  rw [hKsum] at hratio
  set Qval : ℤ := ∏ j ∈ Finset.range δ, (K2 + j + 1 : ℤ)
  set Pval : ℤ := ∏ j ∈ Finset.range δ, (N - K2 - j)
  have hratio' : Ring.choose N (p ^ r * α - M) * Qval =
      Ring.choose N K2 * Pval := hratio
  have hk2Z : (K2 : ℤ) = (p ^ r * α : ℤ) - ↑(t - M) := by
    simpa [K2] using (Nat.cast_sub hleK)
  have hidx : ∀ j ∈ Finset.range δ,
      t - M - 1 - j = M + (δ - 1 - j) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    omega
  have hQfac : ∀ j ∈ Finset.range δ,
      (K2 + j + 1 : ℤ) = (p : ℤ) ^ r * (α : ℤ) - (M + (δ - 1 - j) : ℕ) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hcast : ((M + (δ - 1 - j) : ℕ) : ℤ) = (t : ℤ) - M - 1 - j := by
      have hid := hidx j (Finset.mem_range.mpr hj)
      have htriple : ((t - M - 1 - j : ℕ) : ℤ) = (t : ℤ) - M - 1 - j := by
        have htmj : M + 1 + j ≤ t := by omega
        rw [show t - M - 1 - j = t - (M + 1 + j) from by omega]
        rw [Nat.cast_sub htmj, Nat.cast_add, Nat.cast_add, Nat.cast_one]
        ring
      rw [← hid]; exact htriple
    rw [hk2Z, Nat.cast_sub (Nat.le_of_lt hMt), hcast]
    push_cast
    ring
  have hQval : Qval =
      ∏ j ∈ Finset.range δ, ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ)) := by
    unfold Qval
    have h1 : ∏ j ∈ Finset.range δ, (K2 + j + 1 : ℤ) =
        ∏ j ∈ Finset.range δ,
          ((p : ℤ) ^ r * (α : ℤ) - (M + (δ - 1 - j) : ℕ)) :=
      Finset.prod_congr rfl hQfac
    rw [h1]
    exact interval_prod_reindex M δ ((p : ℤ) ^ r * (α : ℤ))
  have hPfac : ∀ j ∈ Finset.range δ,
      (N - K2 - j : ℤ) = (p : ℤ) ^ r * ((β : ℤ) - α) - (M + j : ℕ) := by
    intro j _hj
    have : (N - K2 - j : ℤ) =
        ((p ^ r * β : ℕ) : ℤ) - t - ((p ^ r * α : ℤ) - ↑(t - M)) - j := by
      simp [N, hk2Z]
    rw [this, Nat.cast_sub (Nat.le_of_lt hMt)]
    push_cast
    ring
  have hPval : Pval =
      (intervalPoly M δ).eval ((p : ℤ) ^ r * ((β : ℤ) - α)) := by
    unfold Pval
    rw [intervalPoly_eval]
    exact Finset.prod_congr rfl hPfac
  have hQval' : Qval =
      (intervalPoly M δ).eval ((p : ℤ) ^ r * (α : ℤ)) := by
    rw [hQval, intervalPoly_eval]
  have hPQ : (p : ℤ) ^ r ∣ Pval - Qval := by
    rw [hPval, hQval']
    exact eval_scale_pow_sub_dvd (intervalPoly M δ) p r ((β : ℤ) - α) (α : ℤ) hr
  have hiden : Qval * (Ring.choose N (p ^ r * α - M) - Ring.choose N K2) =
      Ring.choose N K2 * (Pval - Qval) := by
    linarith [hratio']
  have hQne : Qval ≠ 0 := by
    rw [hQval]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    have ha : (M + j : ℕ) < p ^ r := by
      have : M + j < t := by omega
      exact lt_trans this htpr
    have hz : ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ)) =
        ((p ^ r * α - (M + j) : ℕ) : ℤ) := by
      have hle : M + j ≤ p ^ r * α := le_pow_mul_of_lt_pow hα ha
      rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_sub hle]
    rw [hz]
    exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le ha
      (Nat.le_mul_of_pos_right _ hα))).ne.symm
  exact ⟨hiden, hPQ, hQval, hQne⟩

lemma interval_prod_val_le {p r α M δ t : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hα : 1 ≤ α) (hM : 1 ≤ M) (hδ : 0 < δ) (htpr : t < p ^ r)
    (hmax : M + δ - 1 ≤ t - 2) :
    padicValInt p (∏ j ∈ Finset.range δ,
        ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ))) ≤
      padicValNat p (t - 2).factorial := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hf : ∀ j ∈ Finset.range δ,
      ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ)) ≠ 0 := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have ha : M + j < p ^ r := by
      have : M + j ≤ M + δ - 1 := by omega
      exact lt_of_le_of_lt (this.trans hmax) (lt_of_le_of_lt (Nat.sub_le _ _) htpr)
    have hz : ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ)) =
        ((p ^ r * α - (M + j) : ℕ) : ℤ) := by
      have hle : M + j ≤ p ^ r * α := le_pow_mul_of_lt_pow hα ha
      rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_sub hle]
    rw [hz]
    exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le ha
      (Nat.le_mul_of_pos_right _ hα))).ne.symm
  rw [padicValInt_prod _ _ hf]
  have hterm : ∀ j ∈ Finset.range δ,
      padicValInt p ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ)) =
        padicValNat p (M + j) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have ha0 : 0 < M + j := Nat.add_pos_left hM j
    have ha : M + j < p ^ r := by
      have : M + j ≤ M + δ - 1 := by omega
      exact lt_of_le_of_lt (this.trans hmax) (lt_of_le_of_lt (Nat.sub_le _ _) htpr)
    exact padicValInt_pow_mul_sub hp hr hα ha0 ha
  have hsum : ∑ j ∈ Finset.range δ,
      padicValInt p ((p : ℤ) ^ r * (α : ℤ) - (M + j : ℕ)) =
      ∑ j ∈ Finset.range δ, padicValNat p (M + j) :=
    Finset.sum_congr rfl hterm
  rw [hsum]
  have hmap : ∑ j ∈ Finset.range δ, padicValNat p (M + j) =
      ∑ a ∈ (Finset.range δ).image (fun j : ℕ => M + j), padicValNat p a := by
    refine (Finset.sum_image (g := fun j : ℕ => M + j)
      (fun x _hx y _hy hxy => Nat.add_left_cancel hxy)).symm
  rw [hmap]
  have hS : (Finset.range δ).image (fun j : ℕ => M + j) ⊆ Finset.Icc 1 (t - 2) := by
    intro a ha
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc] at ha ⊢
    obtain ⟨j, hj, rfl⟩ := ha
    constructor
    · omega
    · have : M + j ≤ M + δ - 1 := by omega
      exact this.trans hmax
  have hnonneg : ∀ a ∈ Finset.Icc 1 (t - 2), 0 ≤ padicValNat p a :=
    fun _ _ => Nat.zero_le _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun a _ _ => Nat.zero_le (padicValNat p a))
  have hfac : ∑ i ∈ Finset.Icc 1 (t - 2), padicValNat p i =
      padicValNat p (t - 2).factorial :=
    padicValNat_factorial_eq_sum.symm
  exact hle.trans hfac.le

lemma binom_diff_val_dvd {p r α β t M : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hM : 1 ≤ M) (hM2 : 2 * M < t) (htpr : t < p ^ r)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    (p : ℤ) ^
      (((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card + r
        - padicValNat p (t - 2).factorial) ∣
      Ring.choose (((p ^ r * β : ℕ) : ℤ) - t) (p ^ r * α - M) -
        Ring.choose (((p ^ r * β : ℕ) : ℤ) - t) (p ^ r * α - (t - M)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hiden, hPQ, hQval, hQne⟩ :=
    binom_diff_identity (p := p) (r := r) (α := α) (β := β) (t := t) (M := M)
      hp hr hM hM2 htpr hα hβ
  set N : ℤ := ((p ^ r * β : ℕ) : ℤ) - t
  set K2 : ℕ := p ^ r * α - (t - M)
  set δ : ℕ := t - 2 * M
  set Qval : ℤ := ∏ j ∈ Finset.range δ, (K2 + j + 1 : ℤ)
  set Pval : ℤ := ∏ j ∈ Finset.range δ, (N - K2 - j)
  set κ : ℕ := ((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card
  set vf : ℕ := padicValNat p (t - 2).factorial
  have hs0 : 0 < t - M := by omega
  have hs : t - M < t := by omega
  have hC2 : (p : ℤ) ^ κ ∣ Ring.choose N K2 := by
    simpa [N, K2, κ] using
      choose_pow_sub_val_dvd (p := p) (r := r) (α := α) (β := β) (t := t)
        (s := t - M) hp hr hs0 hs htpr hα hβ
  have hmul : (p : ℤ) ^ (κ + r) ∣
      Ring.choose N K2 * (Pval - Qval) := by
    rw [pow_add]
    exact mul_dvd_mul hC2 hPQ
  have hQmul : (p : ℤ) ^ (κ + r) ∣
      Qval * (Ring.choose N (p ^ r * α - M) - Ring.choose N K2) := by
    rwa [hiden]
  have hQle : padicValInt p Qval ≤ vf := by
    have hmax : M + δ - 1 ≤ t - 2 := by
      simp only [δ]; omega
    have hδpos : 0 < δ := Nat.sub_pos_of_lt hM2
    simpa [Qval, hQval, vf] using
      interval_prod_val_le (p := p) (r := r) (α := α) (M := M) (δ := δ) (t := t)
        hp hr hα hM hδpos htpr hmax
  -- p^{κ+r} | Q * (C1-C2). Cancel p^{v(Q)} ≤ vf.
  set diff : ℤ := Ring.choose N (p ^ r * α - M) - Ring.choose N K2
  change (p : ℤ) ^ (κ + r - vf) ∣ diff
  by_cases hdz : diff = 0
  · simp [hdz]
  · have hQd : (p : ℤ) ^ (κ + r) ∣ Qval * diff := hQmul
    have hvsum : κ + r ≤ padicValInt p (Qval * diff) := by
      have hne : Qval * diff ≠ 0 := mul_ne_zero hQne hdz
      have := (padicValInt_dvd_iff (κ + r) (Qval * diff)).mp hQd
      exact this.resolve_left hne
    have hvmul : padicValInt p (Qval * diff) =
        padicValInt p Qval + padicValInt p diff :=
      padicValInt.mul hQne hdz
    have : κ + r - vf ≤ padicValInt p diff := by
      have : padicValInt p Qval + padicValInt p diff ≥ κ + r := by
        rwa [← hvmul]
      omega
    exact (padicValInt_dvd_iff (κ + r - vf) diff).mpr (Or.inr this)

lemma eight_mul_le_pow_five {k : ℕ} (hk : 2 ≤ k) : 8 * k ≤ 5 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 8 * (k + 1) ≤ 5 * (8 * k) := by omega
    have : 5 * (8 * k) ≤ 5 * 5 ^ k := Nat.mul_le_mul_left 5 ih
    have : 5 * 5 ^ k = 5 ^ (k + 1) := by rw [mul_comm, pow_succ]
    omega

lemma padicValNat_lt_of_lt_pow {p n k : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (h : n < p ^ k) : padicValNat p n < k := by
  have hdiv : p ^ padicValNat p n ∣ n := pow_padicValNat_dvd
  have hle : p ^ padicValNat p n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
  exact (Nat.pow_lt_pow_iff_right (Fact.out : Nat.Prime p).one_lt).mp
    (lt_of_le_of_lt hle h)

/-- Numerical room for the middle-range valuation: `3(r+1) + v(t) + v((t-2)!) ≤ t + 2r + κ`. -/
lemma middle_val_enough {p r t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5)
    (hr : 2 ≤ r) (htp : p < t) (ht : t < 3 * (r + 1)) :
    3 * (r + 1) + padicValNat p t + padicValNat p (t - 2).factorial ≤
      t + 2 * r +
        ((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ht6 : 6 ≤ t := by omega
  have htpr : t < p ^ r := lt_of_lt_of_le ht (three_mul_succ_le_pow hp5 hr)
  set κ := ((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card
  set vt := padicValNat p t
  set vf := padicValNat p (t - 2).factorial
  have hr_mem : r ∈ (Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i) := by
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, Nat.le_of_lt htpr⟩
  have κpos : 1 ≤ κ := Finset.card_pos.mpr ⟨r, hr_mem⟩
  have hvt_le_log : vt ≤ Nat.log p t := padicValNat_le_nat_log t
  have hvf_bound : 4 * vf < t - 2 := by
    have ht2 : t - 2 ≠ 0 := by omega
    have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p ht2
    have hp4 : 4 ≤ p - 1 := by omega
    have : 4 * vf ≤ (p - 1) * vf := Nat.mul_le_mul_right vf hp4
    exact lt_of_le_of_lt this (by simpa [vf] using hlt)
  by_cases htp2 : t ≤ p ^ 2
  · -- i0 ≤ 2, so κ ≥ r - 1
    have h2mem : 2 ∈ (Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i) := by
      simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨by omega, by omega⟩, htp2⟩
    have hIco : Finset.Ico 2 (r + 1) ⊆
        (Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i) := by
      intro i hi
      simp only [Finset.mem_Ico, Finset.mem_filter] at hi ⊢
      refine ⟨⟨by omega, hi.2⟩, ?_⟩
      have : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
      exact htp2.trans this
    have κge : r - 1 ≤ κ := by
      have hcard : #(Finset.Ico 2 (r + 1)) = r - 1 := by
        rw [Nat.card_Ico]; omega
      have := Finset.card_le_card hIco
      rwa [hcard] at this
    -- Need 3r+3+vt+vf ≤ t+2r+κ, using κ ≥ r-1: enough that 4+vt+vf ≤ t
    have hneed : vt + vf + 4 ≤ t := by
      by_cases hlt2 : t < p ^ 2
      · have hvt1 : vt ≤ 1 := by
          have : vt < 2 := padicValNat_lt_of_lt_pow (by omega : t ≠ 0) hlt2
          omega
        by_cases hvf0 : vf = 0
        · omega
        · have hvfpos : 1 ≤ vf := Nat.pos_of_ne_zero hvf0
          -- 4 vf < t-2 ⇒ t ≥ 4 vf + 3 ≥ vf + 5 (since vf ≥ 1 ⇒ 3 vf ≥ 2)
          have : t ≥ 4 * vf + 3 := by omega
          have : 4 * vf + 3 ≥ vf + 5 := by nlinarith
          omega
      · have heq : t = p ^ 2 := le_antisymm htp2 (Nat.le_of_not_gt hlt2)
        have hvt2 : vt = 2 := by
          simp only [vt, heq]
          exact padicValNat.prime_pow 2
        -- vf < (t-2)/4, t = p^2 ≥ 25
        have hp25 : 25 ≤ t := by
          have : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
          omega
        omega
    omega
  · -- t > p^2 ≥ 25
    have ht25 : 25 ≤ t := by
      have : 5 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
      omega
    have hlog2 : 2 ≤ Nat.log p t := by
      have : p ^ 2 ≤ t := Nat.le_of_not_gt (fun h => htp2 (Nat.le_of_lt h))
      exact (Nat.le_log_iff_pow_le hp.one_lt (by omega)).mpr this
    have h8log : 8 * Nat.log p t ≤ t := by
      have : 8 * Nat.log p t ≤ 5 ^ Nat.log p t := eight_mul_le_pow_five hlog2
      have : 5 ^ Nat.log p t ≤ p ^ Nat.log p t :=
        Nat.pow_le_pow_left hp5 _
      have : p ^ Nat.log p t ≤ t := Nat.pow_log_le_self p (by omega : t ≠ 0)
      omega
    -- κ ≥ r - log p t  (i0 ≤ log+1, and log+1 ≤ r since t < p^r)
    have hlog_lt : Nat.log p t < r := by
      have : p ^ Nat.log p t ≤ t := Nat.pow_log_le_self p (by omega : t ≠ 0)
      have : p ^ Nat.log p t < p ^ r := lt_of_le_of_lt this htpr
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp this
    have hi0 : Nat.log p t + 1 ≤ r := by omega
    have hIco : Finset.Ico (Nat.log p t + 1) (r + 1) ⊆
        (Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i) := by
      intro i hi
      simp only [Finset.mem_Ico, Finset.mem_filter] at hi ⊢
      refine ⟨⟨by omega, hi.2⟩, ?_⟩
      have : t < p ^ (Nat.log p t + 1) := Nat.lt_pow_succ_log_self hp.one_lt t
      have : p ^ (Nat.log p t + 1) ≤ p ^ i :=
        Nat.pow_le_pow_right hp.pos (by omega)
      exact Nat.le_of_lt (lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt t) this)
    have κge : r - Nat.log p t ≤ κ := by
      have hcard : #(Finset.Ico (Nat.log p t + 1) (r + 1)) = r - Nat.log p t := by
        rw [Nat.card_Ico]; omega
      have := Finset.card_le_card hIco
      rwa [hcard] at this
    -- 3 + vt + vf + log ≤ t, using vt ≤ log, 2 log ≤ t/4, 4 vf < t-2
    have : 3 + vt + vf + Nat.log p t ≤ t := by
      have h2log : 2 * Nat.log p t ≤ t / 4 := by
        have : 8 * Nat.log p t ≤ t := h8log
        omega
      have hvf' : vf ≤ (t - 3) / 4 := by omega
      omega
    omega

lemma inner_sum_middle_dvd {p r α β t : ℕ} (hp : p.Prime) (hp5 : p ≥ 5)
    (hr : 0 < r) (ht3 : 3 ≤ t) (htpr : t < p ^ r)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    (p : ℤ) ^
      (((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card + r
        - padicValNat p (t - 2).factorial) ∣
      ∑ M ∈ Finset.range (p ^ r * α + 1),
        gPhiPowCoeff p t M *
          Ring.choose (((p ^ r * β : ℕ) : ℤ) - t) (p ^ r * α - M) := by
  have ht : 1 ≤ t := by omega
  have hA : t - 1 ≤ p ^ r * α := by
    have : t - 1 < p ^ r := lt_of_le_of_lt (Nat.sub_le _ _) htpr
    exact le_pow_mul_of_lt_pow hα this
  rw [inner_sum_pair (((p ^ r * β : ℕ) : ℤ)) hp hp5 ht hA]
  refine Finset.dvd_sum fun M hM => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hM
  exact dvd_mul_of_dvd_right
    (binom_diff_val_dvd hp hr hM.1.1 hM.2 htpr hα hβ) _

/-- The two-variable lift for nonnegative upper index, `k = r+1 ≥ 2`. -/
lemma U_mul_p_pow_mod (p A B r : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * (r + 1)) ∣
      U (p * (p ^ r * A)) ((p * (p ^ r * B) : ℕ) : ℤ) -
        U (p ^ r * A) ((p ^ r * B : ℕ) : ℤ) := by
  by_cases hA0 : A = 0
  · subst hA0
    -- U(0, _) = 1
    have hU0 : ∀ C : ℤ, U 0 C = 1 := by
      intro C; simp [U, gCoeff]
    simp [hU0]
  by_cases hB0 : B = 0
  · subst hB0
    have hApos : 0 < A := Nat.pos_of_ne_zero hA0
    have hpos1 : 0 < p * (p ^ r * A) :=
      Nat.mul_pos hp.pos (Nat.mul_pos (pow_pos hp.pos r) hApos)
    have hpos2 : 0 < p ^ r * A := Nat.mul_pos (pow_pos hp.pos r) hApos
    simp only [mul_zero, Nat.cast_zero]
    rw [U_zero_right hpos1, U_zero_right hpos2, gCoeff_pow_mul hp hp5]
    simp
  -- A ≥ 1, B ≥ 1
  have hApos : 1 ≤ A := Nat.pos_of_ne_zero hA0
  have hBpos : 1 ≤ B := Nat.pos_of_ne_zero hB0
  set A' : ℕ := p ^ r * A
  set B' : ℕ := p ^ r * B
  have hexp := U_mul_p_expand p A' B' hp hp5
  have h0 :
      (p : ℤ) ^ 0 * (B'.choose 0 : ℤ) *
        ∑ M ∈ Finset.range (A' + 1),
          gPhiPowCoeff p 0 M * Ring.choose ((B' : ℤ) - 0) (A' - M) =
        U A' B' := by
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul,
      gPhiPowCoeff_zero_left, sub_zero]
    rfl
  have hsplit :
      ∑ t ∈ Finset.range (B' + 1),
          (p : ℤ) ^ t * (B'.choose t : ℤ) *
            ∑ M ∈ Finset.range (A' + 1),
              gPhiPowCoeff p t M * Ring.choose ((B' : ℤ) - t) (A' - M) =
        U A' B' +
          ∑ t ∈ Finset.Icc 1 B',
            (p : ℤ) ^ t * (B'.choose t : ℤ) *
              ∑ M ∈ Finset.range (A' + 1),
                gPhiPowCoeff p t M * Ring.choose ((B' : ℤ) - t) (A' - M) := by
    have hrng : Finset.range (B' + 1) = insert 0 (Finset.Icc 1 B') := by
      ext t; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    have h0i : (0 : ℕ) ∉ Finset.Icc 1 B' := by simp
    rw [hrng, Finset.sum_insert h0i]
    simpa using h0
  rw [hexp, hsplit, add_sub_cancel_left]
  refine Finset.dvd_sum fun t ht => ?_
  simp only [Finset.mem_Icc] at ht
  by_cases ht12 : t = 1 ∨ t = 2
  · rw [inner_sum_t_le_two (B := B') hp hp5 ht12]
    simp
  · have ht3 : 3 ≤ t := by omega
    by_cases htbig : 3 * (r + 1) ≤ t
    · have hpow : (p : ℤ) ^ (3 * (r + 1)) ∣ (p : ℤ) ^ t :=
        pow_dvd_pow (p : ℤ) htbig
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpow _) _
    · have htlt : t < 3 * (r + 1) := Nat.lt_of_not_ge htbig
      by_cases htp : t ≤ p
      · -- 3 ≤ t ≤ p: pairing gives p^{2r}
        have hS : (p : ℤ) ^ (2 * r) ∣
            ∑ M ∈ Finset.range (A' + 1),
              gPhiPowCoeff p t M * Ring.choose ((B' : ℤ) - t) (A' - M) := by
          simpa [A', B'] using
            inner_sum_pow_dvd (p := p) (r := r) (α := A) (β := B) (t := t)
              hp hp5 (by omega) ht3 htp hApos hBpos
        by_cases htp' : t < p
        · have hch : (p : ℤ) ^ r ∣ (B'.choose t : ℤ) := by
            have h := choose_scale_pow_dvd (B := B) (t := t) hp
              (by omega : 0 < r) (by omega : 0 < t) htp'
            rw [ringChoose_nat] at h
            simpa [B'] using h
          have hneed : 3 * (r + 1) ≤ t + r + 2 * r := by omega
          have hcomb : (p : ℤ) ^ (t + r + 2 * r) ∣
              (p : ℤ) ^ t * (B'.choose t : ℤ) *
                ∑ M ∈ Finset.range (A' + 1),
                  gPhiPowCoeff p t M * Ring.choose ((B' : ℤ) - t) (A' - M) := by
            have h1 : (p : ℤ) ^ (t + r) ∣ (p : ℤ) ^ t * (B'.choose t : ℤ) := by
              rw [pow_add]
              exact mul_dvd_mul_left _ hch
            have : (p : ℤ) ^ (t + r + 2 * r) =
                (p : ℤ) ^ (t + r) * (p : ℤ) ^ (2 * r) := by rw [pow_add]
            rw [this]
            exact mul_dvd_mul h1 hS
          exact dvd_trans (pow_dvd_pow (p : ℤ) hneed) hcomb
        · -- t = p: choose contributes p^{r-1}
          have hteq : t = p := le_antisymm htp (Nat.le_of_not_gt htp')
          have hch : (p : ℤ) ^ (r - 1) ∣ (B'.choose t : ℤ) := by
            have h := choose_scale_self_dvd (B := B) hp hr
            rw [ringChoose_nat] at h
            simpa [B', hteq] using h
          have hneed : 3 * (r + 1) ≤ t + (r - 1) + 2 * r := by
            have hp5' : 5 ≤ p := hp5
            omega
          have hcomb : (p : ℤ) ^ (t + (r - 1) + 2 * r) ∣
              (p : ℤ) ^ t * (B'.choose t : ℤ) *
                ∑ M ∈ Finset.range (A' + 1),
                  gPhiPowCoeff p t M * Ring.choose ((B' : ℤ) - t) (A' - M) := by
            have h1 : (p : ℤ) ^ (t + (r - 1)) ∣ (p : ℤ) ^ t * (B'.choose t : ℤ) := by
              rw [pow_add]
              exact mul_dvd_mul_left _ hch
            have : (p : ℤ) ^ (t + (r - 1) + 2 * r) =
                (p : ℤ) ^ (t + (r - 1)) * (p : ℤ) ^ (2 * r) := by rw [pow_add]
            rw [this]
            exact mul_dvd_mul h1 hS
          exact dvd_trans (pow_dvd_pow (p : ℤ) hneed) hcomb
      · -- middle range p < t < 3(r+1): pairing + scaled choose valuation
        have hr2 : 2 ≤ r := by
          by_contra h
          omega
        have htp' : p < t := Nat.lt_of_not_ge htp
        have htpr : t < p ^ r :=
          lt_of_lt_of_le htlt (three_mul_succ_le_pow hp5 hr2)
        have hS :=
          inner_sum_middle_dvd (p := p) (r := r) (α := A) (β := B) (t := t)
            hp hp5 (by omega) ht3 htpr hApos hBpos
        have hch :=
          choose_scale_val_dvd (B := B) (t := t) hp (by omega : 0 < r)
            (by omega : 0 < t) htpr
        set κ : ℕ :=
          ((Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i)).card
        set vt : ℕ := padicValNat p t
        set vf : ℕ := padicValNat p (t - 2).factorial
        have hnum := middle_val_enough hp hp5 hr2 htp' htlt
        haveI : Fact p.Prime := ⟨hp⟩
        have hvt_le : vt ≤ r := by
          have : vt < r := padicValNat_lt_of_lt_pow (by omega : t ≠ 0) htpr
          omega
        have hvf_le : vf ≤ κ + r := by
          have ht2 : t - 2 ≠ 0 := by omega
          have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p ht2
          have hp4 : 4 ≤ p - 1 := by omega
          have hvf4 : 4 * vf ≤ (p - 1) * vf := Nat.mul_le_mul_right vf hp4
          have hvf_bound : 4 * vf < t - 2 :=
            lt_of_le_of_lt hvf4 (by simpa [vf] using hlt)
          have hr_mem : r ∈ (Finset.Ico 1 (r + 1)).filter (fun i => t ≤ p ^ i) := by
            simp only [Finset.mem_filter, Finset.mem_Ico]
            exact ⟨⟨by omega, by omega⟩, Nat.le_of_lt htpr⟩
          have κpos : 1 ≤ κ := Finset.card_pos.mpr ⟨r, hr_mem⟩
          omega
        have hneed : 3 * (r + 1) ≤ t + (r - vt) + (κ + r - vf) := by
          omega
        have hch' : (p : ℤ) ^ (r - vt) ∣ (B'.choose t : ℤ) := by
          rw [ringChoose_nat] at hch
          simpa [B', vt] using hch
        have hS' : (p : ℤ) ^ (κ + r - vf) ∣
            ∑ M ∈ Finset.range (A' + 1),
              gPhiPowCoeff p t M * Ring.choose ((B' : ℤ) - t) (A' - M) := by
          simpa [A', B', κ, vf] using hS
        have h1 : (p : ℤ) ^ (t + (r - vt)) ∣ (p : ℤ) ^ t * (B'.choose t : ℤ) := by
          rw [pow_add]
          exact mul_dvd_mul_left _ hch'
        have hcomb : (p : ℤ) ^ (t + (r - vt) + (κ + r - vf)) ∣
            (p : ℤ) ^ t * (B'.choose t : ℤ) *
              ∑ M ∈ Finset.range (A' + 1),
                gPhiPowCoeff p t M * Ring.choose ((B' : ℤ) - t) (A' - M) := by
          have hpow : (p : ℤ) ^ (t + (r - vt) + (κ + r - vf)) =
              (p : ℤ) ^ (t + (r - vt)) * (p : ℤ) ^ (κ + r - vf) := by
            rw [pow_add]
          rw [hpow]
          exact mul_dvd_mul h1 hS'
        exact dvd_trans (pow_dvd_pow (p : ℤ) hneed) hcomb

/-- Integer upper-index form of the two-variable lift. -/
lemma U_mul_p_pow_mod_int (p A r : ℕ) (B : ℤ) (hp : p.Prime) (hp5 : p ≥ 5)
    (hr : 1 ≤ r) :
    (p : ℤ) ^ (3 * (r + 1)) ∣
      U (p * (p ^ r * A)) ((p : ℤ) ^ (r + 1) * B) -
        U (p ^ r * A) ((p : ℤ) ^ r * B) := by
  set f : ℕ → ℤ := fun n =>
    U (p * (p ^ r * A)) ((p : ℤ) ^ (r + 1) * n) -
      U (p ^ r * A) ((p : ℤ) ^ r * n)
  set P : Polynomial ℚ :=
    Upoly_scale_pow (p ^ (r + 1)) A - Upoly_scale_pow (p ^ r) A
  have hPdeg : P.natDegree ≤ p ^ (r + 1) * A := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (sup_le (Upoly_scale_pow_natDegree_le (p ^ (r + 1)) A)
        ((Upoly_scale_pow_natDegree_le (p ^ r) A).trans
          (Nat.mul_le_mul_right A (Nat.pow_le_pow_right hp.pos (Nat.le_succ r)))))
  have hPeval : ∀ n : ℕ, P.eval (n : ℚ) = Int.cast (f n) := by
    intro n
    rw [Polynomial.eval_sub]
    have hnQ : (n : ℚ) = ((n : ℤ) : ℚ) := (Int.cast_natCast (R := ℚ) n).symm
    rw [hnQ]
    have hs1 := Upoly_scale_pow_eval (p ^ (r + 1)) A (n : ℤ)
    have hs2 := Upoly_scale_pow_eval (p ^ r) A (n : ℤ)
    have hpow1 : ((p ^ (r + 1) : ℕ) : ℤ) * (n : ℤ) = (p : ℤ) ^ (r + 1) * n := by
      simp
    have hpow2 : ((p ^ r : ℕ) : ℤ) * (n : ℤ) = (p : ℤ) ^ r * n := by simp
    have hA1 : p ^ (r + 1) * A = p * (p ^ r * A) := by
      rw [pow_succ, mul_comm (p ^ r), mul_assoc]
    rw [hs1, hs2, hpow1, hpow2, hA1, Int.cast_sub]
  have hf : ∀ n : ℕ, (p : ℤ) ^ (3 * (r + 1)) ∣ f n := by
    intro n
    have h := U_mul_p_pow_mod p A n r hp hp5 hr
    have hcast : ((p * (p ^ r * n) : ℕ) : ℤ) = (p : ℤ) ^ (r + 1) * n := by
      simp [pow_succ, mul_assoc, mul_left_comm]
    have hcast2 : ((p ^ r * n : ℕ) : ℤ) = (p : ℤ) ^ r * n := by simp
    simpa [f, hcast, hcast2] using h
  obtain ⟨z, hz, hzdvd⟩ :=
    mahler_extension f (p ^ (r + 1) * A) ((p : ℤ) ^ (3 * (r + 1))) P
      hPdeg hPeval hf B
  have hPB : P.eval (B : ℚ) =
      Int.cast (U (p * (p ^ r * A)) ((p : ℤ) ^ (r + 1) * B) -
        U (p ^ r * A) ((p : ℤ) ^ r * B)) := by
    rw [Polynomial.eval_sub]
    have hs1 := Upoly_scale_pow_eval (p ^ (r + 1)) A B
    have hs2 := Upoly_scale_pow_eval (p ^ r) A B
    have hA1 : p ^ (r + 1) * A = p * (p ^ r * A) := by
      rw [pow_succ, mul_comm (p ^ r), mul_assoc]
    have h1 : ((p ^ (r + 1) : ℕ) : ℤ) * B = (p : ℤ) ^ (r + 1) * B := by simp
    have h2 : ((p ^ r : ℕ) : ℤ) * B = (p : ℤ) ^ r * B := by simp
    rw [hs1, hs2, hA1, h1, h2, Int.cast_sub]
  have hzeq : U (p * (p ^ r * A)) ((p : ℤ) ^ (r + 1) * B) -
      U (p ^ r * A) ((p : ℤ) ^ r * B) = z := by
    apply Int.cast_injective (α := ℚ)
    rw [← hPB, hz]
  rwa [hzeq]

lemma aTrue_mul_p_pow (m : ℤ) (p n k : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (hk : 2 ≤ k) :
    aTrue m (n * p ^ k) ≡ aTrue m (n * p ^ (k - 1))
      [ZMOD (p : ℤ) ^ (3 * k)] := by
  rw [aTrue_eq_U, aTrue_eq_U]
  have hr : 1 ≤ k - 1 := by omega
  have h := U_mul_p_pow_mod_int p n (k - 1) (n * (m + 2)) hp hp5 hr
  have hA : n * p ^ k = p * (p ^ (k - 1) * n) := by
    calc
      n * p ^ k = p ^ k * n := Nat.mul_comm _ _
      _ = p ^ ((k - 1) + 1) * n := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
      _ = (p ^ (k - 1) * p) * n := by rw [pow_succ]
      _ = p * (p ^ (k - 1) * n) := by ring
  have hmod : (p : ℤ) ^ (3 * k) = (p : ℤ) ^ (3 * (k - 1 + 1)) := by
    congr 1; omega
  rw [hA, hmod]
  rw [Int.modEq_iff_dvd, ← dvd_neg, neg_sub]
  convert h using 2
  · rw [pow_succ]
    push_cast; ring
  · push_cast; ring

/--
Conjecture on OEIS A333096:
More generally, for each integer $m$, we conjecture that the sequence
$a_m(n) := \text{the } n\text{-th order Taylor polynomial of } c(x)^{m \cdot n} \text{ evaluated at } x = 1$
satisfies the supercongruences $a_m(n \cdot p^k) \equiv a_m(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333096_supercongruence_conjecture (m : ℤ) (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (n k : ℕ) (hn : n > 0) (hk : k > 0) :
    a_gen m (n * p ^ k) ≡ a_gen m (n * p ^ (k - 1)) [ZMOD (p ^ (3 * k) : ℤ)] := by
  by_cases hk1 : k = 1
  · subst hk1
    have hpow : (p ^ (3 * 1) : ℤ) = (p : ℤ) ^ 3 := by norm_num
    rw [hpow, pow_one, pow_zero, mul_one]
    refine a_gen_congr_of_aTrue (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hn) hp.ne_zero)
      (Nat.pos_iff_ne_zero.mp hn) ?_
    exact aTrue_mul_p m p n hp hp5
  · have hk2 : 2 ≤ k := by omega
    have hpow : (p ^ (3 * k) : ℤ) = (p : ℤ) ^ (3 * k) := by
      simp
    rw [hpow]
    refine a_gen_congr_of_aTrue
      (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hn)
        (pow_ne_zero k hp.ne_zero))
      (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hn)
        (pow_ne_zero (k - 1) hp.ne_zero)) ?_
    exact aTrue_mul_p_pow m p n k hp hp5 hk2
