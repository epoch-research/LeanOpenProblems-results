import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A129365: $a(n) = A092287(n)/A129364(n)$.
$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$
-/
def a (n : ℕ) : ℕ :=
  -- A092287(n) = Product Product gcd(j,k)
  let numerator : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
  -- A129364(n) = Product (floor(n/k)!)^k
  let denominator : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

  -- The conjecture guarantees that the division is exact.
  numerator / denominator

-- Helper function for A004125, b(n) = floor(n/2)
def b (n : ℕ) : ℕ := n / 2

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

namespace A129365Aux

/-- The numerator `A092287(m) = ∏_{j,k=1}^m gcd(j,k)`. -/
def N (m : ℕ) : ℕ := (Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k
/-- The denominator `A129364(m) = ∏_{k=1}^m (⌊m/k⌋!)^k`. -/
def D (m : ℕ) : ℕ := (Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k
/-- The pure "denominator term" function `G(M) = ∑_{k=1}^M k·⌊M/k⌋`. -/
def G (M : ℕ) : ℕ := ∑ k ∈ Icc 1 M, k * (M / k)

/-- The number of multiples of `d` in `[1,m]` is `⌊m/d⌋`. -/
theorem count_mult (m d : ℕ) : ∑ j ∈ Icc 1 m, (if d ∣ j then (1:ℕ) else 0) = m / d := by
  rw [Finset.sum_boole]
  have : (Icc 1 m) = Ioc 0 m := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [this]
  simpa using Nat.Ioc_filter_dvd_card_eq_div m d

/-- The `q`-adic valuation of any `j ∈ [1,m]` is at most `log_q m`. -/
theorem fact_bound (q j m : ℕ) (hq : q.Prime) (hj : j ≠ 0) (hjm : j ≤ m) :
    j.factorization q ≤ Nat.log q m := by
  rw [Nat.le_log_iff_pow_le hq.one_lt (by omega : m ≠ 0)]
  calc q ^ j.factorization q ≤ j := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd j q)
    _ ≤ m := hjm

/-- `∑_{i=1}^{B-1} [i ≤ M] = M` whenever `M < B`. -/
theorem sum_ind_le (B M : ℕ) (h : M < B) : ∑ i ∈ Ico 1 B, (if i ≤ M then (1:ℕ) else 0) = M := by
  rw [Finset.sum_boole]
  have : {i ∈ Ico 1 B | i ≤ M} = Ico 1 (M+1) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  rw [this]; simp [Nat.card_Ico]

/-- `min(v_q j, v_q k)` written as a sum of indicators over prime powers. -/
theorem min_val (q j k B : ℕ) (hq : q.Prime) (hj : j ≠ 0) (hk : k ≠ 0)
    (hjB : j.factorization q < B) (hkB : k.factorization q < B) :
    min (j.factorization q) (k.factorization q)
      = ∑ i ∈ Ico 1 B, (if q ^ i ∣ j then (1:ℕ) else 0) * (if q ^ i ∣ k then (1:ℕ) else 0) := by
  have hmin : min (j.factorization q) (k.factorization q) < B := by omega
  have step1 : ∑ i ∈ Ico 1 B, (if q ^ i ∣ j then (1:ℕ) else 0) * (if q ^ i ∣ k then (1:ℕ) else 0)
      = ∑ i ∈ Ico 1 B, (if i ≤ min (j.factorization q) (k.factorization q) then (1:ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hq.pow_dvd_iff_le_factorization hj, hq.pow_dvd_iff_le_factorization hk]
    by_cases h1 : i ≤ j.factorization q <;> by_cases h2 : i ≤ k.factorization q <;>
      simp [h1, h2]
  rw [step1, sum_ind_le B _ hmin]

/-- Legendre-type formula for the numerator: `v_q(N(m)) = ∑_{i=1}^{B-1} ⌊m/q^i⌋²`. -/
theorem numer_fact (q m B : ℕ) (hq : q.Prime) (hB : Nat.log q m < B) :
    (N m).factorization q = ∑ i ∈ Ico 1 B, (m / q ^ i) ^ 2 := by
  have hbnd : ∀ j ∈ Icc 1 m, j.factorization q < B := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact lt_of_le_of_lt (fact_bound q j m hq (by omega) hj.2) hB
  have h1 : (N m).factorization q
      = ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, min (j.factorization q) (k.factorization q) := by
    unfold N
    rw [Nat.factorization_prod_apply]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.factorization_prod_apply]
      · apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hj hk
        rw [Nat.factorization_gcd (by omega) (by omega)]
        rfl
      · intro k hk
        rw [Finset.mem_Icc] at hj hk
        exact Nat.gcd_ne_zero_left (by omega)
    · intro j hj
      rw [Finset.mem_Icc] at hj
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      rw [Finset.mem_Icc] at hk
      exact Nat.gcd_ne_zero_left (by omega)
  rw [h1]
  have h2 : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m,
      min (j.factorization q) (k.factorization q)
        = ∑ i ∈ Ico 1 B, (if q ^ i ∣ j then (1:ℕ) else 0) * (if q ^ i ∣ k then (1:ℕ) else 0) := by
    intro j hj k hk
    have hj' := Finset.mem_Icc.mp hj
    have hk' := Finset.mem_Icc.mp hk
    exact min_val q j k B hq (by omega) (by omega) (hbnd j hj) (hbnd k hk)
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => h2 j hj k hk))]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul_sum]
  rw [count_mult, sq]

/-- The tail terms `k > M` of `∑ k*(M/k)` vanish, giving the pure function `G`. -/
theorem G_reduce (M m : ℕ) (hMm : M ≤ m) : ∑ k ∈ Icc 1 m, k * (M / k) = G M := by
  symm
  unfold G
  apply Finset.sum_subset
  · intro x hx; rw [Finset.mem_Icc] at *; omega
  · intro x hx hxn
    rw [Finset.mem_Icc] at hx
    simp only [Finset.mem_Icc, not_and, not_le] at hxn
    have hxM : M < x := hxn (by omega)
    rw [Nat.div_eq_of_lt hxM, mul_zero]

/-- Legendre-type formula for the denominator: `v_q(D(m)) = ∑_{i=1}^{B-1} G(⌊m/q^i⌋)`. -/
theorem denom_fact (q m B : ℕ) (hq : q.Prime) (hB : Nat.log q m < B) :
    (D m).factorization q = ∑ i ∈ Ico 1 B, G (m / q ^ i) := by
  have h1 : (D m).factorization q
      = ∑ k ∈ Icc 1 m, ∑ i ∈ Ico 1 B, k * ((m / k) / q ^ i) := by
    unfold D
    rw [Nat.factorization_prod_apply]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Nat.factorization_pow]
      have hlog : Nat.log q (m / k) < B :=
        lt_of_le_of_lt (Nat.log_mono_right (Nat.div_le_self m k)) hB
      rw [Finsupp.smul_apply, Nat.factorization_factorial hq hlog, smul_eq_mul,
        Finset.mul_sum]
    · intro k hk
      exact pow_ne_zero _ (Nat.factorial_ne_zero _)
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hMm : m / q ^ i ≤ m := Nat.div_le_self m _
  rw [← G_reduce (m / q ^ i) m hMm]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- `G(M) ≤ M²`, the key inequality guaranteeing exact division. -/
theorem G_le (M : ℕ) : G M ≤ M ^ 2 := by
  unfold G
  calc ∑ k ∈ Icc 1 M, k * (M / k) ≤ ∑ k ∈ Icc 1 M, M := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self M k
    _ = M ^ 2 := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
        have : M + 1 - 1 = M := by omega
        rw [this, sq]

theorem N_ne_zero (m : ℕ) : N m ≠ 0 := by
  unfold N
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  rw [Finset.mem_Icc] at hj
  exact Nat.gcd_ne_zero_left (by omega)

theorem D_ne_zero (m : ℕ) : D m ≠ 0 := by
  unfold D
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact pow_ne_zero _ (Nat.factorial_ne_zero _)

/-- Exactness of the division: `D(m) ∣ N(m)`, since `v_q(D) ≤ v_q(N)` for every prime `q`. -/
theorem D_dvd_N (m : ℕ) : D m ∣ N m := by
  rw [← Nat.factorization_le_iff_dvd (D_ne_zero m) (N_ne_zero m)]
  rw [Finsupp.le_iff]
  intro p hp
  rw [Nat.support_factorization] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hlog : Nat.log p m < m + 1 := lt_of_le_of_lt (Nat.log_le_self p m) (by omega)
  rw [denom_fact p m (m+1) hpp hlog, numer_fact p m (m+1) hpp hlog]
  apply Finset.sum_le_sum
  intro i hi
  exact G_le (m / p ^ i)

/-- Consequence of exactness: `v_q(N) = v_q(N/D) + v_q(D)`. -/
theorem a_fact_p (q m : ℕ) :
    (N m / D m).factorization q + (D m).factorization q = (N m).factorization q := by
  have hdvd := D_dvd_N m
  have hcancel : N m / D m * D m = N m := Nat.div_mul_cancel hdvd
  have hq_ne : N m / D m ≠ 0 := by
    intro h; rw [h, Nat.zero_mul] at hcancel; exact N_ne_zero m hcancel.symm
  have : (N m).factorization = (N m / D m).factorization + (D m).factorization := by
    conv_lhs => rw [← hcancel]
    rw [Nat.factorization_mul hq_ne (D_ne_zero m)]
  rw [this, Finsupp.add_apply]

/-- Key invariance: for `i ≥ 1`, `⌊(np+k)/p^i⌋ = ⌊np/p^i⌋` when `k < p`. -/
theorem inv_div (n p k i : ℕ) (hk : k < p) (hi : 1 ≤ i) :
    (n * p + k) / p ^ i = (n * p) / p ^ i := by
  have hp0 : 0 < p := by omega
  rcases i with _ | j
  · omega
  · have e1 : (n * p + k) / p = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right k n hp0, Nat.div_eq_of_lt hk, Nat.zero_add]
    have e2 : (n * p) / p = n := Nat.mul_div_cancel n hp0
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e1, e2]

/-- The main invariance for `a`, phrased with `N`/`D`. -/
theorem final (n p k : ℕ) (hp : p.Prime) (hk : k < p) :
    (N (n * p) / D (n * p)).factorization p
      = (N (n * p + k) / D (n * p + k)).factorization p := by
  set B := n * p + k + 1 with hBdef
  have hl1 : Nat.log p (n * p) < B :=
    lt_of_le_of_lt (Nat.log_le_self p (n * p)) (by omega)
  have hl2 : Nat.log p (n * p + k) < B :=
    lt_of_le_of_lt (Nat.log_le_self p (n * p + k)) (by omega)
  have hN : (N (n * p)).factorization p = (N (n * p + k)).factorization p := by
    rw [numer_fact p (n * p) B hp hl1, numer_fact p (n * p + k) B hp hl2]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [inv_div n p k i hk hi.1]
  have hD : (D (n * p)).factorization p = (D (n * p + k)).factorization p := by
    rw [denom_fact p (n * p) B hp hl1, denom_fact p (n * p + k) B hp hl2]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [inv_div n p k i hk hi.1]
  have ea := a_fact_p p (n * p)
  have eb := a_fact_p p (n * p + k)
  omega

end A129365Aux

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  exact A129365Aux.final n p k hp hk
