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

/-! ### Auxiliary lemmas -/

/-- Count of multiples of `q` in `[1,n]`. -/
private theorem count_mult (n q : ℕ) :
    (∑ j ∈ Icc 1 n, (if q ∣ j then (1 : ℕ) else 0)) = n / q := by
  rw [Finset.sum_boole, Nat.cast_id]
  have h : Icc 1 n = Ioc 0 n := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h]
  exact Nat.Ioc_filter_dvd_card_eq_div n q

/-- For a prime `p`, `n < p ^ (n+1)`. -/
private theorem npow_lt (n p : ℕ) (hp : p.Prime) : n < p ^ (n + 1) := by
  calc n < 2 ^ (n + 1) := by have := Nat.lt_two_pow_self (n := n + 1); omega
    _ ≤ p ^ (n + 1) := Nat.pow_le_pow_left hp.two_le _

/-- The `p`-adic valuation of the numerator `∏∏ gcd(j,k)`. -/
private theorem valN (n p : ℕ) (hp : p.Prime) :
    ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k).factorization p
      = ∑ i ∈ Ico 1 (n + 1), (n / p ^ i) * (n / p ^ i) := by
  have hgcd_pos : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 n, Nat.gcd j k ≠ 0 := by
    intro j hj k hk
    simp only [Finset.mem_Icc] at hj hk
    have : 0 < Nat.gcd j k := Nat.gcd_pos_of_pos_left _ (by omega)
    omega
  rw [Nat.factorization_prod_apply
    (fun j hj => Finset.prod_ne_zero_iff.mpr (fun k hk => hgcd_pos j hj k hk))]
  have step1 : ∀ j ∈ Icc 1 n, ((Icc 1 n).prod fun k => Nat.gcd j k).factorization p
      = ∑ k ∈ Icc 1 n, ∑ i ∈ Ico 1 (n + 1),
          (if p ^ i ∣ j then (1 : ℕ) else 0) * (if p ^ i ∣ k then 1 else 0) := by
    intro j hj
    rw [Nat.factorization_prod_apply (fun k hk => hgcd_pos j hj k hk)]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hgle : Nat.gcd j k ≤ n :=
      le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right j k)) (by omega)
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp
        (Nat.pos_of_ne_zero (hgcd_pos j hj k (by simp only [Finset.mem_Icc]; omega)))
        (lt_of_le_of_lt hgle (npow_lt n p hp))]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hP : p ^ i ∣ j <;> by_cases hQ : p ^ i ∣ k <;>
      simp [Nat.dvd_gcd_iff, hP, hQ]
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul_sum, count_mult]

/-- The `p`-adic valuation of the denominator `∏ (⌊n/k⌋!)^k`. -/
private theorem valD (n p : ℕ) (hp : p.Prime) :
    ((Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k).factorization p
      = ∑ i ∈ Ico 1 (n + 1), ∑ k ∈ Icc 1 n, k * ((n / p ^ i) / k) := by
  rw [Nat.factorization_prod_apply (fun k hk => pow_ne_zero k (Nat.factorial_ne_zero _))]
  have step : ∀ k ∈ Icc 1 n, (((n / k).factorial) ^ k).factorization p
      = ∑ i ∈ Ico 1 (n + 1), k * ((n / p ^ i) / k) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    have hlog : Nat.log p (n / k) < n + 1 := by
      calc Nat.log p (n / k) ≤ Nat.log p n := Nat.log_mono_right (Nat.div_le_self n k)
        _ < n + 1 := by
            rcases Nat.eq_zero_or_pos n with h | h
            · simp [h]
            · exact Nat.log_lt_of_lt_pow (by omega) (npow_lt n p hp)
    rw [Nat.factorization_factorial hp hlog, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k (p ^ i)]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]

/-- Shrinking the range of a `∑ k, k * (m/k)` sum: terms with `k > m` vanish. -/
private theorem sum_shrink (m n : ℕ) (hmn : m ≤ n) :
    (∑ k ∈ Icc 1 n, k * (m / k)) = ∑ k ∈ Icc 1 m, k * (m / k) := by
  refine (Finset.sum_subset (fun x hx => ?_) (fun x hx hx2 => ?_)).symm
  · simp only [Finset.mem_Icc] at *; omega
  · simp only [Finset.mem_Icc] at hx hx2
    have : m / x = 0 := Nat.div_eq_of_lt (by omega)
    rw [this, Nat.mul_zero]

/-- `S(m) = ∑_{k=1}^m k⌊m/k⌋ ≤ m²`. -/
private theorem sumS_le (m : ℕ) : (∑ k ∈ Icc 1 m, k * (m / k)) ≤ m * m := by
  calc (∑ k ∈ Icc 1 m, k * (m / k)) ≤ ∑ k ∈ Icc 1 m, m := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Nat.mul_comm]
          exact Nat.div_mul_le_self m k
    _ = m * m := by rw [Finset.sum_const, Nat.card_Icc]; simp

/-- For `m ≤ 2`, `S(m) = m²`. -/
private theorem sumS_eq (m : ℕ) (hm : m ≤ 2) : (∑ k ∈ Icc 1 m, k * (m / k)) = m * m := by
  interval_cases m <;> decide

/-- For `m ≥ 3`, `S(m) < m²`, since the term `k = m-1` is `< m`. -/
private theorem sumS_lt (m : ℕ) (hm : 3 ≤ m) : (∑ k ∈ Icc 1 m, k * (m / k)) < m * m := by
  have key : (∑ k ∈ Icc 1 m, k * (m / k)) < ∑ k ∈ Icc 1 m, m := by
    apply Finset.sum_lt_sum
    · intro k hk
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self m k
    · refine ⟨m - 1, ?_, ?_⟩
      · simp only [Finset.mem_Icc]; omega
      · have h1 : m / (m - 1) = 1 := by rw [Nat.div_eq_of_lt_le] <;> omega
        rw [h1]; omega
  calc (∑ k ∈ Icc 1 m, k * (m / k)) < ∑ k ∈ Icc 1 m, m := key
    _ = m * m := by rw [Finset.sum_const, Nat.card_Icc]; simp

/-- `p ≤ n/3 ↔ 3 ≤ n/p`. -/
private theorem div3_iff (n p : ℕ) (hp : 0 < p) : p ≤ n / 3 ↔ 3 ≤ n / p := by
  rw [Nat.le_div_iff_mul_le (by norm_num), Nat.le_div_iff_mul_le hp]
  omega

/-- The core equivalence: `v_p(N) > v_p(D)` iff `p ≤ n/3`. -/
private theorem main_iff (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    (∑ i ∈ Ico 1 (n + 1), ∑ k ∈ Icc 1 n, k * ((n / p ^ i) / k))
        < (∑ i ∈ Ico 1 (n + 1), (n / p ^ i) * (n / p ^ i)) ↔ p ≤ n / 3 := by
  have hle : ∀ i ∈ Ico 1 (n + 1),
      (∑ k ∈ Icc 1 n, k * ((n / p ^ i) / k)) ≤ (n / p ^ i) * (n / p ^ i) := by
    intro i hi
    rw [sum_shrink (n / p ^ i) n (Nat.div_le_self n _)]
    exact sumS_le (n / p ^ i)
  constructor
  · intro hlt
    by_contra hcon
    rw [div3_iff n p hp.pos] at hcon
    push_neg at hcon
    have heq : ∀ i ∈ Ico 1 (n + 1),
        (∑ k ∈ Icc 1 n, k * ((n / p ^ i) / k)) = (n / p ^ i) * (n / p ^ i) := by
      intro i hi
      simp only [Finset.mem_Ico] at hi
      rw [sum_shrink (n / p ^ i) n (Nat.div_le_self n _)]
      apply sumS_eq
      calc n / p ^ i ≤ n / p := Nat.div_le_div_left (Nat.le_self_pow (by omega) p) hp.pos
        _ ≤ 2 := by omega
    rw [Finset.sum_congr rfl heq] at hlt
    exact lt_irrefl _ hlt
  · intro hle3
    rw [div3_iff n p hp.pos] at hle3
    apply Finset.sum_lt_sum hle
    refine ⟨1, ?_, ?_⟩
    · simp only [Finset.mem_Ico]; omega
    · rw [pow_one, sum_shrink (n / p) n (Nat.div_le_self n _)]
      exact sumS_lt (n / p) hle3

/--
oeis_a129365_conjecture_B: If p is a prime then p|a(n) if and only if p <= n/3.
Note: Since `a n` is non-zero for $n > 0$, $p \mid a n$ iff $p$ is in the factorization of $a n$.
-/
theorem oeis_a129365_conjecture_B (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) :
  p ∣ a n ↔ p ≤ n / 3 := by
  have hgcd : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 n, Nat.gcd j k ≠ 0 := by
    intro j hj k hk
    simp only [Finset.mem_Icc] at hj hk
    have : 0 < Nat.gcd j k := Nat.gcd_pos_of_pos_left _ (by omega)
    omega
  have hNpos : ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun j hj => Finset.prod_ne_zero_iff.mpr (fun k hk => hgcd j hj k hk))
  have hDpos : ((Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k hk => pow_ne_zero k (Nat.factorial_ne_zero _))
  -- The denominator divides the numerator.
  have hdvd : ((Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k)
      ∣ ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k) := by
    rw [← Nat.factorization_le_iff_dvd hDpos hNpos]
    intro q
    by_cases hq : q.Prime
    · rw [valN n q hq, valD n q hq]
      apply Finset.sum_le_sum
      intro i hi
      rw [sum_shrink (n / q ^ i) n (Nat.div_le_self n _)]
      exact sumS_le (n / q ^ i)
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
      exact Nat.zero_le _
  have haval : a n = ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k)
      / ((Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k) := rfl
  have hane : a n ≠ 0 := by
    rw [haval]
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hNpos) hdvd)
      (Nat.pos_of_ne_zero hDpos)
    omega
  -- `N = (a n) * D`, hence `v_p(N) = v_p(a n) + v_p(D)`.
  have hmul : ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k)
      = a n * ((Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k) := by
    rw [haval]; exact (Nat.div_mul_cancel hdvd).symm
  have hfact : ((Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k).factorization p
      = (a n).factorization p
        + ((Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k).factorization p := by
    rw [hmul, Nat.factorization_mul hane hDpos, Finsupp.add_apply]
  rw [valN n p hp, valD n p hp] at hfact
  rw [Nat.Prime.dvd_iff_one_le_factorization hp hane]
  rw [show (1 ≤ (a n).factorization p)
      ↔ (∑ i ∈ Ico 1 (n + 1), ∑ k ∈ Icc 1 n, k * ((n / p ^ i) / k))
          < (∑ i ∈ Ico 1 (n + 1), (n / p ^ i) * (n / p ^ i)) from by omega]
  exact main_iff n p hn hp
