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

/-! ### Auxiliary definitions and lemmas for the proof -/

/-- The numerator `A092287(m) = ∏_{j,k=1}^m gcd(j,k)`. -/
def numer (m : ℕ) : ℕ := (Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k
/-- The denominator `A129364(m) = ∏_{k=1}^m (⌊m/k⌋!)^k`. -/
def denom (m : ℕ) : ℕ := (Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k

lemma count_mult (m d : ℕ) :
    (∑ j ∈ Icc 1 m, (if d ∣ j then 1 else 0)) = m / d := by
  rw [Finset.sum_boole]
  rw [show Icc 1 m = Ioc 0 m by ext x; simp [Nat.lt_iff_add_one_le]]
  exact_mod_cast Nat.Ioc_filter_dvd_card_eq_div m d

-- factorization of a positive nat as sum of indicators
lemma factorization_as_sum (q n b : ℕ) (hq : q.Prime) (hn : 0 < n) (hb : n < q ^ b) :
    n.factorization q = ∑ i ∈ Ico 1 b, (if q ^ i ∣ n then 1 else 0) := by
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hq hn hb, Finset.card_filter]

lemma numer_factorization (q m b : ℕ) (hq : q.Prime) (hb : m < q ^ b) :
    (numer m).factorization q = ∑ i ∈ Ico 1 b, (m / q ^ i) ^ 2 := by
  unfold numer
  rw [Nat.factorization_prod_apply (by
    intro j hj
    simp only [mem_Icc] at hj
    exact Finset.prod_ne_zero_iff.mpr (fun k hk => by
      simp only [mem_Icc] at hk; exact Nat.gcd_ne_zero_right (by omega)))]
  have inner : ∀ j ∈ Icc 1 m,
      ((Icc 1 m).prod fun k => Nat.gcd j k).factorization q
        = ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization q := by
    intro j hj
    rw [Nat.factorization_prod_apply]
    intro k hk
    simp only [mem_Icc] at hk hj
    exact Nat.gcd_ne_zero_right (by omega)
  rw [Finset.sum_congr rfl inner]
  -- rewrite each factorization as product-indicator sum over Ico 1 b
  have step : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m,
      (Nat.gcd j k).factorization q
        = ∑ i ∈ Ico 1 b, ((if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0)) := by
    intro j hj k hk
    simp only [mem_Icc] at hj hk
    rw [factorization_as_sum q _ b hq
      (Nat.gcd_pos_of_pos_left _ (by omega))
      (by calc Nat.gcd j k ≤ j := Nat.gcd_le_left _ (by omega)
            _ ≤ m := by omega
            _ < q ^ b := hb)]
    apply Finset.sum_congr rfl
    intro i hi
    have hiff : (q ^ i ∣ Nat.gcd j k) ↔ (q ^ i ∣ j ∧ q ^ i ∣ k) := Nat.dvd_gcd_iff
    by_cases h1 : q ^ i ∣ j <;> by_cases h2 : q ^ i ∣ k <;> simp [hiff, h1, h2]
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => step j hj k hk))]
  -- swap sums: bring i outermost
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  -- now ∑ i ∑ j ∑ k, indj * indk = ∑ i (∑ j indj)*(∑ k indk)
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul_sum]
  simp only [count_mult]
  rw [sq]

-- g N = ∑ k in [1,N] k*(N/k)
def gg (N : ℕ) : ℕ := ∑ k ∈ Icc 1 N, k * (N / k)

lemma gg_le_sq (N : ℕ) : gg N ≤ N ^ 2 := by
  unfold gg
  calc ∑ k ∈ Icc 1 N, k * (N / k) ≤ ∑ k ∈ Icc 1 N, N := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Nat.mul_comm]; exact Nat.div_mul_le_self N k
    _ = N ^ 2 := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
        simp [sq]

lemma denom_factorization (q m b : ℕ) (hq : q.Prime) (hb0 : b ≠ 0) (hb : m < q ^ b) :
    (denom m).factorization q = ∑ i ∈ Ico 1 b, gg (m / q ^ i) := by
  unfold denom
  rw [Nat.factorization_prod_apply (by
    intro k hk; exact pow_ne_zero _ (Nat.factorial_ne_zero _))]
  -- each term: (( (m/k)! )^k).factorization q = k * ((m/k)!).factorization q
  have hterm : ∀ k ∈ Icc 1 m,
      (((m / k)!) ^ k).factorization q = k * (((m / k)!).factorization q) := by
    intro k hk
    rw [Nat.factorization_pow]
    simp [Finsupp.smul_apply]
  rw [Finset.sum_congr rfl hterm]
  -- Legendre on each factorial
  have hleg : ∀ k ∈ Icc 1 m,
      k * (((m / k)!).factorization q) = ∑ i ∈ Ico 1 b, k * ((m / k) / q ^ i) := by
    intro k hk
    rw [Nat.factorization_factorial hq
      (Nat.log_lt_of_lt_pow' hb0 (lt_of_le_of_lt (Nat.div_le_self m k) hb))]
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hleg]
  -- swap
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  -- ∑ k ∈ Icc 1 m, k * ((m/k)/q^i) = gg (m/q^i)
  have hrw : ∀ k, (m / k) / q ^ i = (m / q ^ i) / k := by
    intro k
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp only [hrw]
  unfold gg
  -- trim from Icc 1 m to Icc 1 (m/q^i)
  symm
  apply Finset.sum_subset
  · apply Finset.Icc_subset_Icc_right
    exact Nat.div_le_self m (q ^ i)
  · intro k hk hknot
    simp only [mem_Icc] at hk hknot
    have : m / q ^ i < k := by omega
    rw [Nat.div_eq_zero_iff.mpr (Or.inr this)] at *
    simp

lemma numer_ne_zero (m : ℕ) : numer m ≠ 0 := by
  unfold numer
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [mem_Icc] at hj hk
  exact Nat.gcd_ne_zero_right (by omega)

lemma denom_ne_zero (m : ℕ) : denom m ≠ 0 := by
  unfold denom
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact pow_ne_zero _ (Nat.factorial_ne_zero _)

lemma denom_dvd_numer (m : ℕ) : denom m ∣ numer m := by
  rw [← Nat.factorization_le_iff_dvd (denom_ne_zero m) (numer_ne_zero m)]
  rw [Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  · have hb : m < q ^ (m + 1) := by
      calc m < 2 ^ m := Nat.lt_two_pow_self
        _ ≤ q ^ m := Nat.pow_le_pow_left hq.two_le m
        _ ≤ q ^ (m + 1) := Nat.pow_le_pow_right hq.pos (by omega)
    rw [denom_factorization q m (m + 1) hq (by omega) hb,
        numer_factorization q m (m + 1) hq hb]
    apply Finset.sum_le_sum
    intro i _
    exact gg_le_sq _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
    exact Nat.zero_le _

-- floor invariance: for i ≥ 1, k < p
lemma floor_inv (n p k i : ℕ) (hk : k < p) (hi : 1 ≤ i) :
    (n * p + k) / p ^ i = (n * p) / p ^ i := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hp : 0 < p := by omega
  rw [pow_succ, mul_comm (p ^ i') p, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [show n * p + k = k + n * p by ring, Nat.add_mul_div_right k n hp,
      Nat.div_eq_of_lt hk, Nat.zero_add, Nat.mul_div_cancel n hp]

lemma bound_np (n p k : ℕ) (hp : p.Prime) (hk : k < p) :
    n * p + k < p ^ (n * p + p) := by
  have h1 : n * p + k < n * p + p := by omega
  have h2 : n * p + p < 2 ^ (n * p + p) := Nat.lt_two_pow_self
  have h3 : 2 ^ (n * p + p) ≤ p ^ (n * p + p) := Nat.pow_le_pow_left hp.two_le _
  omega

lemma numer_fact_eq (n p k : ℕ) (hp : p.Prime) (hk : k < p) :
    (numer (n * p + k)).factorization p = (numer (n * p)).factorization p := by
  have hbA : n * p + k < p ^ (n * p + p) := bound_np n p k hp hk
  have hbB : n * p < p ^ (n * p + p) := by
    have := bound_np n p 0 hp hp.pos; omega
  rw [numer_factorization p _ (n * p + p) hp hbA,
      numer_factorization p _ (n * p + p) hp hbB]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mem_Ico] at hi
  rw [floor_inv n p k i hk hi.1]

lemma denom_fact_eq (n p k : ℕ) (hp : p.Prime) (hk : k < p) :
    (denom (n * p + k)).factorization p = (denom (n * p)).factorization p := by
  have hb0 : n * p + p ≠ 0 := by have := hp.pos; positivity
  have hbA : n * p + k < p ^ (n * p + p) := bound_np n p k hp hk
  have hbB : n * p < p ^ (n * p + p) := by
    have := bound_np n p 0 hp hp.pos; omega
  rw [denom_factorization p _ (n * p + p) hp hb0 hbA,
      denom_factorization p _ (n * p + p) hp hb0 hbB]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mem_Ico] at hi
  rw [floor_inv n p k i hk hi.1]

lemma a_fact (m p : ℕ) :
    (numer m / denom m).factorization p
      = (numer m).factorization p - (denom m).factorization p := by
  rw [Nat.factorization_div (denom_dvd_numer m)]
  rfl


/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  show (numer (n * p) / denom (n * p)).factorization p
    = (numer (n * p + k) / denom (n * p + k)).factorization p
  rw [a_fact, a_fact, numer_fact_eq n p k hp hk, denom_fact_eq n p k hp hk]
