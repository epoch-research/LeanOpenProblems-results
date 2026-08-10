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

namespace A129365

/-- The numerator A092287(n). -/
def num (n : ℕ) : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k

/-- The denominator A129364(n). -/
def den (n : ℕ) : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

/-- The contribution of one power of `p` to the valuation of the denominator,
as a function of `q = n / p^i`. -/
def S (q : ℕ) : ℕ := ∑ k ∈ Icc 1 q, k * (q / k)

lemma a_eq (n : ℕ) : a n = num n / den n := rfl

lemma num_ne_zero (n : ℕ) : num n ≠ 0 := by
  unfold num
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.prod_ne_zero_iff]
  intro k _
  exact (Nat.gcd_pos_of_pos_left k (mem_Icc.mp hj).1).ne'

lemma den_ne_zero (n : ℕ) : den n ≠ 0 := by
  unfold den
  rw [Finset.prod_ne_zero_iff]
  exact fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _)

lemma factorization_lt_of_lt_pow {p j B : ℕ} (hj : j ≠ 0) (h : j < p ^ B) :
    j.factorization p < B := by
  by_contra hcon
  push_neg at hcon
  have h1 : p ^ B ∣ j := dvd_trans (pow_dvd_pow p hcon) (Nat.ordProj_dvd j p)
  have h2 : p ^ B ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj) h1
  omega

lemma indicator_sum {B m : ℕ} (hm : m < B) :
    ∑ i ∈ Ico 1 B, (if i ≤ m then (1 : ℕ) else 0) = m := by
  rw [Finset.sum_boole, Nat.cast_id]
  have h : {i ∈ Ico 1 B | i ≤ m} = Icc 1 m := by
    ext i
    simp only [Finset.mem_filter, mem_Ico, mem_Icc]
    omega
  rw [h, Nat.card_Icc]
  omega

lemma min_eq_sum {B m₁ m₂ : ℕ} (h₁ : m₁ < B) :
    min m₁ m₂ = ∑ i ∈ Ico 1 B, (if i ≤ m₁ ∧ i ≤ m₂ then (1 : ℕ) else 0) := by
  have h : ∀ i : ℕ, (i ≤ m₁ ∧ i ≤ m₂) ↔ i ≤ min m₁ m₂ := fun i => (le_min_iff).symm
  simp only [h]
  exact (indicator_sum (lt_of_le_of_lt (min_le_left _ _) h₁)).symm

lemma ite_and_eq_mul (A B : Prop) [Decidable A] [Decidable B] :
    (if A ∧ B then (1 : ℕ) else 0)
      = (if A then (1 : ℕ) else 0) * (if B then (1 : ℕ) else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma count_dvd {p : ℕ} (hp : p.Prime) (n i : ℕ) :
    (∑ j ∈ Icc 1 n, if i ≤ j.factorization p then (1 : ℕ) else 0) = n / p ^ i := by
  have h : ∀ j ∈ Icc 1 n, (if i ≤ j.factorization p then (1 : ℕ) else 0)
      = if p ^ i ∣ j then 1 else 0 := by
    intro j hj
    have hj0 : j ≠ 0 := by
      have := (mem_Icc.mp hj).1; omega
    simp only [hp.pow_dvd_iff_le_factorization hj0]
  rw [Finset.sum_congr rfl h, Finset.sum_boole, Nat.cast_id]
  have h2 : Icc 1 n = Ioc 0 n := by
    ext j; simp only [mem_Icc, mem_Ioc]; omega
  rw [h2]
  exact Nat.Ioc_filter_dvd_card_eq_div n (p ^ i)

/-- The `p`-adic valuation of A092287(n): `∑_{i≥1} ⌊n/p^i⌋²`. -/
lemma num_factorization {p : ℕ} (hp : p.Prime) {n B : ℕ} (hn : n < p ^ B) :
    (num n).factorization p = ∑ i ∈ Ico 1 B, (n / p ^ i) ^ 2 := by
  have hne : ∀ j ∈ Icc 1 n, ((Icc 1 n).prod fun k => Nat.gcd j k) ≠ 0 := by
    intro j hj
    rw [Finset.prod_ne_zero_iff]
    intro k _
    exact (Nat.gcd_pos_of_pos_left k (mem_Icc.mp hj).1).ne'
  unfold num
  rw [Nat.factorization_prod hne, Finset.sum_apply']
  have hvlt : ∀ j ∈ Icc 1 n, j.factorization p < B := by
    intro j hj
    have h1 := (mem_Icc.mp hj).1
    have h2 := (mem_Icc.mp hj).2
    exact factorization_lt_of_lt_pow (by omega) (lt_of_le_of_lt h2 hn)
  have step1 : ∀ j ∈ Icc 1 n,
      ((Icc 1 n).prod fun k => Nat.gcd j k).factorization p
      = ∑ k ∈ Icc 1 n, min (j.factorization p) (k.factorization p) := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hgne : ∀ k ∈ Icc 1 n, Nat.gcd j k ≠ 0 := fun k _ =>
      (Nat.gcd_pos_of_pos_left k hj1).ne'
    rw [Nat.factorization_prod hgne, Finset.sum_apply']
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    rw [Nat.factorization_gcd (by omega) (by omega), Finsupp.inf_apply]
  rw [Finset.sum_congr rfl step1]
  calc
    ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, min (j.factorization p) (k.factorization p)
        = ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, ∑ i ∈ Ico 1 B,
            ((if i ≤ j.factorization p then (1 : ℕ) else 0)
              * (if i ≤ k.factorization p then (1 : ℕ) else 0)) := by
          refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
          rw [min_eq_sum (hvlt j hj)]
          exact Finset.sum_congr rfl fun i _ => ite_and_eq_mul _ _
    _ = ∑ i ∈ Ico 1 B, ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n,
            ((if i ≤ j.factorization p then (1 : ℕ) else 0)
              * (if i ≤ k.factorization p then (1 : ℕ) else 0)) := by
          rw [Finset.sum_congr rfl fun j (_ : j ∈ Icc 1 n) => Finset.sum_comm]
          exact Finset.sum_comm
    _ = ∑ i ∈ Ico 1 B,
          (∑ j ∈ Icc 1 n, if i ≤ j.factorization p then (1 : ℕ) else 0)
            * (∑ k ∈ Icc 1 n, if i ≤ k.factorization p then (1 : ℕ) else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul_sum]
    _ = ∑ i ∈ Ico 1 B, (n / p ^ i) * (n / p ^ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [count_dvd hp]
    _ = ∑ i ∈ Ico 1 B, (n / p ^ i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => (pow_two _).symm

/-- The `p`-adic valuation of A129364(n): `∑_{i≥1} S(⌊n/p^i⌋)`. -/
lemma den_factorization {p : ℕ} (hp : p.Prime) {n B : ℕ} (hn0 : 0 < n) (hn : n < p ^ B) :
    (den n).factorization p = ∑ i ∈ Ico 1 B, S (n / p ^ i) := by
  have hB0 : 0 < B := by
    rcases Nat.eq_zero_or_pos B with rfl | h
    · simp only [pow_zero] at hn; omega
    · exact h
  have hne : ∀ k ∈ Icc 1 n, (Nat.factorial (n / k)) ^ k ≠ 0 :=
    fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _)
  unfold den
  rw [Nat.factorization_prod hne, Finset.sum_apply']
  have step1 : ∀ k ∈ Icc 1 n,
      ((Nat.factorial (n / k)) ^ k).factorization p
        = ∑ i ∈ Ico 1 B, k * (n / p ^ i / k) := by
    intro k _
    have hlog : Nat.log p (n / k) < B := by
      rcases Nat.eq_zero_or_pos (n / k) with h0 | h0
      · rw [h0, Nat.log_zero_right]; exact hB0
      · exact Nat.log_lt_of_lt_pow h0.ne' (lt_of_le_of_lt (Nat.div_le_self n k) hn)
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.factorization_factorial hp hlog, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hq : n / p ^ i ≤ n := Nat.div_le_self _ _
  unfold S
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hq) ?_).symm
  intro k hk hk'
  simp only [mem_Icc] at hk hk'
  have hlt : n / p ^ i < k := by omega
  rw [Nat.div_eq_of_lt hlt, mul_zero]

lemma S_le_sq (q : ℕ) : S q ≤ q ^ 2 := by
  have h : ∀ k ∈ Icc 1 q, k * (q / k) ≤ q := by
    intro k _
    calc k * (q / k) = q / k * k := mul_comm _ _
    _ ≤ q := Nat.div_mul_le_self q k
  calc S q ≤ ∑ _k ∈ Icc 1 q, q := Finset.sum_le_sum h
  _ = q * q := by
      rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  _ = q ^ 2 := (pow_two q).symm

/-- The division defining A129365 is exact. -/
lemma den_dvd_num (n : ℕ) : den n ∣ num n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · unfold den num; simp
  rw [← Nat.factorization_le_iff_dvd (den_ne_zero n) (num_ne_zero n), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hB : n < p ^ n :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hp.two_le n)
    rw [num_factorization hp hB, den_factorization hp hn0 hB]
    exact Finset.sum_le_sum fun i _ => S_le_sq _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The `p`-adic valuation of A129365(n). -/
lemma a_factorization {p : ℕ} (hp : p.Prime) {n B : ℕ} (hn0 : 0 < n) (hn : n < p ^ B) :
    (a n).factorization p
      = (∑ i ∈ Ico 1 B, (n / p ^ i) ^ 2) - ∑ i ∈ Ico 1 B, S (n / p ^ i) := by
  rw [a_eq, Nat.factorization_div (den_dvd_num n), Finsupp.tsub_apply,
      num_factorization hp hn, den_factorization hp hn0 hn]

end A129365

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  have hp1 : 1 < p := hp.one_lt
  set B := n * p + p with hB
  have hBlt : B < p ^ B := Nat.lt_pow_self hp1
  have h1 : n * p < p ^ B := by omega
  have h2 : n * p + k < p ^ B := by omega
  have hnp : 0 < n * p := Nat.mul_pos hn (by omega)
  rw [A129365.a_factorization hp hnp h1, A129365.a_factorization hp (by omega) h2]
  have key : ∀ i ∈ Ico 1 B, (n * p + k) / p ^ i = n * p / p ^ i := by
    intro i hi
    have hi1 : 1 ≤ i := (mem_Ico.mp hi).1
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    have e1 : (n * p + k) / p = n := by
      rw [add_comm, Nat.add_mul_div_right k n (by omega : 0 < p),
        Nat.div_eq_of_lt hk, zero_add]
    have e2 : n * p / p = n := by
      have := Nat.add_mul_div_right 0 n (show 0 < p by omega)
      simpa using this
    rw [e1, e2]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => by rw [key i hi]
  · exact Finset.sum_congr rfl fun i hi => by rw [key i hi]
