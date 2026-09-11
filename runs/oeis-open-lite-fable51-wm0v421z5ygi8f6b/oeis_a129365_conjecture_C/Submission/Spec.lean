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

lemma min_fact_eq_sum {p : ℕ} (hp : p.Prime) {j k b : ℕ} (hj : j ≠ 0) (hk : k ≠ 0)
    (hb : j.factorization p < b) :
    min (j.factorization p) (k.factorization p) =
      ∑ i ∈ Ico 1 b, (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
  rw [Finset.sum_boole, Nat.cast_id]
  have : filter (fun i => p ^ i ∣ j ∧ p ^ i ∣ k) (Ico 1 b)
      = Ico 1 (min (j.factorization p) (k.factorization p) + 1) := by
    ext i
    simp only [mem_filter, mem_Ico, hp.pow_dvd_iff_le_factorization hj,
      hp.pow_dvd_iff_le_factorization hk]
    omega
  rw [this, Nat.card_Ico]
  omega

lemma num_factorization {p : ℕ} (hp : p.Prime) (N b : ℕ) (hb : N < b) :
    ((Icc 1 N).prod fun j => (Icc 1 N).prod fun k => Nat.gcd j k).factorization p
      = ∑ i ∈ Ico 1 b, (N / p ^ i) ^ 2 := by
  have hne : ∀ j ∈ Icc 1 N, ∀ k ∈ Icc 1 N, Nat.gcd j k ≠ 0 := by
    intro j hj k hk
    simp only [mem_Icc] at hj
    exact Nat.gcd_ne_zero_left (by omega)
  rw [Nat.factorization_prod_apply (fun j hj => Finset.prod_ne_zero_iff.mpr (hne j hj))]
  have h1 : ∀ j ∈ Icc 1 N, ((Icc 1 N).prod fun k => Nat.gcd j k).factorization p
      = ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 N, (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
    intro j hj
    rw [Nat.factorization_prod_apply (hne j hj), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [mem_Icc] at hj hk
    rw [Nat.factorization_gcd (by omega) (by omega), Finsupp.inf_apply]
    exact min_fact_eq_sum hp (by omega) (by omega)
      (lt_of_lt_of_le (Nat.factorization_lt p (by omega)) (by omega))
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have h2 : ∀ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0)
      = (if p ^ i ∣ j then 1 else 0) * ∑ k ∈ Icc 1 N, (if p ^ i ∣ k then 1 else 0) := by
    intro j hj
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    split_ifs <;> simp_all
  have h3 : Icc 1 N = Ioc 0 N := by ext x; simp only [mem_Icc, mem_Ioc]; omega
  rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, Finset.sum_boole, Nat.cast_id,
    h3, Nat.Ioc_filter_dvd_card_eq_div, sq]

lemma den_factorization {p : ℕ} (hp : p.Prime) (N b : ℕ) (hb : N < b) :
    ((Icc 1 N).prod fun k => (Nat.factorial (N / k)) ^ k).factorization p
      = ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 N, k * (N / p ^ i / k) := by
  rw [Nat.factorization_prod_apply (fun k _ => pow_ne_zero _ (factorial_ne_zero _))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_def _ hp]
  haveI := Fact.mk hp
  rw [padicValNat_factorial (b := b)
    (lt_of_le_of_lt (Nat.log_le_self _ _) (lt_of_le_of_lt (Nat.div_le_self _ _) hb))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm (p ^ i) k, mul_comm]

lemma sum_div_eq (M N : ℕ) (h : M ≤ N) :
    ∑ k ∈ Icc 1 N, k * (M / k) = ∑ k ∈ Icc 1 M, k * (M / k) := by
  symm
  apply Finset.sum_subset
  · intro x hx; simp only [mem_Icc] at hx ⊢; omega
  · intro x hx hx'
    simp only [mem_Icc] at hx hx'
    rw [Nat.div_eq_of_lt (by omega)]; simp

lemma den_dvd_num (N : ℕ) :
    ((Icc 1 N).prod fun k => (Nat.factorial (N / k)) ^ k) ∣
      ((Icc 1 N).prod fun j => (Icc 1 N).prod fun k => Nat.gcd j k) := by
  have hden : ((Icc 1 N).prod fun k => (Nat.factorial (N / k)) ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (factorial_ne_zero _))
  have hnum : ((Icc 1 N).prod fun j => (Icc 1 N).prod fun k => Nat.gcd j k) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun j hj => Finset.prod_ne_zero_iff.mpr (fun k hk => ?_))
    simp only [mem_Icc] at hj
    exact Nat.gcd_ne_zero_left (by omega)
  rw [← Nat.factorization_le_iff_dvd hden hnum]
  intro q
  by_cases hq : q.Prime
  · rw [num_factorization hq N (N+1) (lt_succ_self N), den_factorization hq N (N+1) (lt_succ_self N)]
    apply Finset.sum_le_sum
    intro i hi
    rw [sum_div_eq _ _ (Nat.div_le_self _ _), sq]
    calc ∑ k ∈ Icc 1 (N / q ^ i), k * (N / q ^ i / k)
        ≤ ∑ k ∈ Icc 1 (N / q ^ i), N / q ^ i := Finset.sum_le_sum (fun k _ => Nat.mul_div_le _ _)
      _ = N / q ^ i * (N / q ^ i) := by simp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  simp only [a]
  rw [Nat.factorization_div (den_dvd_num _), Nat.factorization_div (den_dvd_num _)]
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  have hb1 : n * p < n * p + p := by omega
  have hb2 : n * p + k < n * p + p := by omega
  rw [num_factorization hp (n*p) _ hb1, num_factorization hp (n*p+k) _ hb2,
    den_factorization hp _ _ hb1, den_factorization hp _ _ hb2]
  have key : ∀ i ∈ Ico 1 (n * p + p), (n * p + k) / p ^ i = (n * p) / p ^ i := by
    intro i hi
    simp only [mem_Ico] at hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [pow_succ, mul_comm (p ^ i'), ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ hp.pos, add_comm, Nat.add_mul_div_right _ _ hp.pos,
      Nat.div_eq_of_lt hk, zero_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i hi => by rw [key i hi])
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [key i hi, sum_div_eq _ _ (Nat.div_le_self _ _),
      sum_div_eq (n * p / p ^ i) (n * p + k) (le_trans (Nat.div_le_self _ _) (by omega))]


theorem oeis_a129365_conjecture_C.disproof : ¬ (type_of% @oeis_a129365_conjecture_C) := sorry
