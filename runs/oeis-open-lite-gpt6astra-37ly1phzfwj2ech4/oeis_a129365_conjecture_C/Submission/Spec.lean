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

def num (N : ℕ) := (Icc 1 N).prod fun j => (Icc 1 N).prod fun k => Nat.gcd j k
def den (N : ℕ) := (Icc 1 N).prod fun k => (Nat.factorial (N / k)) ^ k

lemma num_ne (N : ℕ) : num N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact Nat.gcd_ne_zero_left (by have := (mem_Icc.mp hj).1; omega)

lemma den_ne (N : ℕ) : den N ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _))

lemma count_dvd (N d : ℕ) : (∑ j ∈ Icc 1 N, if d ∣ j then 1 else 0) = N / d := by
  rw [Finset.sum_boole]
  rw [← Nat.card_multiples' N d]
  apply congrArg Finset.card
  ext j
  simp only [mem_filter, mem_Icc, mem_range]
  omega

lemma num_val (N p B : ℕ) (hp : p.Prime) (hB : Nat.log p N < B) :
    (num N).factorization p = ∑ i ∈ Ico 1 B, (N / p ^ i) ^ 2 := by
  have hpow : N < p ^ B := Nat.lt_pow_of_log_lt hp.one_lt hB
  have hn j (hj : j ∈ Icc 1 N) : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
  unfold num
  rw [Nat.factorization_prod_apply (fun j hj => Finset.prod_ne_zero_iff.mpr
    (fun k hk => Nat.gcd_ne_zero_left (hn j hj)))]
  simp_rw [Nat.factorization_prod_apply (fun k hk => Nat.gcd_ne_zero_right (hn k hk))]
  have hv j (hj : j ∈ Icc 1 N) k (hk : k ∈ Icc 1 N) :
      (Nat.gcd j k).factorization p = ∑ i ∈ Ico 1 B, if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp
      (Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (hn j hj)))
      ((Nat.gcd_le_left k (Nat.pos_of_ne_zero (hn j hj))).trans_lt
        ((mem_Icc.mp hj).2.trans_lt hpow))]
    simp [Nat.dvd_gcd_iff, Finset.sum_boole]
  calc
    _ = ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, ∑ i ∈ Ico 1 B,
          if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
      apply sum_congr rfl; intro j hj
      apply sum_congr rfl; intro k hk
      exact hv j hj k hk
    _ = ∑ i ∈ Ico 1 B, ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
          if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
      simp_rw [Finset.sum_comm (s := Icc 1 N) (t := Ico 1 B)]
    _ = _ := by
      apply sum_congr rfl; intro i hi
      simp_rw [show ∀ j k : ℕ, (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) =
        (if p ^ i ∣ j then 1 else 0) * (if p ^ i ∣ k then 1 else 0) by
          intros; split_ifs <;> simp_all]
      rw [← Finset.sum_mul_sum, count_dvd, pow_two]

lemma sum_div_extend (M N : ℕ) (h : M ≤ N) :
    (∑ k ∈ Icc 1 N, k * (M / k)) = ∑ k ∈ Icc 1 M, k * (M / k) := by
  symm
  apply Finset.sum_subset (Icc_subset_Icc le_rfl h)
  intro k hk hnot
  have hmk : M < k := by
    simp only [mem_Icc] at hk hnot
    omega
  simp [Nat.div_eq_of_lt hmk]

lemma den_val (N p B : ℕ) (hp : p.Prime) (hB : Nat.log p N < B) :
    (den N).factorization p =
      ∑ i ∈ Ico 1 B, ∑ k ∈ Icc 1 (N / p ^ i), k * ((N / p ^ i) / k) := by
  unfold den
  rw [Nat.factorization_prod_apply (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _))]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hf k : (N / k).factorial.factorization p = ∑ i ∈ Ico 1 B, (N / p ^ i) / k := by
    rw [Nat.factorization_factorial hp ((Nat.log_mono_right (Nat.div_le_self N k)).trans_lt hB)]
    apply sum_congr rfl; intro i hi
    simp [Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro i hi
  exact sum_div_extend _ _ (Nat.div_le_self _ _)

lemma sum_div_le (M : ℕ) : (∑ k ∈ Icc 1 M, k * (M / k)) ≤ M ^ 2 := by
  calc
    _ ≤ ∑ k ∈ Icc 1 M, M := Finset.sum_le_sum (fun k _ => Nat.mul_div_le M k)
    _ = M ^ 2 := by simp [pow_two]

lemma den_dvd_num (N : ℕ) : den N ∣ num N := by
  apply (Nat.factorization_prime_le_iff_dvd (den_ne N) (num_ne N)).mp
  intro p hp
  rw [den_val N p (Nat.log p N + 1) hp (by omega),
    num_val N p (Nat.log p N + 1) hp (by omega)]
  exact Finset.sum_le_sum (fun i _ => sum_div_le _)

lemma quotient_val_eq (N M p : ℕ) (hp : p.Prime) (h : N / p = M / p) :
    (num N / den N).factorization p = (num M / den M).factorization p := by
  let B := max (Nat.log p N) (Nat.log p M) + 1
  have hN : Nat.log p N < B := by dsimp [B]; omega
  have hM : Nat.log p M < B := by dsimp [B]; omega
  have hdiv i (hi : i ∈ Ico 1 B) : N / p ^ i = M / p ^ i := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by
      have := (mem_Ico.mp hi).1; omega)
    simp only [pow_succ', ← Nat.div_div_eq_div_mul, h]
  rw [Nat.factorization_div (den_dvd_num N), Nat.factorization_div (den_dvd_num M),
    Finsupp.tsub_apply, Finsupp.tsub_apply,
    num_val N p B hp hN, num_val M p B hp hM,
    den_val N p B hp hN, den_val M p B hp hM]
  congr 1
  · exact sum_congr rfl (fun i hi => by rw [hdiv i hi])
  · exact sum_congr rfl (fun i hi => by rw [hdiv i hi])

end A129365

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  apply A129365.quotient_val_eq _ _ _ hp
  rw [Nat.mul_div_cancel _ hp.pos, Nat.mul_comm n p, Nat.mul_add_div hp.pos,
    Nat.div_eq_of_lt hk, Nat.add_zero]

theorem oeis_a129365_conjecture_C.disproof : ¬ (type_of% @oeis_a129365_conjecture_C) := sorry
