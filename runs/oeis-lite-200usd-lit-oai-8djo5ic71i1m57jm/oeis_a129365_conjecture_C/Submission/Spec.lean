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


set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace A129365Work

def num (N : ℕ) : ℕ := (Icc 1 N).prod fun j => (Icc 1 N).prod fun k => Nat.gcd j k
def den (N : ℕ) : ℕ := (Icc 1 N).prod fun k => (Nat.factorial (N / k)) ^ k

def Vnum (N q B : ℕ) : ℕ := ∑ i ∈ Ico 1 B, (N / q ^ i) ^ 2
def Vden (N q B : ℕ) : ℕ := ∑ i ∈ Ico 1 B, ∑ k ∈ Icc 1 N, k * (N / (k * q ^ i))

lemma Icc_one_eq_Ioc_zero (N : ℕ) : (Icc 1 N : Finset ℕ) = Ioc 0 N := by
  ext x; simp only [mem_Icc, mem_Ioc]; omega

lemma card_multiples_Icc (N d : ℕ) :
    ∑ x ∈ Icc 1 N, (if d ∣ x then 1 else 0) = N / d := by
  rw [← Finset.card_filter]
  rw [Icc_one_eq_Ioc_zero, Nat.Ioc_filter_dvd_card_eq_div]

lemma min_eq_sum_ind (a b B : ℕ) (ha : a < B) (hb : b < B) :
    min a b = ∑ i ∈ Ico 1 B, if i ≤ a ∧ i ≤ b then 1 else 0 := by
  rw [← Finset.card_filter]
  have h : ({i ∈ Ico 1 B | i ≤ a ∧ i ≤ b} : Finset ℕ) = Icc 1 (min a b) := by
    ext i
    simp only [mem_filter, mem_Ico, mem_Icc]
    omega
  rw [h, Nat.card_Icc]
  omega

lemma pow_dvd_iff_le_fac {q x i : ℕ} (hq : Nat.Prime q) (hx : x ≠ 0) :
    q ^ i ∣ x ↔ i ≤ x.factorization q := by
  exact hq.pow_dvd_iff_le_factorization hx

lemma sum_indicator_and_eq_mul (N d : ℕ) :
    (∑ x ∈ Icc 1 N, if d ∣ x then 1 else 0) ^ 2
      = ∑ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, if d ∣ x ∧ d ∣ y then 1 else 0 := by
  rw [pow_two]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hx' : d ∣ x <;> by_cases hy' : d ∣ y <;> simp [hx', hy']

lemma factorization_lt_of_lt_pow {q x B : ℕ} (hq : Nat.Prime q) (hx0 : x ≠ 0) (hx : x < q ^ B) :
    x.factorization q < B := by
  by_contra hnot
  have hle : B ≤ x.factorization q := Nat.le_of_not_gt hnot
  have hdvd : q ^ B ∣ x := (hq.pow_dvd_iff_le_factorization hx0).2 hle
  have hqpow0 : 0 < q ^ B := pow_pos hq.pos B
  have : q ^ B ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hdvd
  omega

lemma min_fac_eq_sum_pow_dvd {N q B j k : ℕ} (hq : Nat.Prime q)
    (hj : j ∈ Icc 1 N) (hk : k ∈ Icc 1 N) (hB : N < q ^ B) :
    min (j.factorization q) (k.factorization q)
      = ∑ i ∈ Ico 1 B, if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0 := by
  have hjpos : j ≠ 0 := by
    have : 1 ≤ j := (mem_Icc.mp hj).1
    omega
  have hkpos : k ≠ 0 := by
    have : 1 ≤ k := (mem_Icc.mp hk).1
    omega
  have hjlt : j < q ^ B := lt_of_le_of_lt (mem_Icc.mp hj).2 hB
  have hklt : k < q ^ B := lt_of_le_of_lt (mem_Icc.mp hk).2 hB
  rw [min_eq_sum_ind (j.factorization q) (k.factorization q) B
    (factorization_lt_of_lt_pow hq hjpos hjlt) (factorization_lt_of_lt_pow hq hkpos hklt)]
  apply Finset.sum_congr rfl
  intro i hi
  have hjiff : (i ≤ j.factorization q) ↔ q ^ i ∣ j := (hq.pow_dvd_iff_le_factorization hjpos).symm
  have hkiff : (i ≤ k.factorization q) ↔ q ^ i ∣ k := (hq.pow_dvd_iff_le_factorization hkpos).symm
  by_cases h1 : i ≤ j.factorization q <;> by_cases h2 : i ≤ k.factorization q
  · have hdj : q ^ i ∣ j := hjiff.mp h1
    have hdk : q ^ i ∣ k := hkiff.mp h2
    simp [h1, h2, hdj, hdk]
  · have hdj : q ^ i ∣ j := hjiff.mp h1
    have hndk : ¬ q ^ i ∣ k := fun h => h2 (hkiff.mpr h)
    simp [h1, h2, hdj, hndk]
  · have hndj : ¬ q ^ i ∣ j := fun h => h1 (hjiff.mpr h)
    have hdk : q ^ i ∣ k := hkiff.mp h2
    simp [h1, h2, hndj, hdk]
  · have hndj : ¬ q ^ i ∣ j := fun h => h1 (hjiff.mpr h)
    have hndk : ¬ q ^ i ∣ k := fun h => h2 (hkiff.mpr h)
    simp [h1, h2, hndj, hndk]

lemma num_fac_formula (N q B : ℕ) (hq : Nat.Prime q) (hB : N < q ^ B) :
    (num N).factorization q = Vnum N q B := by
  classical
  unfold num Vnum
  rw [Nat.factorization_prod_apply]
  · trans ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (Nat.gcd j k).factorization q
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.factorization_prod_apply]
      intro k hk
      exact Nat.gcd_ne_zero_left (by
        have : 1 ≤ j := (mem_Icc.mp hj).1
        omega)
    trans ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
        ∑ i ∈ Ico 1 B, if q ^ i ∣ j ∧ q ^ i ∣ k then 1 else 0
    · apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.factorization_gcd]
      · rw [Finsupp.inf_apply]
        change min (j.factorization q) (k.factorization q) = _
        exact min_fac_eq_sum_pow_dvd hq hj hk hB
      · have : 1 ≤ j := (mem_Icc.mp hj).1; omega
      · have : 1 ≤ k := (mem_Icc.mp hk).1; omega
    · simp_rw [Finset.sum_comm (s := Icc 1 N) (t := Ico 1 B)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← sum_indicator_and_eq_mul N (q ^ i)]
      rw [card_multiples_Icc]
  · intro j hj
    exact Finset.prod_ne_zero_iff.mpr (by
      intro k hk
      exact Nat.gcd_ne_zero_left (by
        have : 1 ≤ j := (mem_Icc.mp hj).1
        omega))

end A129365Work

namespace A129365Work

lemma div_pos_of_mem_Icc {N k : ℕ} (hk : k ∈ Icc 1 N) : 0 < N / k := by
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hkN : k ≤ N := (mem_Icc.mp hk).2
  exact Nat.div_pos hkN hk1

lemma den_fac_formula (N q B : ℕ) (hq : Nat.Prime q) (hB : N < q ^ B) :
    (den N).factorization q = Vden N q B := by
  classical
  unfold den Vden
  rw [Nat.factorization_prod_apply]
  · trans ∑ k ∈ Icc 1 N, k * (Nat.factorial (N / k)).factorization q
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.factorization_pow]
      simp
    trans ∑ k ∈ Icc 1 N, k * (∑ i ∈ Ico 1 B, (N / k) / q ^ i)
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.factorization_factorial hq]
      have hmpos : (N / k) ≠ 0 := by exact (div_pos_of_mem_Icc hk).ne'
      exact Nat.log_lt_of_lt_pow hmpos (lt_of_le_of_lt (Nat.div_le_self N k) hB)
    · simp_rw [Finset.mul_sum]
      simp_rw [Nat.div_div_eq_div_mul]
      rw [Finset.sum_comm]
  · intro k hk
    exact pow_ne_zero k (Nat.factorial_ne_zero _)

end A129365Work

namespace A129365Work

lemma card_filter_Icc_le (N M : ℕ) :
    ((Icc 1 N).filter fun k => k ≤ M).card ≤ M := by
  have hsub : ((Icc 1 N).filter fun k => k ≤ M) ⊆ Icc 1 M := by
    intro k hk
    simp only [mem_filter, mem_Icc] at hk ⊢
    exact ⟨hk.1.1, hk.2⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  omega

lemma sum_mul_div_le_sq (N M : ℕ) :
    ∑ k ∈ Icc 1 N, k * (M / k) ≤ M ^ 2 := by
  classical
  calc
    ∑ k ∈ Icc 1 N, k * (M / k)
        ≤ ∑ k ∈ Icc 1 N, (if k ≤ M then M else 0) := by
          apply Finset.sum_le_sum
          intro k hk
          by_cases h : k ≤ M
          · simp [h]
            exact Nat.mul_div_le M k
          · have hkgt : M < k := Nat.lt_of_not_ge h
            have hdiv : M / k = 0 := Nat.div_eq_of_lt hkgt
            simp [h, hdiv]
    _ = ((Icc 1 N).filter fun k => k ≤ M).card * M := by
          rw [← Finset.sum_filter]
          simp
    _ ≤ M * M := Nat.mul_le_mul_right M (card_filter_Icc_le N M)
    _ = M ^ 2 := by rw [pow_two]

lemma Vden_le_Vnum (N q B : ℕ) : Vden N q B ≤ Vnum N q B := by
  classical
  unfold Vden Vnum
  apply Finset.sum_le_sum
  intro i hi
  let M := N / q ^ i
  calc
    ∑ k ∈ Icc 1 N, k * (N / (k * q ^ i))
        = ∑ k ∈ Icc 1 N, k * (M / k) := by
          apply Finset.sum_congr rfl
          intro k hk
          unfold M
          have hdiv : N / (k * q ^ i) = N / q ^ i / k := by
            rw [mul_comm k (q ^ i)]
            exact (Nat.div_div_eq_div_mul N (q ^ i) k).symm
          rw [hdiv]
    _ ≤ M ^ 2 := sum_mul_div_le_sq N M
    _ = (N / q ^ i) ^ 2 := rfl

lemma num_ne_zero (N : ℕ) : num N ≠ 0 := by
  unfold num
  exact Finset.prod_ne_zero_iff.mpr (by
    intro j hj
    exact Finset.prod_ne_zero_iff.mpr (by
      intro k hk
      exact Nat.gcd_ne_zero_left (by
        have : 1 ≤ j := (mem_Icc.mp hj).1
        omega)))

lemma den_ne_zero (N : ℕ) : den N ≠ 0 := by
  unfold den
  exact Finset.prod_ne_zero_iff.mpr (by
    intro k hk
    exact pow_ne_zero k (Nat.factorial_ne_zero _))

lemma pow_bound_prime (N q : ℕ) (hq : Nat.Prime q) : N < q ^ (N + 1) := by
  have h := Nat.lt_pow_self (n := N + 1) hq.one_lt
  omega

lemma den_dvd_num (N : ℕ) : den N ∣ num N := by
  apply (Nat.factorization_prime_le_iff_dvd (den_ne_zero N) (num_ne_zero N)).mp
  intro q hq
  rw [den_fac_formula N q (N+1) hq (pow_bound_prime N q hq)]
  rw [num_fac_formula N q (N+1) hq (pow_bound_prime N q hq)]
  exact Vden_le_Vnum N q (N+1)

lemma a_eq_num_div_den (N : ℕ) : a N = num N / den N := by
  simp [a, num, den]

lemma a_fac_formula (N q B : ℕ) (hq : Nat.Prime q) (hB : N < q ^ B) :
    (a N).factorization q = Vnum N q B - Vden N q B := by
  rw [a_eq_num_div_den]
  rw [Nat.factorization_div (den_dvd_num N)]
  rw [Finsupp.coe_tsub, Pi.sub_apply]
  rw [num_fac_formula N q B hq hB]
  rw [den_fac_formula N q B hq hB]

end A129365Work

namespace A129365Work

lemma div_mul_add_lt (n p k : ℕ) (hp0 : 0 < p) (hk : k < p) : (n * p + k) / p = n := by
  rw [mul_comm n p]
  rw [Nat.mul_add_div hp0]
  rw [Nat.div_eq_of_lt hk]
  simp

lemma div_mul_exact (n p : ℕ) (hp0 : 0 < p) : (n * p) / p = n := by
  rw [mul_comm n p, Nat.mul_div_right n hp0]

lemma div_by_mul_pow_eq (N p r i : ℕ) (hi : 1 ≤ i) :
    N / (r * p ^ i) = (N / p) / (r * p ^ (i - 1)) := by
  rw [Nat.div_div_eq_div_mul]
  congr 1
  calc
    r * p ^ i = r * (p ^ (i - 1) * p) := by rw [← pow_succ, Nat.sub_add_cancel hi]
    _ = p * (r * p ^ (i - 1)) := by ac_rfl

lemma div_pow_eq (N p i : ℕ) (hi : 1 ≤ i) :
    N / p ^ i = (N / p) / p ^ (i - 1) := by
  simpa using (div_by_mul_pow_eq N p 1 i hi)

lemma Vnum_mul_add_eq (n p k B : ℕ) (hp0 : 0 < p) (hk : k < p) :
    Vnum (n * p + k) p B = Vnum (n * p) p B := by
  classical
  unfold Vnum
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : 1 ≤ i := (mem_Ico.mp hi).1
  have h1 : (n * p + k) / p ^ i = (n * p) / p ^ i := by
    rw [div_pow_eq (n*p+k) p i hi1, div_pow_eq (n*p) p i hi1]
    rw [div_mul_add_lt n p k hp0 hk, div_mul_exact n p hp0]
  rw [h1]

lemma Vden_mul_add_eq (n p k B : ℕ) (hp0 : 0 < p) (hk : k < p) :
    Vden (n * p + k) p B = Vden (n * p) p B := by
  classical
  unfold Vden
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : 1 ≤ i := (mem_Ico.mp hi).1
  have hN1 : ∑ x ∈ Icc 1 (n * p + k), x * ((n * p + k) / (x * p ^ i))
      = ∑ x ∈ Icc 1 (n * p + k), x * (n / (x * p ^ (i - 1))) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [div_by_mul_pow_eq (n*p+k) p x i hi1]
    rw [div_mul_add_lt n p k hp0 hk]
  have hN0 : ∑ x ∈ Icc 1 (n * p), x * (n * p / (x * p ^ i))
      = ∑ x ∈ Icc 1 (n * p), x * (n / (x * p ^ (i - 1))) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [div_by_mul_pow_eq (n*p) p x i hi1]
    rw [div_mul_exact n p hp0]
  rw [hN1, hN0]
  apply Eq.symm
  apply Finset.sum_subset
  · exact Finset.Icc_subset_Icc le_rfl (by omega)
  · intro x hx hxnot
    have hxparts : 1 ≤ x ∧ x ≤ n * p + k := mem_Icc.mp hx
    have hx_gt : n * p < x := by
      have hnotle : ¬ x ≤ n * p := by
        intro hle
        exact hxnot (mem_Icc.mpr ⟨hxparts.1, hle⟩)
      omega
    have hn_lt_x : n < x := by
      have hn_le_np : n ≤ n * p := by
        exact Nat.le_mul_of_pos_right (m := p) n hp0
      omega
    have hdenpos : 1 ≤ p ^ (i - 1) := Nat.one_le_pow (i - 1) p hp0
    have hlt : n < x * p ^ (i - 1) := by
      exact lt_of_lt_of_le hn_lt_x (by
        exact Nat.le_mul_of_pos_right (m := p ^ (i - 1)) x (lt_of_lt_of_le zero_lt_one hdenpos))
    have hdiv : n / (x * p ^ (i - 1)) = 0 := Nat.div_eq_of_lt hlt
    simp [hdiv]

end A129365Work

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  let B := n * p + k + 1
  have hp0 : 0 < p := hp.pos
  have hle : n * p ≤ n * p + k := by omega
  have hB1 : n * p + k < p ^ B := by
    unfold B
    exact A129365Work.pow_bound_prime (n*p+k) p hp
  have hB0 : n * p < p ^ B := lt_of_le_of_lt hle hB1
  rw [A129365Work.a_fac_formula (n*p) p B hp hB0]
  rw [A129365Work.a_fac_formula (n*p+k) p B hp hB1]
  rw [A129365Work.Vnum_mul_add_eq n p k B hp0 hk]
  rw [A129365Work.Vden_mul_add_eq n p k B hp0 hk]
