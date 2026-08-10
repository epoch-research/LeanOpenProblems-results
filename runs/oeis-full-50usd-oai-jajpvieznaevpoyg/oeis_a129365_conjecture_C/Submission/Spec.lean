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


def numerator (N : ℕ) : ℕ := (Icc 1 N).prod fun j => (Icc 1 N).prod fun k => Nat.gcd j k

def denominator (N : ℕ) : ℕ := (Icc 1 N).prod fun k => (Nat.factorial (N / k)) ^ k

lemma numerator_ne_zero (N : ℕ) : numerator N ≠ 0 := by
  unfold numerator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply Nat.gcd_ne_zero_left
  exact (Nat.succ_le_iff.mp (mem_Icc.mp hj).1).ne'

lemma denominator_ne_zero (N : ℕ) : denominator N ≠ 0 := by
  unfold denominator
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact pow_ne_zero _ (Nat.factorial_ne_zero _)



lemma num_fac (N q : ℕ) (_hq : Nat.Prime q) :
    (numerator N).factorization q =
      ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, min (j.factorization q) (k.factorization q) := by
  unfold numerator
  rw [Nat.factorization_prod_apply]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.factorization_prod_apply]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.factorization_gcd]
      · simp [Finsupp.inf_apply]
      · exact (Nat.succ_le_iff.mp (mem_Icc.mp hj).1).ne'
      · exact (Nat.succ_le_iff.mp (mem_Icc.mp hk).1).ne'
    · intro k hk
      apply Nat.gcd_ne_zero_left
      exact (Nat.succ_le_iff.mp (mem_Icc.mp hj).1).ne'
  · intro j hj
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply Nat.gcd_ne_zero_left
    exact (Nat.succ_le_iff.mp (mem_Icc.mp hj).1).ne'


lemma den_fac (N q : ℕ) :
    (denominator N).factorization q =
      ∑ k ∈ Icc 1 N, k * ((N / k)!).factorization q := by
  unfold denominator
  rw [Nat.factorization_prod_apply]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.factorization_pow]
    simp
  · intro k hk
    exact pow_ne_zero _ (Nat.factorial_ne_zero _)


lemma lt_prime_pow_succ_of_le (N x p : ℕ) (hp : Nat.Prime p) (hx : x ≤ N) : x < p ^ (N + 1) := by
  have hN : N < p ^ (N + 1) := by
    calc
      N < N + 1 := Nat.lt_succ_self N
      _ ≤ p ^ (N + 1) := by
        -- since p ≥ 2, p^(N+1) ≥ N+1
        exact (Nat.lt_pow_self hp.one_lt (n := N + 1)).le
  exact lt_of_le_of_lt hx hN

lemma factorization_eq_sum_ind (N x p : ℕ) (hp : Nat.Prime p) (hx0 : 0 < x) (hxN : x ≤ N) :
    x.factorization p = ∑ i ∈ Icc 1 N, if p ^ i ∣ x then 1 else 0 := by
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hx0 (lt_prime_pow_succ_of_le N x p hp hxN)]
  rw [← Ico_succ_right_eq_Icc]
  exact Finset.card_filter (fun i => p ^ i ∣ x) (Icc 1 N)


lemma min_eq_sum_ind (N a b : ℕ) (ha : a ≤ N) (_hb : b ≤ N) :
    min a b = ∑ i ∈ Icc 1 N, if i ≤ a ∧ i ≤ b then 1 else 0 := by
  rw [← Finset.card_filter]
  have hset : ({i ∈ Icc 1 N | i ≤ a ∧ i ≤ b} : Finset ℕ) = Icc 1 (min a b) := by
    ext i
    simp only [mem_filter, mem_Icc]
    omega
  rw [hset]
  simp

lemma min_factorization_eq_sum_ind (N x y p : ℕ) (hp : Nat.Prime p)
    (hx0 : 0 < x) (hy0 : 0 < y) (hxN : x ≤ N) (hyN : y ≤ N) :
    min (x.factorization p) (y.factorization p) =
      ∑ i ∈ Icc 1 N, if p ^ i ∣ x ∧ p ^ i ∣ y then 1 else 0 := by
  have hxle : x.factorization p ≤ N := (Nat.factorization_lt p hx0.ne').le.trans hxN
  have hyle : y.factorization p ≤ N := (Nat.factorization_lt p hy0.ne').le.trans hyN
  rw [min_eq_sum_ind N (x.factorization p) (y.factorization p) hxle hyle]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hix : p ^ i ∣ x <;> by_cases hiy : p ^ i ∣ y
  · have hix' : i ≤ x.factorization p := (hp.pow_dvd_iff_le_factorization hx0.ne').mp hix
    have hiy' : i ≤ y.factorization p := (hp.pow_dvd_iff_le_factorization hy0.ne').mp hiy
    simp [hix, hiy, hix', hiy']
  · have hiy' : ¬ i ≤ y.factorization p := by
      intro hle; exact hiy ((hp.pow_dvd_iff_le_factorization hy0.ne').mpr hle)
    simp [hix, hiy, hiy']
  · have hix' : ¬ i ≤ x.factorization p := by
      intro hle; exact hix ((hp.pow_dvd_iff_le_factorization hx0.ne').mpr hle)
    simp [hix, hiy, hix']
  · have hix' : ¬ i ≤ x.factorization p := by
      intro hle; exact hix ((hp.pow_dvd_iff_le_factorization hx0.ne').mpr hle)
    simp [hix, hiy, hix']


lemma sum_Icc_dvd_indicator (N d : ℕ) :
    (∑ j ∈ Icc 1 N, if d ∣ j then 1 else 0) = N / d := by
  rw [← Finset.card_filter]
  have hset : ({j ∈ Icc 1 N | d ∣ j} : Finset ℕ) = {j ∈ range (N + 1) | j ≠ 0 ∧ d ∣ j} := by
    ext j
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · intro h
      constructor
      · omega
      · constructor
        · omega
        · exact h.2
    · intro h
      constructor
      · constructor <;> omega
      · exact h.2.2
  rw [hset]
  simpa [Nat.succ_eq_add_one] using Nat.card_multiples' N d

lemma double_sum_dvd_indicator (N d : ℕ) :
    (∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, if d ∣ j ∧ d ∣ k then 1 else 0) =
      (N / d) * (N / d) := by
  have hconst : (∑ j ∈ Icc 1 N, if d ∣ j then (N / d) else 0) =
      (N / d) * (∑ j ∈ Icc 1 N, if d ∣ j then 1 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases ha : d ∣ j <;> simp [ha]
  calc
    (∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, if d ∣ j ∧ d ∣ k then 1 else 0)
        = ∑ j ∈ Icc 1 N, if d ∣ j then (N / d) else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hjd : d ∣ j
          · have hcnt : #({x ∈ Icc 1 N | d ∣ x}) = N / d := by
              rw [Finset.card_filter]
              exact sum_Icc_dvd_indicator N d
            simp [hjd, hcnt]
          · simp [hjd]
    _ = (N / d) * (N / d) := by
          rw [hconst, sum_Icc_dvd_indicator]

lemma numerator_factorization_formula (N p : ℕ) (hp : Nat.Prime p) :
    (numerator N).factorization p = ∑ i ∈ Icc 1 N, (N / p ^ i) * (N / p ^ i) := by
  rw [num_fac N p hp]
  calc
    (∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, min (j.factorization p) (k.factorization p))
        = ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
            ∑ i ∈ Icc 1 N, if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          exact min_factorization_eq_sum_ind N j k p hp
            (Nat.succ_le_iff.mp (mem_Icc.mp hj).1)
            (Nat.succ_le_iff.mp (mem_Icc.mp hk).1)
            (mem_Icc.mp hj).2 (mem_Icc.mp hk).2
    _ = ∑ j ∈ Icc 1 N, ∑ i ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
            if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_comm]
    _ = ∑ i ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
            if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ Icc 1 N, (N / p ^ i) * (N / p ^ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact double_sum_dvd_indicator N (p ^ i)

lemma log_div_lt_succ (N k p : ℕ) : Nat.log p (N / k) < N + 1 := by
  have h1 : Nat.log p (N / k) ≤ N / k := Nat.log_le_self p (N / k)
  have h2 : N / k ≤ N := Nat.div_le_self N k
  omega

lemma denominator_factorization_formula (N p : ℕ) (hp : Nat.Prime p) :
    (denominator N).factorization p =
      ∑ i ∈ Icc 1 N, ∑ k ∈ Icc 1 N, k * (N / (k * p ^ i)) := by
  rw [den_fac]
  calc
    (∑ k ∈ Icc 1 N, k * ((N / k)!).factorization p)
        = ∑ k ∈ Icc 1 N, k * (∑ i ∈ Icc 1 N, (N / k) / p ^ i) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.factorization_factorial hp (log_div_lt_succ N k p)]
          have hI : Ico 1 (N + 1) = Icc 1 N := by
            ext i
            simp only [mem_Ico, mem_Icc]
            omega
          rw [hI]
    _ = ∑ k ∈ Icc 1 N, ∑ i ∈ Icc 1 N, k * ((N / k) / p ^ i) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
    _ = ∑ k ∈ Icc 1 N, ∑ i ∈ Icc 1 N, k * (N / (k * p ^ i)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro i hi
          rw [Nat.div_div_eq_div_mul]
    _ = ∑ i ∈ Icc 1 N, ∑ k ∈ Icc 1 N, k * (N / (k * p ^ i)) := by
          rw [Finset.sum_comm]

lemma sum_mul_div_le_square (N m : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Icc 1 N, k * (m / k)) ≤ m * m := by
  have hsub : Icc 1 m ⊆ Icc 1 N := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hm⟩
  calc
    (∑ k ∈ Icc 1 N, k * (m / k)) = ∑ k ∈ Icc 1 m, k * (m / k) := by
      rw [Finset.sum_subset hsub]
      intro k hkN hknot
      have hkgt : m < k := by
        by_contra hle
        exact hknot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hkN).1, Nat.le_of_not_gt hle⟩)
      rw [Nat.div_eq_of_lt hkgt]
      simp
    _ ≤ ∑ k ∈ Icc 1 m, m := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [Nat.mul_comm] using Nat.div_mul_le_self m k
    _ = m * m := by
      simp

lemma denominator_factorization_le_numerator (N q : ℕ) (hq : Nat.Prime q) :
    (denominator N).factorization q ≤ (numerator N).factorization q := by
  rw [denominator_factorization_formula N q hq, numerator_factorization_formula N q hq]
  apply Finset.sum_le_sum
  intro i hi
  have hrewrite : (∑ k ∈ Icc 1 N, k * (N / (k * q ^ i))) =
      ∑ k ∈ Icc 1 N, k * ((N / q ^ i) / k) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    rw [Nat.div_div_eq_div_mul]
    rw [mul_comm]
  rw [hrewrite]
  exact sum_mul_div_le_square N (N / q ^ i) (Nat.div_le_self N (q ^ i))

lemma denominator_dvd_numerator (N : ℕ) : denominator N ∣ numerator N := by
  have hden : denominator N ≠ 0 := denominator_ne_zero N
  have hnum : numerator N ≠ 0 := numerator_ne_zero N
  rw [← Nat.factorization_le_iff_dvd hden hnum]
  intro q
  by_cases hq : Nat.Prime q
  · exact denominator_factorization_le_numerator N q hq
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

lemma div_mul_add_small_by_prime (n p k : ℕ) (hp0 : 0 < p) (hk : k < p) :
    (n * p + k) / p = n := by
  rw [Nat.add_comm]
  rw [Nat.add_mul_div_right _ _ hp0]
  rw [Nat.div_eq_of_lt hk]
  simp

lemma div_mul_by_pos (n p : ℕ) (hp0 : 0 < p) : (n * p) / p = n := by
  rw [mul_comm]
  exact Nat.mul_div_right n hp0

lemma div_pow_eq_of_small (n p k i : ℕ) (hp0 : 0 < p) (hk : k < p) (hi : 1 ≤ i) :
    (n * p + k) / p ^ i = (n * p) / p ^ i := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show 1 + r = r + 1 by omega]
  rw [pow_succ']
  rw [← Nat.div_div_eq_div_mul (n * p + k) p (p ^ r)]
  rw [← Nat.div_div_eq_div_mul (n * p) p (p ^ r)]
  rw [div_mul_add_small_by_prime n p k hp0 hk, div_mul_by_pos n p hp0]

lemma numerator_factorization_formula_bound (N B p : ℕ) (hp : Nat.Prime p) (hNB : N ≤ B) :
    (numerator N).factorization p = ∑ i ∈ Icc 1 B, (N / p ^ i) * (N / p ^ i) := by
  rw [num_fac N p hp]
  calc
    (∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N, min (j.factorization p) (k.factorization p))
        = ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
            ∑ i ∈ Icc 1 B, if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          exact min_factorization_eq_sum_ind B j k p hp
            (Nat.succ_le_iff.mp (mem_Icc.mp hj).1)
            (Nat.succ_le_iff.mp (mem_Icc.mp hk).1)
            ((mem_Icc.mp hj).2.trans hNB) ((mem_Icc.mp hk).2.trans hNB)
    _ = ∑ j ∈ Icc 1 N, ∑ i ∈ Icc 1 B, ∑ k ∈ Icc 1 N,
            if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_comm]
    _ = ∑ i ∈ Icc 1 B, ∑ j ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
            if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ Icc 1 B, (N / p ^ i) * (N / p ^ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact double_sum_dvd_indicator N (p ^ i)

lemma log_div_lt_bound (N B k p : ℕ) (hNB : N ≤ B) : Nat.log p (N / k) < B + 1 := by
  have h1 : Nat.log p (N / k) ≤ N / k := Nat.log_le_self p (N / k)
  have h2 : N / k ≤ N := Nat.div_le_self N k
  omega

lemma denominator_factorization_formula_bound (N B p : ℕ) (hp : Nat.Prime p) (hNB : N ≤ B) :
    (denominator N).factorization p =
      ∑ i ∈ Icc 1 B, ∑ k ∈ Icc 1 N, k * (N / (k * p ^ i)) := by
  rw [den_fac]
  calc
    (∑ k ∈ Icc 1 N, k * ((N / k)!).factorization p)
        = ∑ k ∈ Icc 1 N, k * (∑ i ∈ Icc 1 B, (N / k) / p ^ i) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.factorization_factorial hp (log_div_lt_bound N B k p hNB)]
          have hI : Ico 1 (B + 1) = Icc 1 B := by
            ext i
            simp only [mem_Ico, mem_Icc]
            omega
          rw [hI]
    _ = ∑ k ∈ Icc 1 N, ∑ i ∈ Icc 1 B, k * ((N / k) / p ^ i) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
    _ = ∑ k ∈ Icc 1 N, ∑ i ∈ Icc 1 B, k * (N / (k * p ^ i)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro i hi
          rw [Nat.div_div_eq_div_mul]
    _ = ∑ i ∈ Icc 1 B, ∑ k ∈ Icc 1 N, k * (N / (k * p ^ i)) := by
          rw [Finset.sum_comm]

lemma inner_sum_eq_floor (N d : ℕ) :
    (∑ k ∈ Icc 1 N, k * (N / (k * d))) =
      ∑ k ∈ Icc 1 (N / d), k * ((N / d) / k) := by
  have hrewrite : (∑ k ∈ Icc 1 N, k * (N / (k * d))) =
      ∑ k ∈ Icc 1 N, k * ((N / d) / k) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    rw [Nat.div_div_eq_div_mul]
    rw [mul_comm]
  rw [hrewrite]
  have hm : N / d ≤ N := Nat.div_le_self N d
  have hsub : Icc 1 (N / d) ⊆ Icc 1 N := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hm⟩
  rw [Finset.sum_subset hsub]
  intro k hkN hknot
  have hkgt : N / d < k := by
    by_contra hle
    exact hknot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hkN).1, Nat.le_of_not_gt hle⟩)
  rw [Nat.div_eq_of_lt hkgt]
  simp


lemma a_factorization (N p : ℕ) :
    (a N).factorization p = (numerator N).factorization p - (denominator N).factorization p := by
  have ha : a N = numerator N / denominator N := by
    simp [a, numerator, denominator]
  rw [ha, Nat.factorization_div (denominator_dvd_numerator N)]
  rfl

lemma numerator_factorization_block (n p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    (numerator (n * p)).factorization p = (numerator (n * p + k)).factorization p := by
  let B := n * p + k
  have hle : n * p ≤ B := by simp [B]
  rw [numerator_factorization_formula_bound (n * p) B p hp hle,
      numerator_factorization_formula_bound (n * p + k) B p hp (le_rfl)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
  have hdiv := div_pow_eq_of_small n p k i hp.pos hk hi1
  rw [hdiv]

lemma denominator_factorization_block (n p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
    (denominator (n * p)).factorization p = (denominator (n * p + k)).factorization p := by
  let B := n * p + k
  have hle : n * p ≤ B := by simp [B]
  rw [denominator_factorization_formula_bound (n * p) B p hp hle,
      denominator_factorization_formula_bound (n * p + k) B p hp (le_rfl)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
  have hdiv := div_pow_eq_of_small n p k i hp.pos hk hi1
  rw [inner_sum_eq_floor (n * p) (p ^ i), inner_sum_eq_floor (n * p + k) (p ^ i)]
  rw [hdiv]

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
    (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  have _hn : 0 < n := hn
  rw [a_factorization, a_factorization]
  rw [numerator_factorization_block n p k hp hk, denominator_factorization_block n p k hp hk]
















