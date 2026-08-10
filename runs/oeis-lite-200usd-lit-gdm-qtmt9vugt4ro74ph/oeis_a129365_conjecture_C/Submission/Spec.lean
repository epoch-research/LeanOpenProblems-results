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

def num (n : ℕ) : ℕ :=
  (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k

def den (n : ℕ) : ℕ :=
  (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma a_def (n : ℕ) : a n = num n / den n := rfl

lemma sum_div_le (n M : ℕ) (hM : M ≤ n) :
  ∑ k ∈ Icc 1 n, k * (M / k) ≤ M ^ 2 := by
  rcases eq_or_ne M 0 with (rfl | hM0)
  · simp
  have h_split : Icc 1 n = Icc 1 M ∪ Ioc M n := by
    apply Finset.ext; intro x; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have h_disj : Disjoint (Icc 1 M) (Ioc M n) := by
    apply disjoint_iff_ne.mpr; intro x hx y hy hxy; simp only [mem_Icc, mem_Ioc] at hx hy; omega
  rw [h_split, sum_union h_disj]
  have h_zero : ∑ k ∈ Ioc M n, k * (M / k) = 0 := by
    apply sum_eq_zero; intro k hk; simp only [mem_Ioc] at hk; have : M / k = 0 := Nat.div_eq_of_lt hk.1; rw [this, mul_zero]
  rw [h_zero, add_zero]
  have h_le : ∑ k ∈ Icc 1 M, k * (M / k) ≤ ∑ k ∈ Icc 1 M, M := by
    apply sum_le_sum; intro k hk; simp only [mem_Icc] at hk; apply Nat.mul_div_le
  apply h_le.trans
  rw [sum_const, card_Icc]
  simp only [smul_eq_mul]
  have : M + 1 - 1 = M := by omega
  rw [this, sq]

lemma factorial_val (n k q : ℕ) (hq : Nat.Prime q) (hk : 1 ≤ k) :
  padicValNat q (Nat.factorial (n / k)) = ∑ i ∈ Ico 1 (n + 2), (n / k) / q ^ i := by
  have hq_prime : Fact q.Prime := ⟨hq⟩
  apply padicValNat_factorial
  have hq2 : 1 < q := hq.one_lt
  have h_le : n / k ≤ n := Nat.div_le_self _ _
  have h_log : log q (n / k) ≤ log q n := log_mono_right h_le
  have h_log_lt : log q n < n + 1 := by
    apply log_lt_of_lt_pow' (Nat.succ_ne_zero n)
    have : q ^ n ≤ q ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : n < q ^ n := Nat.lt_pow_self hq.one_lt
    exact h2.trans_le this
  omega

lemma card_multiples_Icc (m D : ℕ) :
  ∑ j ∈ Icc 1 m, (if D ∣ j then 1 else 0) = m / D := by
  have h_eq : Icc 1 m = Ioc 0 m := by apply Finset.ext; intro x; simp only [mem_Icc, mem_Ioc]; omega
  rw [h_eq]
  have h_sum_card : ∑ j ∈ Ioc 0 m, (if D ∣ j then 1 else 0) = ((Ioc 0 m).filter (fun j => D ∣ j)).card := by rw [sum_boole]; rfl
  rw [h_sum_card, Ioc_filter_dvd_card_eq_div]

lemma gcd_val_sum (m j k q : ℕ) (hq : Nat.Prime q) (hj : j ∈ Icc 1 m) (hk : k ∈ Icc 1 m) :
  padicValNat q (Nat.gcd j k) = ∑ i ∈ Ico 1 (m + 2), if q ^ i ∣ Nat.gcd j k then 1 else 0 := by
  have hq_prime : Fact q.Prime := ⟨hq⟩
  rw [← factorization_def _ hq]
  have h_gcd_pos : 0 < Nat.gcd j k := by apply Nat.gcd_pos_of_pos_left; have : 1 ≤ j := (mem_Icc.mp hj).1; omega
  have h_gcd_lt : Nat.gcd j k < q ^ (m + 2) := by
    have h_le_m : Nat.gcd j k ≤ m := by
      have hj1 : 1 ≤ j := (mem_Icc.mp hj).1; have hj2 : j ≤ m := (mem_Icc.mp hj).2
      exact (Nat.le_of_dvd hj1 (Nat.gcd_dvd_left j k)).trans hj2
    have h_pow : m < q ^ (m + 2) := by
      have h2 : m < 2 ^ (m + 1) := by
        have : m < 2 ^ m := Nat.lt_pow_self (by decide); have h_pow_le : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        exact this.trans_le h_pow_le
      have h3 : 2 ^ (m + 1) < 2 ^ (m + 2) := Nat.pow_lt_pow_succ (by decide)
      have h_pow_q : 2 ^ (m + 2) ≤ q ^ (m + 2) := Nat.pow_le_pow_left hq.two_le _
      have h_pow_2 : m < 2 ^ (m + 2) := h2.trans h3
      exact h_pow_2.trans_le h_pow_q
    omega
  rw [factorization_eq_card_pow_dvd_of_lt hq h_gcd_pos h_gcd_lt, sum_boole]; simp

lemma val_den (m q : ℕ) (hq : Nat.Prime q) :
  padicValNat q (den m) = ∑ k ∈ Icc 1 m, k * padicValNat q (Nat.factorial (m / k)) := by
  have hq_prime : Fact q.Prime := ⟨hq⟩; rw [← factorization_def _ hq]
  have h_nz : ∀ k ∈ Icc 1 m, (Nat.factorial (m / k)) ^ k ≠ 0 := by intro k hk; apply pow_ne_zero; exact Nat.factorial_ne_zero _
  rw [den, factorization_prod h_nz]; simp [factorization_pow, factorization_def _ hq]

lemma val_num (m q : ℕ) (hq : Nat.Prime q) :
  padicValNat q (num m) = ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, padicValNat q (Nat.gcd j k) := by
  rw [← factorization_def _ hq]
  have h_nz1 : ∀ j ∈ Icc 1 m, (Icc 1 m).prod (fun k => Nat.gcd j k) ≠ 0 := by
    intro j hj; rw [prod_ne_zero_iff]; intro k hk; apply Nat.gcd_ne_zero_left; have hj1 : 1 ≤ j := (mem_Icc.mp hj).1; omega
  rw [num, factorization_prod h_nz1]
  have h_nz2 : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, Nat.gcd j k ≠ 0 := by intro j hj k hk; apply Nat.gcd_ne_zero_left; have hj1 : 1 ≤ j := (mem_Icc.mp hj).1; omega
  have h_inner : ∀ j ∈ Icc 1 m, (((Icc 1 m).prod fun k => Nat.gcd j k).factorization) q = ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization q := by
    intro j hj; rw [factorization_prod (by intro k hk; exact h_nz2 j hj k hk)]; simp
  have h_sum : (∑ j ∈ Icc 1 m, ((Icc 1 m).prod fun k => Nat.gcd j k).factorization) q = ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (Nat.gcd j k).factorization q := by
    simp; apply sum_congr rfl; intro j hj; exact h_inner j hj
  rw [h_sum]; simp_rw [factorization_def _ hq]

lemma div_div_comm (m k d : ℕ) : (m / k) / d = (m / d) / k := by
  rcases eq_or_ne k 0 with (rfl | hk); · simp
  rcases eq_or_ne d 0 with (rfl | hd); · simp
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]

lemma den_le_num_lhs (m q : ℕ) (hq : Nat.Prime q) :
  padicValNat q (den m) ≤ ∑ i ∈ Ico 1 (m + 2), (m / q ^ i) ^ 2 := by
  rw [val_den m q hq]
  have h_val : ∀ k ∈ Icc 1 m, padicValNat q (Nat.factorial (m / k)) = ∑ i ∈ Ico 1 (m + 2), (m / k) / q ^ i := by
    intro k hk; have hk1 : 1 ≤ k := (mem_Icc.mp hk).1; exact factorial_val m k q hq hk1
  have h_eq1 : ∑ k ∈ Icc 1 m, k * padicValNat q (Nat.factorial (m / k)) = ∑ k ∈ Icc 1 m, k * ∑ i ∈ Ico 1 (m + 2), (m / k) / q ^ i := by
    apply sum_congr rfl; intro k hk; rw [h_val k hk]
  rw [h_eq1]
  have h_eq2 : ∀ k ∈ Icc 1 m, k * ∑ i ∈ Ico 1 (m + 2), (m / k) / q ^ i = ∑ i ∈ Ico 1 (m + 2), k * ((m / k) / q ^ i) := by intro k hk; rw [mul_sum]
  have h_eq3 : ∑ k ∈ Icc 1 m, k * ∑ i ∈ Ico 1 (m + 2), (m / k) / q ^ i = ∑ k ∈ Icc 1 m, ∑ i ∈ Ico 1 (m + 2), k * ((m / k) / q ^ i) := by
    apply sum_congr rfl; intro k hk; exact h_eq2 k hk
  rw [h_eq3, sum_comm]
  apply sum_le_sum; intro i hi
  have h_div : ∀ k ∈ Icc 1 m, k * ((m / k) / q ^ i) = k * ((m / q ^ i) / k) := by intro k hk; rw [div_div_comm]
  have h_eq4 : ∑ k ∈ Icc 1 m, k * ((m / k) / q ^ i) = ∑ k ∈ Icc 1 m, k * ((m / q ^ i) / k) := by apply sum_congr rfl; intro k hk; exact h_div k hk
  rw [h_eq4]
  have h_le_div : m / q ^ i ≤ m := Nat.div_le_self _ _
  exact sum_div_le m (m / q ^ i) h_le_div

lemma num_val_eq (m q : ℕ) (hq : Nat.Prime q) :
  padicValNat q (num m) = ∑ i ∈ Ico 1 (m + 2), (m / q ^ i) ^ 2 := by
  rw [val_num m q hq]
  have h_gcd : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, padicValNat q (Nat.gcd j k) = ∑ i ∈ Ico 1 (m + 2), if q ^ i ∣ Nat.gcd j k then 1 else 0 := by
    intro j hj k hk; exact gcd_val_sum m j k q hq hj hk
  have h_sum1 : ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, padicValNat q (Nat.gcd j k) = ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, ∑ i ∈ Ico 1 (m + 2), if q ^ i ∣ Nat.gcd j k then 1 else 0 := by
    apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro k hk; exact h_gcd j hj k hk
  rw [h_sum1]
  have h_swap1 : ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, ∑ i ∈ Ico 1 (m + 2), (if q ^ i ∣ Nat.gcd j k then 1 else 0) = ∑ j ∈ Icc 1 m, ∑ i ∈ Ico 1 (m + 2), ∑ k ∈ Icc 1 m, (if q ^ i ∣ Nat.gcd j k then 1 else 0) := by
    apply sum_congr rfl; intro j hj; rw [sum_comm]
  rw [h_swap1, sum_comm]
  apply sum_congr rfl; intro i hi
  have h_dvd : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, (if q ^ i ∣ Nat.gcd j k then 1 else 0) = (if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0) := by
    intro j hj k hk
    by_cases h1 : q ^ i ∣ j <;> by_cases h2 : q ^ i ∣ k
    · have h_gcd : q ^ i ∣ Nat.gcd j k := Nat.dvd_gcd h1 h2
      simp [h1, h2, h_gcd]
    · have h_gcd : ¬ q ^ i ∣ Nat.gcd j k := by
        intro h
        have := (dvd_gcd_iff.mp h).2
        exact h2 this
      simp [h1, h2, h_gcd]
    · have h_gcd : ¬ q ^ i ∣ Nat.gcd j k := by
        intro h
        have := (dvd_gcd_iff.mp h).1
        exact h1 this
      simp [h1, h2, h_gcd]
    · have h_gcd : ¬ q ^ i ∣ Nat.gcd j k := by
        intro h
        have := (dvd_gcd_iff.mp h).1
        exact h1 this
      simp [h1, h2, h_gcd]
  have h_sum2 : ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (if q ^ i ∣ Nat.gcd j k then 1 else 0) = ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, ((if q ^ i ∣ j then 1 else 0) * (if q ^ i ∣ k then 1 else 0)) := by
    apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro k hk; exact h_dvd j hj k hk
  rw [h_sum2]
  simp_rw [← mul_sum]; rw [← sum_mul, card_multiples_Icc m (q ^ i), sq]

lemma den_le_num (m q : ℕ) (hq : Nat.Prime q) :
  padicValNat q (den m) ≤ padicValNat q (num m) := by
  have h_lhs := den_le_num_lhs m q hq; rw [← num_val_eq m q hq] at h_lhs; exact h_lhs

lemma div_pow_eq (n p k i : ℕ) (hp : 1 < p) (hk : k < p) (hi : 1 ≤ i) :
  (n * p + k) / p ^ i = (n * p) / p ^ i := by
  have h_pow : p ^ i = p * p ^ (i - 1) := by
    rw [mul_comm]
    rw [← pow_succ, Nat.sub_add_cancel hi]
  rw [h_pow]
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have h_add : (n * p + k) / p = n := by
    rw [add_comm, Nat.add_mul_div_right _ _ (by omega)]
    have : k / p = 0 := Nat.div_eq_of_lt hk
    rw [this, zero_add]
  have hp_pos : 0 < p := by omega
  have h_mul : n * p / p = n := Nat.mul_div_cancel n hp_pos
  rw [h_add, h_mul]

lemma sum_div_pow_const (A B B' p : ℕ) (hB1 : 1 ≤ B) (hB : B ≤ B') (h_zero : ∀ i, B ≤ i → A / p ^ i = 0) :
  ∑ i ∈ Ico 1 B, (A / p ^ i) ^ 2 = ∑ i ∈ Ico 1 B', (A / p ^ i) ^ 2 := by
  have h_split : Ico 1 B' = Ico 1 B ∪ Ico B B' := by
    apply Finset.ext; intro x; simp only [mem_Ico, mem_union]; omega
  have h_disj : Disjoint (Ico 1 B) (Ico B B') := by
    apply disjoint_iff_ne.mpr; intro x hx y hy hxy; simp only [mem_Ico] at hx hy; omega
  rw [h_split, sum_union h_disj]
  have h_zero_sum : ∑ i ∈ Ico B B', (A / p ^ i) ^ 2 = 0 := by
    apply sum_eq_zero; intro i hi; simp only [mem_Ico] at hi
    have : A / p ^ i = 0 := h_zero i hi.1
    rw [this, zero_pow (by omega)]
  rw [h_zero_sum, add_zero]

lemma sum_div_pow_const_linear (A B B' p : ℕ) (hB1 : 1 ≤ B) (hB : B ≤ B') (h_zero : ∀ i, B ≤ i → A / p ^ i = 0) :
  ∑ i ∈ Ico 1 B, A / p ^ i = ∑ i ∈ Ico 1 B', A / p ^ i := by
  have h_split : Ico 1 B' = Ico 1 B ∪ Ico B B' := by
    apply Finset.ext; intro x; simp only [mem_Ico, mem_union]; omega
  have h_disj : Disjoint (Ico 1 B) (Ico B B') := by
    apply disjoint_iff_ne.mpr; intro x hx y hy hxy; simp only [mem_Ico] at hx hy; omega
  rw [h_split, sum_union h_disj]
  have h_zero_sum : ∑ i ∈ Ico B B', A / p ^ i = 0 := by
    apply sum_eq_zero; intro i hi; simp only [mem_Ico] at hi
    exact h_zero i hi.1
  rw [h_zero_sum, add_zero]

lemma div_zero_of_large (A p i : ℕ) (hp : 1 < p) (hi : A + 2 ≤ i) : A / p ^ i = 0 := by
  apply Nat.div_eq_of_lt
  have h_pow_gt : A < p ^ i := by
    have h1 : A < p ^ (A + 2) := by
      have : A < 2 ^ (A + 2) := by
        have : A < 2 ^ A := Nat.lt_pow_self (by decide)
        have h2 : 2 ^ A < 2 ^ (A + 2) := by
          have : A < A + 2 := by omega
          exact Nat.pow_lt_pow_right (by decide) this
        exact this.trans h2
      have h_le : 2 ≤ p := by omega
      have hq : 2 ^ (A + 2) ≤ p ^ (A + 2) := pow_le_pow_left' h_le (A + 2)
      exact this.trans_le hq
    have h2 : p ^ (A + 2) ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi
    exact h1.trans_le h2
  exact h_pow_gt

lemma num_val_eq_of_k (n p k : ℕ) (hp : Nat.Prime p) (hk : k < p) :
  padicValNat p (num (n * p)) = padicValNat p (num (n * p + k)) := by
  rw [num_val_eq (n * p) p hp]
  rw [num_val_eq (n * p + k) p hp]
  have h_le : n * p + 2 ≤ n * p + k + 2 := by omega
  have h_b1 : 1 ≤ n * p + 2 := by omega
  have h_zero : ∀ i, n * p + 2 ≤ i → n * p / p ^ i = 0 := by
    intro i hi
    exact div_zero_of_large (n * p) p i hp.one_lt hi
  rw [sum_div_pow_const (n * p) (n * p + 2) (n * p + k + 2) p h_b1 h_le h_zero]
  apply sum_congr rfl
  intro i hi
  simp only [mem_Ico] at hi
  rw [div_pow_eq n p k i hp.one_lt hk hi.1]

lemma div_eq_one_of_le_of_lt (a b : ℕ) (hb : 0 < b) (h1 : b ≤ a) (h2 : a < 2 * b) : a / b = 1 := by
  have h3 : 1 ≤ a / b := by
    rw [Nat.le_div_iff_mul_le hb]
    omega
  have h4 : a / b < 2 := by
    rw [Nat.div_lt_iff_lt_mul hb]
    omega
  omega

lemma val_factorial_div_large (n p k j : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) (hj : n * p < j) (hj2 : j ≤ n * p + k) :
  padicValNat p (Nat.factorial ((n * p + k) / j)) = 0 := by
  have hj_pos : 0 < j := by omega
  have h_div : (n * p + k) / j = 1 := by
    apply div_eq_one_of_le_of_lt (n * p + k) j hj_pos hj2
    have : n * p + k < (n + 1) * p := by
      rw [add_mul, one_mul]
      omega
    have h_2j : (n + 1) * p ≤ 2 * j := by
      have : (n + 1) * p ≤ 2 * (n * p) := by
        have hp_pos : 0 < p := hp.pos
        rw [← mul_assoc]
        apply Nat.mul_le_mul_right
        omega
      have h_2j' : 2 * (n * p) < 2 * j := by
        apply Nat.mul_lt_mul_of_pos_left hj (by decide)
      omega
    omega
  rw [h_div]
  simp

lemma factorial_val_eq_of_k (n p k j : ℕ) (hp : Nat.Prime p) (hk : k < p) (hj : j ∈ Icc 1 (n * p)) :
  padicValNat p (Nat.factorial ((n * p + k) / j)) = padicValNat p (Nat.factorial ((n * p) / j)) := by
  have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
  rw [factorial_val (n * p + k) j p hp hj1]
  rw [factorial_val (n * p) j p hp hj1]
  have h_le : n * p + 2 ≤ n * p + k + 2 := by omega
  have h_b1 : 1 ≤ n * p + 2 := by omega
  have h_zero : ∀ i, n * p + 2 ≤ i → ((n * p) / j) / p ^ i = 0 := by
    intro i hi
    rw [div_div_comm]
    have : (n * p) / p ^ i = 0 := div_zero_of_large (n * p) p i hp.one_lt hi
    rw [this, Nat.zero_div]
  rw [sum_div_pow_const_linear ((n * p) / j) (n * p + 2) (n * p + k + 2) p h_b1 h_le h_zero]
  apply sum_congr rfl
  intro i hi
  simp only [mem_Ico] at hi
  rw [div_div_comm (n * p + k) j (p ^ i), div_div_comm (n * p) j (p ^ i)]
  have : (n * p + k) / p ^ i = (n * p) / p ^ i := div_pow_eq n p k i hp.one_lt hk hi.1
  rw [this]

lemma den_val_eq_of_k (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  padicValNat p (den (n * p)) = padicValNat p (den (n * p + k)) := by
  rw [val_den (n * p) p hp]
  rw [val_den (n * p + k) p hp]
  have h_split : Icc 1 (n * p + k) = Icc 1 (n * p) ∪ Ioc (n * p) (n * p + k) := by
    apply Finset.ext; intro x; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have h_disj : Disjoint (Icc 1 (n * p)) (Ioc (n * p) (n * p + k)) := by
    apply disjoint_iff_ne.mpr; intro x hx y hy hxy; simp only [mem_Icc, mem_Ioc] at hx hy; omega
  rw [h_split, sum_union h_disj]
  have h_zero_sum : ∑ j ∈ Ioc (n * p) (n * p + k), j * padicValNat p (Nat.factorial ((n * p + k) / j)) = 0 := by
    apply sum_eq_zero; intro j hj; simp only [mem_Ioc] at hj
    have : padicValNat p (Nat.factorial ((n * p + k) / j)) = 0 := val_factorial_div_large n p k j hn hp hk hj.1 hj.2
    rw [this, mul_zero]
  rw [h_zero_sum, add_zero]
  apply sum_congr rfl
  intro j hj
  rw [factorial_val_eq_of_k n p k j hp hk hj]

lemma den_dvd_num (m : ℕ) : den m ∣ num m := by
  rcases eq_or_ne m 0 with rfl | hm
  · have h_den0 : den 0 = 1 := rfl
    have h_num0 : num 0 = 1 := rfl
    rw [h_den0, h_num0]
  · have h_den : den m ≠ 0 := by
      rw [den]
      apply prod_ne_zero_iff.mpr
      intro k hk
      apply pow_ne_zero
      exact Nat.factorial_ne_zero _
    have h_num : num m ≠ 0 := by
      rw [num]
      apply prod_ne_zero_iff.mpr
      intro j hj
      apply prod_ne_zero_iff.mpr
      intro k hk
      apply Nat.gcd_ne_zero_left
      have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
      omega
    rw [← factorization_le_iff_dvd h_den h_num]
    intro q
    by_cases hq : Nat.Prime q
    · rw [factorization_def (den m) hq, factorization_def (num m) hq]
      exact den_le_num m q hq
    · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
      exact Nat.zero_le _

lemma factorization_a (m p : ℕ) :
  (a m).factorization p = (num m).factorization p - (den m).factorization p := by
  rcases eq_or_ne m 0 with rfl | hm
  · have h1 : a 0 = 1 := rfl
    have h2 : den 0 = 1 := rfl
    have h3 : num 0 = 1 := rfl
    rw [h1, h2, h3]
    simp [Nat.factorization_one]
  · have h_den : den m ≠ 0 := by
      rw [den]
      apply prod_ne_zero_iff.mpr
      intro k hk
      apply pow_ne_zero
      exact Nat.factorial_ne_zero _
    have h_num : num m ≠ 0 := by
      rw [num]
      apply prod_ne_zero_iff.mpr
      intro j hj
      apply prod_ne_zero_iff.mpr
      intro k hk
      apply Nat.gcd_ne_zero_left
      have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
      omega
    have hdvd : den m ∣ num m := den_dvd_num m
    have ha_eq : num m = den m * a m := by
      rw [a_def]
      exact (Nat.mul_div_cancel' hdvd).symm
    have ha_nz : a m ≠ 0 := by
      intro ha0
      rw [ha0, mul_zero] at ha_eq
      exact h_num ha_eq
    have h_fac : (num m).factorization = (den m).factorization + (a m).factorization := by
      rw [ha_eq, Nat.factorization_mul h_den ha_nz]
    have h_fac_p : (num m).factorization p = (den m).factorization p + (a m).factorization p := by
      rw [h_fac]
      rfl
    omega

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  rw [factorization_a (n * p) p]
  rw [factorization_a (n * p + k) p]
  rw [factorization_def (num (n * p)) hp]
  rw [factorization_def (num (n * p + k)) hp]
  rw [factorization_def (den (n * p)) hp]
  rw [factorization_def (den (n * p + k)) hp]
  rw [num_val_eq_of_k n p k hp hk]
  rw [den_val_eq_of_k n p k hn hp hk]


