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


private def num (n : ℕ) : ℕ :=
  (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
private def den (n : ℕ) : ℕ :=
  (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

private lemma gcd_factorization_formula {n j k p : ℕ} (hp : p.Prime)
    (hj : j ∈ Icc 1 n) (hk : k ∈ Icc 1 n) :
    (Nat.gcd j k).factorization p =
      ∑ i ∈ Ico 1 (Nat.log p n + 1), if p ^ i ∣ Nat.gcd j k then 1 else 0 := by
  have hgpos : 0 < Nat.gcd j k := Nat.gcd_pos_of_pos_left _ (mem_Icc.mp hj).1
  have hlog : Nat.log p (Nat.gcd j k) < Nat.log p n + 1 := by
    apply lt_succ_of_le
    exact Nat.log_mono_right ((Nat.gcd_le_left k (mem_Icc.mp hj).1).trans (mem_Icc.mp hj).2)
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hgpos
    (Nat.lt_pow_of_log_lt hp.one_lt hlog)]
  exact Finset.card_filter _ _

private lemma count_dvd_Icc (n q : ℕ) :
    (∑ x ∈ Icc 1 n, if q ∣ x then 1 else 0) = n / q := by
  rw [← Finset.card_filter]
  rw [show Icc 1 n = Ioc 0 n by ext x; simp; omega]
  exact Nat.Ioc_filter_dvd_card_eq_div n q

private lemma num_factorization_formula (n p : ℕ) (hp : p.Prime) :
    (num n).factorization p =
      ∑ i ∈ Ico 1 (Nat.log p n + 1), (n / p ^ i) ^ 2 := by
  unfold num
  have hinner (j : ℕ) (hj : j ∈ Icc 1 n) :
      ∀ k ∈ Icc 1 n, Nat.gcd j k ≠ 0 := by
    intro k hk
    exact Nat.gcd_ne_zero_left (Nat.ne_of_gt (mem_Icc.mp hj).1)
  have houter : ∀ j ∈ Icc 1 n, (∏ k ∈ Icc 1 n, Nat.gcd j k) ≠ 0 := by
    intro j hj
    exact Finset.prod_ne_zero_iff.mpr (hinner j hj)
  rw [Nat.factorization_prod_apply houter]
  apply Eq.trans (Finset.sum_congr rfl fun j hj =>
    Nat.factorization_prod_apply (hinner j hj))
  apply Eq.trans (Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun k hk => gcd_factorization_formula hp hj hk)
  simp_rw [Finset.sum_comm (s := Icc 1 n) (t := Ico 1 (Nat.log p n + 1))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp_rw [Nat.dvd_gcd_iff]
  simp_rw [ite_and]
  rw [pow_two]
  calc
    _ = ∑ x ∈ Icc 1 n, (if p ^ i ∣ x then n / p ^ i else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : p ^ i ∣ x
      · simpa only [h, if_true] using count_dvd_Icc n (p ^ i)
      · simp [h]
    _ = (∑ x ∈ Icc 1 n, if p ^ i ∣ x then 1 else 0) * (n / p ^ i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : p ^ i ∣ x <;> simp [h]
    _ = _ := by rw [count_dvd_Icc]

private lemma den_factorization_formula (n p : ℕ) (hp : p.Prime) :
    (den n).factorization p =
      ∑ i ∈ Ico 1 (Nat.log p n + 1),
        ∑ k ∈ Icc 1 n, k * ((n / p ^ i) / k) := by
  unfold den
  have hterm : ∀ k ∈ Icc 1 n, (Nat.factorial (n / k)) ^ k ≠ 0 := by
    intro k hk
    positivity
  rw [Nat.factorization_prod_apply hterm]
  calc
    (∑ k ∈ Icc 1 n, ((Nat.factorial (n / k)) ^ k).factorization p) =
        ∑ k ∈ Icc 1 n, k * (Nat.factorial (n / k)).factorization p := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.factorization_pow]
          rfl
    _ = ∑ k ∈ Icc 1 n, k *
        (∑ i ∈ Ico 1 (Nat.log p n + 1), (n / k) / p ^ i) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          apply Nat.factorization_factorial hp
          exact (Nat.log_mono_right (Nat.div_le_self n k)).trans_lt (Nat.lt_succ_self _)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := Icc 1 n) (t := Ico 1 (Nat.log p n + 1))]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]


private lemma sum_mul_div_le_sq (M n : ℕ) (hMn : M ≤ n) :
    (∑ k ∈ Icc 1 n, k * (M / k)) ≤ M ^ 2 := by
  have hsub : Icc 1 M ⊆ Icc 1 n := Icc_subset_Icc le_rfl hMn
  have heq : (∑ k ∈ Icc 1 n, k * (M / k)) =
      ∑ k ∈ Icc 1 M, k * (M / k) := by
    symm
    apply Finset.sum_subset hsub
    intro k hkn hkM
    have hlt : M < k := by
      simp only [mem_Icc] at hkn hkM
      omega
    simp [Nat.div_eq_of_lt hlt]
  rw [heq, pow_two]
  calc
    (∑ k ∈ Icc 1 M, k * (M / k)) ≤ ∑ k ∈ Icc 1 M, M := by
      apply Finset.sum_le_sum
      intro k hk
      exact Nat.mul_div_le M k
    _ = M * M := by simp

private lemma den_dvd_num (n : ℕ) : den n ∣ num n := by
  have hden : den n ≠ 0 := by
    unfold den
    positivity
  have hnum : num n ≠ 0 := by
    unfold num
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact Nat.gcd_ne_zero_left (Nat.ne_of_gt (mem_Icc.mp hj).1)
  rw [← Nat.factorization_prime_le_iff_dvd hden hnum]
  intro p hp
  rw [den_factorization_formula n p hp, num_factorization_formula n p hp]
  apply Finset.sum_le_sum
  intro i hi
  exact sum_mul_div_le_sq (n / p ^ i) n (Nat.div_le_self _ _)


private lemma num_factorization_sum (n p : ℕ) :
    (num n).factorization p =
      ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (Nat.gcd j k).factorization p := by
  unfold num
  have hinner (j : ℕ) (hj : j ∈ Icc 1 n) :
      ∀ k ∈ Icc 1 n, Nat.gcd j k ≠ 0 := by
    intro k hk
    exact Nat.gcd_ne_zero_left (Nat.ne_of_gt (mem_Icc.mp hj).1)
  have houter : ∀ j ∈ Icc 1 n, (∏ k ∈ Icc 1 n, Nat.gcd j k) ≠ 0 := by
    intro j hj
    exact Finset.prod_ne_zero_iff.mpr (hinner j hj)
  rw [Nat.factorization_prod_apply houter]
  exact Finset.sum_congr rfl fun j hj => Nat.factorization_prod_apply (hinner j hj)

private lemma den_factorization_sum (n p : ℕ) :
    (den n).factorization p =
      ∑ k ∈ Icc 1 n, k * (Nat.factorial (n / k)).factorization p := by
  unfold den
  rw [Nat.factorization_prod_apply (by intro k hk; positivity)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.factorization_pow]
  rfl

private lemma factorization_gcd_eq_zero_of_not_dvd {m x p : ℕ}
    (hpm : ¬ p ∣ m) : (Nat.gcd m x).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro h
  exact hpm (h.trans (Nat.gcd_dvd_left m x))

private lemma num_factorization_succ (t p : ℕ) (hpm : ¬ p ∣ t + 1) :
    (num (t + 1)).factorization p = (num t).factorization p := by
  rw [num_factorization_sum, num_factorization_sum]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := t) (by omega)]
  have hcols :
      (∑ j ∈ Icc 1 t, ∑ k ∈ Icc 1 (t + 1), (Nat.gcd j k).factorization p) =
      ∑ j ∈ Icc 1 t, ((∑ k ∈ Icc 1 t, (Nat.gcd j k).factorization p) +
        (Nat.gcd j (t + 1)).factorization p) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Finset.sum_Icc_succ_top (a := 1) (b := t) (by omega) _
  rw [hcols]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := t) (by omega)]
  have hz₁ : ∀ j ∈ Icc 1 t, (Nat.gcd j (t + 1)).factorization p = 0 := by
    intro j hj
    rw [Nat.gcd_comm]
    exact factorization_gcd_eq_zero_of_not_dvd hpm
  have hz₂ : ∀ k ∈ Icc 1 t, (Nat.gcd (t + 1) k).factorization p = 0 := by
    intro k hk
    exact factorization_gcd_eq_zero_of_not_dvd hpm
  have hzp : (t + 1).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpm
  have hc :
      (∑ j ∈ Icc 1 t, ((∑ k ∈ Icc 1 t, (Nat.gcd j k).factorization p) +
        (Nat.gcd j (t + 1)).factorization p)) =
      ∑ j ∈ Icc 1 t, ∑ k ∈ Icc 1 t, (Nat.gcd j k).factorization p := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hz₁ j hj, add_zero]
  have hr : (∑ k ∈ Icc 1 t, (Nat.gcd (t + 1) k).factorization p) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact hz₂ k hk
  rw [hc, hr]
  simp [hzp]


private lemma factorial_div_factorization_succ (t k p : ℕ)
    (hpm : ¬ p ∣ t + 1) :
    (Nat.factorial ((t + 1) / k)).factorization p =
      (Nat.factorial (t / k)).factorization p := by
  by_cases hk : k ∣ t + 1
  · have hpq : ¬ p ∣ (t + 1) / k := by
      intro h
      exact hpm (h.trans (Nat.div_dvd_of_dvd hk))
    have hq : (t + 1) / k = t / k + 1 := by
      rw [Nat.succ_div, if_pos hk]
    have hpq' : ¬ p ∣ t / k + 1 := by rwa [← hq]
    rw [hq, Nat.factorial_succ,
      Nat.factorization_mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
    change (t / k + 1).factorization p +
      (Nat.factorial (t / k)).factorization p = _
    rw [Nat.factorization_eq_zero_of_not_dvd hpq', zero_add]
  · rw [Nat.succ_div, if_neg hk, add_zero]

private lemma den_factorization_succ (t p : ℕ) (hpm : ¬ p ∣ t + 1) :
    (den (t + 1)).factorization p = (den t).factorization p := by
  rw [den_factorization_sum, den_factorization_sum]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := t) (by omega)]
  have hold :
      (∑ k ∈ Icc 1 t, k * (Nat.factorial ((t + 1) / k)).factorization p) =
      ∑ k ∈ Icc 1 t, k * (Nat.factorial (t / k)).factorization p := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [factorial_div_factorization_succ t k p hpm]
  rw [hold]
  simp


private def aa (n : ℕ) : ℕ := num n / den n

private lemma aa_factorization (n p : ℕ) :
    (aa n).factorization p =
      (num n).factorization p - (den n).factorization p := by
  unfold aa
  rw [Nat.factorization_div (den_dvd_num n)]
  rfl

private lemma aa_factorization_succ (t p : ℕ) (hpm : ¬ p ∣ t + 1) :
    (aa (t + 1)).factorization p = (aa t).factorization p := by
  rw [aa_factorization, aa_factorization,
    num_factorization_succ t p hpm, den_factorization_succ t p hpm]


-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  change (aa (n * p)).factorization p = (aa (n * p + k)).factorization p
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k < p := by omega
      have hi := ih hk' 
      rw [hi]
      have hbase : p ∣ n * p := by
        simpa [mul_comm] using dvd_mul_right p n
      have hnot : ¬ p ∣ n * p + k + 1 := by
        intro hd
        have hdsmall : p ∣ k + 1 := by
          apply (Nat.dvd_add_iff_left hbase).mpr
          simpa [add_assoc, add_comm, add_left_comm] using hd
        have hle : p ≤ k + 1 := Nat.le_of_dvd (by omega) hdsmall
        omega
      simpa [add_assoc] using
        (aa_factorization_succ (n * p + k) p hnot).symm
