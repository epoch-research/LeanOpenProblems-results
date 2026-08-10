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

namespace OEIS_A129365

/-- Numerator A092287. -/
def Nn (m : ℕ) : ℕ := (Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k
/-- Denominator A129364. -/
def Dd (m : ℕ) : ℕ := (Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k

lemma a_eq (m : ℕ) : a m = Nn m / Dd m := rfl

lemma Nn_ne_zero (m : ℕ) : Nn m ≠ 0 := by
  unfold Nn
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [Finset.mem_Icc] at hj
  exact (Nat.gcd_pos_iff.mpr (Or.inl hj.1)).ne'

lemma Dd_ne_zero (m : ℕ) : Dd m ≠ 0 := by
  unfold Dd
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact pow_ne_zero _ (Nat.factorial_ne_zero _)

lemma sum_indic_le (c b : ℕ) (hc : c < b) :
    ∑ i ∈ Ico 1 b, (if i ≤ c then (1:ℕ) else 0) = c := by
  have hfilt : (Ico 1 b).filter (· ≤ c) = Ico 1 (c+1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.lt_succ_iff]
    omega
  rw [Finset.sum_boole, hfilt, Nat.card_Ico]
  simp

lemma count_dvd (m d : ℕ) :
    ∑ j ∈ Icc 1 m, (if d ∣ j then (1:ℕ) else 0) = m / d := by
  rw [Finset.sum_boole]
  have hset : Icc 1 m = Ioc 0 m := by
    ext x; simp [Nat.lt_iff_add_one_le]
  rw [hset, ← Nat.Ioc_filter_dvd_card_eq_div]
  simp

lemma val_N (q : ℕ) (hq : q.Prime) (m b : ℕ) (hb : Nat.log q m < b) :
    (Nn m).factorization q = ∑ i ∈ Ico 1 b, (m / q^i)^2 := by
  have hgcd_ne : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m, Nat.gcd j k ≠ 0 := by
    intro j hj k hk
    simp only [Finset.mem_Icc] at hj
    exact (Nat.gcd_pos_iff.mpr (Or.inl hj.1)).ne'
  have step1 : (Nn m).factorization q
      = ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, min (j.factorization q) (k.factorization q) := by
    unfold Nn
    rw [Nat.factorization_prod_apply (fun j hj =>
        Finset.prod_ne_zero_iff.mpr (fun k hk => hgcd_ne j hj k hk))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.factorization_prod_apply (fun k hk => hgcd_ne j hj k hk)]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hj hk
    rw [Nat.factorization_gcd (by omega) (by omega), Finsupp.inf_apply]
  rw [step1]
  have step2 : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m,
      min (j.factorization q) (k.factorization q)
        = ∑ i ∈ Ico 1 b, (if q^i ∣ j ∧ q^i ∣ k then (1:ℕ) else 0) := by
    intro j hj k hk
    simp only [Finset.mem_Icc] at hj hk
    have hjne : j ≠ 0 := by omega
    have hkne : k ≠ 0 := by omega
    have hcond : ∀ i, (q^i ∣ j ∧ q^i ∣ k) ↔ i ≤ min (j.factorization q) (k.factorization q) := by
      intro i
      rw [hq.pow_dvd_iff_le_factorization hjne, hq.pow_dvd_iff_le_factorization hkne, le_min_iff]
    have hjlog : j.factorization q ≤ Nat.log q m := by
      have h1 : j.factorization q ≤ Nat.log q j :=
        Nat.le_log_of_pow_le hq.one_lt (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd j q))
      exact h1.trans (Nat.log_mono_right hj.2)
    have hlt : min (j.factorization q) (k.factorization q) < b :=
      Nat.lt_of_le_of_lt (min_le_left _ _) (Nat.lt_of_le_of_lt hjlog hb)
    symm
    calc ∑ i ∈ Ico 1 b, (if q^i ∣ j ∧ q^i ∣ k then (1:ℕ) else 0)
        = ∑ i ∈ Ico 1 b, (if i ≤ min (j.factorization q) (k.factorization q) then (1:ℕ) else 0) := by
          apply Finset.sum_congr rfl; intro i _; rw [if_congr (hcond i) rfl rfl]
      _ = min (j.factorization q) (k.factorization q) := sum_indic_le _ _ hlt
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => step2 j hj k hk))]
  -- swap sums to pull i outermost
  calc ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, ∑ i ∈ Ico 1 b, (if q^i ∣ j ∧ q^i ∣ k then (1:ℕ) else 0)
      = ∑ j ∈ Icc 1 m, ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 m, (if q^i ∣ j ∧ q^i ∣ k then (1:ℕ) else 0) := by
        apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]
    _ = ∑ i ∈ Ico 1 b, ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, (if q^i ∣ j ∧ q^i ∣ k then (1:ℕ) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i ∈ Ico 1 b, (m / q^i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        have hsplit : ∀ j k : ℕ, (if q^i ∣ j ∧ q^i ∣ k then (1:ℕ) else 0)
            = (if q^i ∣ j then 1 else 0) * (if q^i ∣ k then 1 else 0) := by
          intro j k; by_cases h1 : q^i ∣ j <;> by_cases h2 : q^i ∣ k <;> simp [h1, h2]
        simp_rw [hsplit]
        rw [← Finset.sum_mul_sum, count_dvd, pow_two]

lemma val_D (q : ℕ) (hq : q.Prime) (m b : ℕ) (hb : Nat.log q m < b) :
    (Dd m).factorization q = ∑ i ∈ Ico 1 b, ∑ k ∈ Icc 1 (m / q^i), k * ((m/q^i)/k) := by
  unfold Dd
  rw [Nat.factorization_prod_apply (fun k hk => pow_ne_zero _ (Nat.factorial_ne_zero _))]
  have hterm : ∀ k ∈ Icc 1 m, ((m/k)!^k).factorization q
      = k * ∑ i ∈ Ico 1 b, (m/k) / q^i := by
    intro k hk
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    congr 1
    apply Nat.factorization_factorial hq
    exact Nat.lt_of_le_of_lt (Nat.log_mono_right (Nat.div_le_self m k)) hb
  rw [Finset.sum_congr rfl hterm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hdiveq : ∀ k, (m/k)/q^i = (m/q^i)/k := by
    intro k; rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [hdiveq]
  symm
  apply Finset.sum_subset
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans (Nat.div_le_self m (q^i))⟩
  · intro x hx hxnot
    simp only [Finset.mem_Icc, not_and, not_le] at hx hxnot
    rw [Nat.div_eq_of_lt (hxnot hx.1), Nat.mul_zero]

lemma S_le (M : ℕ) : ∑ k ∈ Icc 1 M, k * (M/k) ≤ M^2 := by
  calc ∑ k ∈ Icc 1 M, k * (M/k) ≤ ∑ k ∈ Icc 1 M, M := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Nat.mul_comm]
        exact Nat.div_mul_le_self M k
    _ = M^2 := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel, ← pow_two]

lemma Dd_dvd_Nn (m : ℕ) : Dd m ∣ Nn m := by
  rw [← Nat.factorization_le_iff_dvd (Dd_ne_zero m) (Nn_ne_zero m), Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  · rw [val_D q hq m (m+1) (Nat.lt_succ_of_le (Nat.log_le_self q m)),
        val_N q hq m (m+1) (Nat.lt_succ_of_le (Nat.log_le_self q m))]
    apply Finset.sum_le_sum
    intro i _
    exact S_le (m / q^i)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq]
    exact Nat.zero_le _

lemma floor_block (p n j i : ℕ) (hp : 0 < p) (hj : j < p) (hi : 1 ≤ i) :
    (n*p + j) / p^i = (n*p) / p^i := by
  have hpi : 0 < p^i := pow_pos hp i
  have hdm : n*p = p^i * ((n*p)/p^i) + (n*p)%p^i := (Nat.div_add_mod (n*p) (p^i)).symm
  have hpdvd : p ∣ p^i := dvd_pow_self p (by omega)
  have hr_dvd : p ∣ (n*p)%p^i := (Nat.dvd_mod_iff hpdvd).mpr ⟨n, by ring⟩
  have hr_lt : (n*p)%p^i < p^i := Nat.mod_lt _ hpi
  have hrp : (n*p)%p^i + p ≤ p^i := by
    obtain ⟨c, hc⟩ := hpdvd
    obtain ⟨d, hd⟩ := hr_dvd
    have hdc : d < c := by
      apply Nat.lt_of_mul_lt_mul_left (a := p)
      rw [← hd, ← hc]; exact hr_lt
    rw [hd, hc]
    calc p * d + p = p * (d+1) := by ring
      _ ≤ p * c := Nat.mul_le_mul_left p hdc
  have hlt2 : (n*p)%p^i + j < p^i := by omega
  have hkey : n*p + j = p^i * ((n*p)/p^i) + ((n*p)%p^i + j) := by
    rw [← Nat.add_assoc, ← hdm]
  rw [hkey, Nat.mul_add_div hpi, Nat.div_eq_of_lt hlt2, Nat.add_zero]

end OEIS_A129365

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  have hp0 : 0 < p := hp.pos
  set b := n*p + k + 1 with hbdef
  have hlog0 : Nat.log p (n*p) < b := by
    have := Nat.log_le_self p (n*p); omega
  have hlog1 : Nat.log p (n*p+k) < b := by
    have := Nat.log_le_self p (n*p+k); omega
  have key : ∀ m, (a m).factorization p
      = (OEIS_A129365.Nn m).factorization p - (OEIS_A129365.Dd m).factorization p := by
    intro m
    rw [OEIS_A129365.a_eq, Nat.factorization_div (OEIS_A129365.Dd_dvd_Nn m), Finsupp.tsub_apply]
  rw [key, key]
  have eN : (OEIS_A129365.Nn (n*p)).factorization p
      = (OEIS_A129365.Nn (n*p+k)).factorization p := by
    rw [OEIS_A129365.val_N p hp (n*p) b hlog0, OEIS_A129365.val_N p hp (n*p+k) b hlog1]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    rw [OEIS_A129365.floor_block p n k i hp0 hk hi.1]
  have eD : (OEIS_A129365.Dd (n*p)).factorization p
      = (OEIS_A129365.Dd (n*p+k)).factorization p := by
    rw [OEIS_A129365.val_D p hp (n*p) b hlog0, OEIS_A129365.val_D p hp (n*p+k) b hlog1]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    rw [OEIS_A129365.floor_block p n k i hp0 hk hi.1]
  rw [eN, eD]
