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

/- Setup: numerator and denominator of `a` -/

/-- Numerator of `a n`: `∏_{j=1}^n ∏_{k=1}^n gcd(j,k)`. -/
def aNum (n : ℕ) : ℕ :=
  (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k

/-- Denominator of `a n`: `∏_{k=1}^n (⌊n/k⌋!)^k`. -/
def aDen (n : ℕ) : ℕ :=
  (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma a_eq (n : ℕ) : a n = aNum n / aDen n := rfl

lemma aNum_pos (n : ℕ) : 0 < aNum n := by
  refine prod_pos fun j hj => prod_pos fun k _hk => ?_
  exact Nat.gcd_pos_of_pos_left _ (mem_Icc.mp hj).1

lemma aNum_ne_zero (n : ℕ) : aNum n ≠ 0 := (aNum_pos n).ne'

lemma aDen_pos (n : ℕ) : 0 < aDen n := by
  refine prod_pos fun k _hk => pow_pos ?_ _
  exact factorial_pos _

lemma aDen_ne_zero (n : ℕ) : aDen n ≠ 0 := (aDen_pos n).ne'

/- Arithmetic helpers -/

/-- Exactly `n / d` elements of `Icc 1 n` are multiples of `d`. -/
lemma card_Icc_filter_dvd (n d : ℕ) : #{x ∈ Icc 1 n | d ∣ x} = n / d := by
  have h : Icc 1 n = Ioc 0 n := Icc_succ_left_eq_Ioc 0 n
  rw [h]
  exact Ioc_filter_dvd_card_eq_div n d

/-- Indicator form of `min`. -/
lemma sum_indicator_eq_min (x y N : ℕ) (hx : x ≤ N) (_hy : y ≤ N) :
    ∑ i ∈ Icc 1 N, (if i ≤ x ∧ i ≤ y then 1 else 0) = min x y := by
  simp only [← le_min_iff]
  rw [sum_ite, sum_const, sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  have : {i ∈ Icc 1 N | i ≤ min x y} = Icc 1 (min x y) := by
    ext i
    simp only [mem_filter, mem_Icc]
    constructor
    · intro ⟨⟨h1, _hN⟩, hmin⟩
      exact ⟨h1, hmin⟩
    · intro ⟨h1, hmin⟩
      exact ⟨⟨h1, hmin.trans (le_trans (min_le_left x y) hx)⟩, hmin⟩
  rw [this, card_Icc]
  exact Nat.add_sub_cancel (min x y) 1

/-- `min(v_p(j), v_p(k))` as a sum of divisibility indicators. -/
lemma min_factorization_eq_sum (j k p N : ℕ) (hp : p.Prime) (hj : j ≠ 0) (hk : k ≠ 0)
    (hN : j.factorization p ≤ N ∧ k.factorization p ≤ N) :
    min (j.factorization p) (k.factorization p) =
      ∑ i ∈ Icc 1 N, if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
  rw [← sum_indicator_eq_min _ _ N hN.1 hN.2]
  refine sum_congr rfl fun i _hi => ?_
  have : (p ^ i ∣ j ∧ p ^ i ∣ k) ↔ (i ≤ j.factorization p ∧ i ≤ k.factorization p) := by
    simp [hp.pow_dvd_iff_le_factorization hj, hp.pow_dvd_iff_le_factorization hk]
  simp [this]

/-- The function `g(t) = ∑_{k=1}^t (t mod k)` (OEIS A004125). -/
def g (t : ℕ) : ℕ := ∑ k ∈ Icc 1 t, t % k

lemma g_zero : g 0 = 0 := by simp [g]

lemma sum_mul_div_le_sq (t : ℕ) : ∑ k ∈ Icc 1 t, k * (t / k) ≤ t ^ 2 := by
  have h : ∑ k ∈ Icc 1 t, k * (t / k) ≤ ∑ k ∈ Icc 1 t, t := by
    refine sum_le_sum fun k _hk => ?_
    rw [mul_comm]
    exact Nat.div_mul_le_self t k
  refine h.trans ?_
  rw [sum_const, card_Icc, nsmul_eq_mul, pow_two]
  have : t + 1 - 1 = t := by omega
  simp [this]

lemma g_eq_sub (t : ℕ) : g t = t ^ 2 - ∑ k ∈ Icc 1 t, k * (t / k) := by
  unfold g
  have hle : ∀ k ∈ Icc 1 t, k * (t / k) ≤ t := fun k _hk => by
    rw [mul_comm]
    exact Nat.div_mul_le_self t k
  have hmod : ∀ k ∈ Icc 1 t, t % k = t - k * (t / k) := fun k _hk => by
    calc
      t % k = t % k + k * (t / k) - k * (t / k) := (Nat.add_sub_cancel _ _).symm
      _ = t - k * (t / k) := by rw [Nat.mod_add_div]
  rw [sum_congr rfl hmod]
  rw [sum_tsub_distrib _ hle]
  congr 1
  rw [sum_const, card_Icc, nsmul_eq_mul, pow_two]
  have : t + 1 - 1 = t := by omega
  simp [this]

/- Factorization of the numerator -/

lemma factorization_inner_prod (n j p : ℕ) (hj : j ∈ Icc 1 n) :
    ((Icc 1 n).prod fun k => Nat.gcd j k).factorization p =
      ∑ k ∈ Icc 1 n, (Nat.gcd j k).factorization p := by
  refine factorization_prod_apply fun k _hk => ?_
  exact (Nat.gcd_pos_of_pos_left _ (mem_Icc.mp hj).1).ne'

lemma aNum_factorization (m p : ℕ) (hp : p.Prime) :
    (aNum m).factorization p = ∑ i ∈ Icc 1 m, (m / p ^ i) ^ 2 := by
  unfold aNum
  have hne : ∀ j ∈ Icc 1 m, ((Icc 1 m).prod fun k => Nat.gcd j k) ≠ 0 := by
    intro j hj
    refine prod_ne_zero_iff.mpr fun k _hk => ?_
    exact (Nat.gcd_pos_of_pos_left _ (mem_Icc.mp hj).1).ne'
  rw [factorization_prod_apply hne]
  refine Eq.trans (sum_congr rfl fun j hj => factorization_inner_prod m j p hj) ?_
  -- gcd factorization is the min of factorizations
  have hgcd : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m,
      (Nat.gcd j k).factorization p = min (j.factorization p) (k.factorization p) := by
    intro j hj k hk
    have hj0 : j ≠ 0 := (one_le_iff_ne_zero.mp (mem_Icc.mp hj).1)
    have hk0 : k ≠ 0 := (one_le_iff_ne_zero.mp (mem_Icc.mp hk).1)
    rw [factorization_gcd hj0 hk0, Finsupp.inf_apply]
  rw [sum_congr rfl fun j hj => sum_congr rfl fun k hk => hgcd j hj k hk]
  -- bound: factorization < the number itself ≤ m
  have hbound : ∀ x ∈ Icc 1 m, x.factorization p ≤ m := by
    intro x hx
    have hx0 : x ≠ 0 := (one_le_iff_ne_zero.mp (mem_Icc.mp hx).1)
    exact (factorization_lt p hx0).le.trans (mem_Icc.mp hx).2
  have hmin : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m,
      min (j.factorization p) (k.factorization p) =
        ∑ i ∈ Icc 1 m, if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0 := by
    intro j hj k hk
    refine min_factorization_eq_sum j k p m hp
      (one_le_iff_ne_zero.mp (mem_Icc.mp hj).1)
      (one_le_iff_ne_zero.mp (mem_Icc.mp hk).1) ?_
    exact ⟨hbound j hj, hbound k hk⟩
  rw [sum_congr rfl fun j hj => sum_congr rfl fun k hk => hmin j hj k hk]
  -- ∑_j ∑_k ∑_i ite = ∑_i ∑_j ∑_k ite
  rw [sum_congr rfl fun j _hj => sum_comm, sum_comm]
  refine sum_congr rfl fun i _hi => ?_
  -- ∑_j ∑_k 1_{p^i∣j} 1_{p^i∣k} = (#{j : p^i∣j})²
  have hsplit : ∀ j k : ℕ,
      (if p ^ i ∣ j ∧ p ^ i ∣ k then (1 : ℕ) else 0) =
        (if p ^ i ∣ j then 1 else 0) * (if p ^ i ∣ k then 1 else 0) := by
    intro j k
    split_ifs with h h1 h2 <;> simp_all
  rw [sum_congr rfl fun j _ => sum_congr rfl fun k _ => hsplit j k]
  rw [← sum_mul_sum]
  have hcard : ∀ s : Finset ℕ, ∑ x ∈ s, (if p ^ i ∣ x then (1 : ℕ) else 0) = #{x ∈ s | p ^ i ∣ x} := by
    intro s
    exact sum_boole (fun x => p ^ i ∣ x) s
  simp_rw [hcard, card_Icc_filter_dvd, pow_two]

/- Factorization of the denominator -/

lemma factorization_factorial_Icc (t p m : ℕ) (hp : p.Prime) (htm : t ≤ m) :
    t.factorial.factorization p = ∑ i ∈ Icc 1 m, t / p ^ i := by
  have hlog : log p t < m + 1 := by
    cases eq_or_ne t 0 with
    | inl ht =>
      subst ht
      simp
    | inr ht =>
      exact (log_lt_self p ht).trans_le (htm.trans (Nat.le_succ m))
  have hIco : Ico 1 (m + 1) = Icc 1 m := Ico_succ_right_eq_Icc 1 m
  rw [factorization_factorial hp hlog, hIco]

lemma aDen_factorization (m p : ℕ) (hp : p.Prime) :
    (aDen m).factorization p =
      ∑ i ∈ Icc 1 m, ∑ k ∈ Icc 1 (m / p ^ i), k * ((m / p ^ i) / k) := by
  unfold aDen
  have hne : ∀ k ∈ Icc 1 m, ((m / k).factorial) ^ k ≠ 0 := fun k _hk =>
    pow_ne_zero _ (factorial_ne_zero _)
  rw [factorization_prod_apply hne]
  have hpow : ∀ k ∈ Icc 1 m,
      (((m / k).factorial) ^ k).factorization p = k * (m / k).factorial.factorization p := by
    intro k _hk
    rw [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [sum_congr rfl hpow]
  have hfac : ∀ k ∈ Icc 1 m,
      (m / k).factorial.factorization p = ∑ i ∈ Icc 1 m, (m / k) / p ^ i := by
    intro k hk
    refine factorization_factorial_Icc (m / k) p m hp ?_
    exact Nat.div_le_self m k
  rw [sum_congr rfl fun k hk => by rw [hfac k hk]]
  simp_rw [Finset.mul_sum]
  have hdiv : ∀ k i, (m / k) / p ^ i = m / (k * p ^ i) := fun k i =>
    Nat.div_div_eq_div_mul m k (p ^ i)
  simp_rw [hdiv]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  -- restrict the k-sum to Icc 1 (m / p^i)
  have hsub : Icc 1 (m / p ^ i) ⊆ Icc 1 m :=
    Icc_subset_Icc le_rfl (Nat.div_le_self m (p ^ i))
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun k hk => ?_
    rw [mul_comm k (p ^ i), ← Nat.div_div_eq_div_mul]
  · intro k hk hk'
    -- k ∈ Icc 1 m but not in Icc 1 (m/p^i), so k > m/p^i, hence the term vanishes
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hkn : k ≤ m := (mem_Icc.mp hk).2
    have hgt : m / p ^ i < k := by
      have : ¬(1 ≤ k ∧ k ≤ m / p ^ i) := by
        simpa [mem_Icc] using hk'
      omega
    have hppos : 0 < p ^ i := pow_pos hp.pos _
    have hlt : m < k * p ^ i := (Nat.div_lt_iff_lt_mul hppos).mp hgt
    have : m / (k * p ^ i) = 0 := Nat.div_eq_of_lt hlt
    simp [this]

/- Exact division: `aDen m ∣ aNum m` -/

lemma aDen_factorization_le_aNum (m p : ℕ) (hp : p.Prime) :
    (aDen m).factorization p ≤ (aNum m).factorization p := by
  rw [aNum_factorization m p hp, aDen_factorization m p hp]
  have hle : ∀ i ∈ Icc 1 m,
      ∑ k ∈ Icc 1 (m / p ^ i), k * ((m / p ^ i) / k) ≤ (m / p ^ i) ^ 2 :=
    fun i _hi => sum_mul_div_le_sq (m / p ^ i)
  exact sum_le_sum hle

lemma aDen_dvd_aNum (m : ℕ) : aDen m ∣ aNum m := by
  refine (factorization_prime_le_iff_dvd (aDen_ne_zero m) (aNum_ne_zero m)).mp ?_
  intro p hp
  exact aDen_factorization_le_aNum m p hp

/- The p-adic valuation of `a m` -/

lemma a_factorization (m p : ℕ) (hp : p.Prime) :
    (a m).factorization p = ∑ i ∈ Icc 1 m, g (m / p ^ i) := by
  rw [a_eq, factorization_div (aDen_dvd_aNum m), Finsupp.coe_tsub, Pi.sub_apply]
  rw [aNum_factorization m p hp, aDen_factorization m p hp]
  have hle : ∀ i ∈ Icc 1 m,
      ∑ k ∈ Icc 1 (m / p ^ i), k * ((m / p ^ i) / k) ≤ (m / p ^ i) ^ 2 :=
    fun i _hi => sum_mul_div_le_sq (m / p ^ i)
  rw [← sum_tsub_distrib _ hle]
  refine sum_congr rfl fun i _hi => ?_
  exact (g_eq_sub (m / p ^ i)).symm

/- Constancy of `⌊m / p^i⌋` on residue blocks -/

lemma div_pow_const {n p k i : ℕ} (hp : 0 < p) (hk : k < p) (hi : 1 ≤ i) :
    (n * p + k) / p ^ i = (n * p) / p ^ i := by
  have hpow : p ^ i = p * p ^ (i - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hi]
    rw [pow_succ, mul_comm]
  rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have h1 : (n * p + k) / p = n := by
    rw [add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hk, zero_add]
  have h2 : (n * p) / p = n := Nat.mul_div_cancel n hp
  rw [h1, h2]

lemma sum_g_div_pow_eq {m₁ m₂ p : ℕ} (hp : p.Prime)
    (h : ∀ i, 1 ≤ i → m₁ / p ^ i = m₂ / p ^ i) :
    ∑ i ∈ Icc 1 m₁, g (m₁ / p ^ i) = ∑ i ∈ Icc 1 m₂, g (m₂ / p ^ i) := by
  wlog hle : m₁ ≤ m₂ generalizing m₁ m₂
  · exact (this (fun i hi => (h i hi).symm) (le_of_not_ge hle)).symm
  have hsub : Icc 1 m₁ ⊆ Icc 1 m₂ := Icc_subset_Icc le_rfl hle
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun i hi => ?_
    rw [h i (mem_Icc.mp hi).1]
  · intro i hi hi'
    have him : m₁ < i := by
      have : ¬(1 ≤ i ∧ i ≤ m₁) := by simpa [mem_Icc] using hi'
      have : 1 ≤ i := (mem_Icc.mp hi).1
      omega
    have hlt : m₁ < p ^ i := him.trans (Nat.lt_pow_self hp.one_lt)
    have hz : m₁ / p ^ i = 0 := Nat.div_eq_of_lt hlt
    have : m₂ / p ^ i = 0 := by
      rw [← h i (mem_Icc.mp hi).1, hz]
    simp [this, g_zero]

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  let _ := hn
  rw [a_factorization _ p hp, a_factorization _ p hp]
  refine sum_g_div_pow_eq hp fun i hi => ?_
  exact (div_pow_const hp.pos hk hi).symm
