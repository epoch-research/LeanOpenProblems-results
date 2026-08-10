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

namespace A129365Proof

/-- Number-of-multiples counting: `∑_{j∈[1,m]} [d ∣ j] = m / d`. -/
private lemma count_mult (d m : ℕ) :
    ∑ j ∈ Icc 1 m, (if d ∣ j then (1:ℕ) else 0) = m / d := by
  rw [Finset.sum_boole]
  rw [show Icc 1 m = Ioc 0 m from rfl]
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1

/-- `∑_{i∈[1,L]} [p^i ∣ x] = v_p(x)` when `L ≥ v_p(x)`. -/
private lemma vp_eq_sum (p x L : ℕ) (hp : p.Prime) (hx : x ≠ 0)
    (hL : x.factorization p ≤ L) :
    ∑ i ∈ Icc 1 L, (if p ^ i ∣ x then (1:ℕ) else 0) = x.factorization p := by
  rw [Finset.sum_boole]
  have hfilter : (Icc 1 L).filter (fun i => p ^ i ∣ x) = Icc 1 (x.factorization p) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, hdvd⟩
      exact ⟨h1, (hp.pow_dvd_iff_le_factorization hx).mp hdvd⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 hL⟩, (hp.pow_dvd_iff_le_factorization hx).mpr h2⟩
  rw [hfilter, Nat.card_Icc]
  simp

/-- `v_p(∏_j ∏_k gcd(j,k)) = ∑_j ∑_k min(v_p j, v_p k)`. -/
private lemma N_fact (m p : ℕ) :
    (((Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k)).factorization p
      = ∑ j ∈ Icc 1 m, ∑ k ∈ Icc 1 m, min (j.factorization p) (k.factorization p) := by
  have hj : ∀ j ∈ Icc 1 m, ((Icc 1 m).prod fun k => Nat.gcd j k) ≠ 0 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    have : 0 < Nat.gcd j k := Nat.gcd_pos_of_pos_left k (by omega)
    omega
  rw [Nat.factorization_prod hj]
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j hj'
  rw [Finset.mem_Icc] at hj'
  have hk : ∀ k ∈ Icc 1 m, Nat.gcd j k ≠ 0 := by
    intro k hk
    have : 0 < Nat.gcd j k := Nat.gcd_pos_of_pos_left k (by omega)
    omega
  rw [Nat.factorization_prod hk, Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro k hk'
  rw [Finset.mem_Icc] at hk'
  rw [Nat.factorization_gcd (by omega) (by omega)]
  rfl

/-- `min(v_p j, v_p k) = ∑_{i∈[1,m]} [p^i∣j ∧ p^i∣k]` under bounds. -/
private lemma min_eq_sum (p j k m : ℕ) (hp : p.Prime) (hj : j ≠ 0) (hk : k ≠ 0)
    (hjm : j.factorization p ≤ m) (hkm : k.factorization p ≤ m) :
    min (j.factorization p) (k.factorization p)
      = ∑ i ∈ Icc 1 m, (if p ^ i ∣ j ∧ p ^ i ∣ k then (1:ℕ) else 0) := by
  rw [Finset.sum_boole]
  have hfilter : (Icc 1 m).filter (fun i => p ^ i ∣ j ∧ p ^ i ∣ k)
      = Icc 1 (min (j.factorization p) (k.factorization p)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, hd1, hd2⟩
      exact ⟨h1, (hp.pow_dvd_iff_le_factorization hj).mp hd1,
             (hp.pow_dvd_iff_le_factorization hk).mp hd2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2.trans hjm⟩,
             (hp.pow_dvd_iff_le_factorization hj).mpr h2,
             (hp.pow_dvd_iff_le_factorization hk).mpr h3⟩
  rw [hfilter, Nat.card_Icc]
  simp

/-- Closed form for the numerator valuation: `v_p(N m) = ∑_{i∈[1,m]} (m/p^i)^2`. -/
private lemma N_closed (m p : ℕ) (hp : p.Prime) :
    (((Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k)).factorization p
      = ∑ i ∈ Icc 1 m, (m / p ^ i) ^ 2 := by
  rw [N_fact]
  have step1 : ∀ j ∈ Icc 1 m, ∀ k ∈ Icc 1 m,
      min (j.factorization p) (k.factorization p)
        = ∑ i ∈ Icc 1 m, (if p ^ i ∣ j ∧ p ^ i ∣ k then (1:ℕ) else 0) := by
    intro j hj k hk
    rw [Finset.mem_Icc] at hj hk
    have hjm : j.factorization p ≤ m := (Nat.factorization_lt p (by omega : j ≠ 0)).le.trans (by omega)
    have hkm : k.factorization p ≤ m := (Nat.factorization_lt p (by omega : k ≠ 0)).le.trans (by omega)
    exact min_eq_sum p j k m hp (by omega) (by omega) hjm hkm
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => step1 j hj k hk))]
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have : ∀ j k, (if p ^ i ∣ j ∧ p ^ i ∣ k then (1:ℕ) else 0)
      = (if p ^ i ∣ j then (1:ℕ) else 0) * (if p ^ i ∣ k then (1:ℕ) else 0) := by
    intro j k; by_cases h1 : p^i ∣ j <;> by_cases h2 : p^i ∣ k <;> simp [h1, h2]
  simp_rw [this]
  rw [← Finset.sum_mul_sum]
  rw [count_mult]
  ring

/-- `∏_{i∈[1,n]} i = n!`. -/
private lemma prod_Icc_id (n : ℕ) : (Icc 1 n).prod (fun i => i) = n ! := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; ring

/-- Legendre-type formula: `v_p(n!) = ∑_{i∈[1,m]} n/p^i` for `n ≤ m`. -/
private lemma fact_fact (p n m : ℕ) (hp : p.Prime) (hnm : n ≤ m) :
    (n !).factorization p = ∑ i ∈ Icc 1 m, n / p ^ i := by
  rw [← prod_Icc_id n]
  have hne : ∀ t ∈ Icc 1 n, (fun i => i) t ≠ 0 := by
    intro t ht; rw [Finset.mem_Icc] at ht; show t ≠ 0; omega
  rw [Nat.factorization_prod hne, Finsupp.finset_sum_apply]
  have step : ∀ t ∈ Icc 1 n, (t.factorization p)
      = ∑ i ∈ Icc 1 m, (if p ^ i ∣ t then (1:ℕ) else 0) := by
    intro t ht; rw [Finset.mem_Icc] at ht
    have : t.factorization p ≤ m := (Nat.factorization_lt p (by omega : t ≠ 0)).le.trans (by omega)
    exact (vp_eq_sum p t m hp (by omega) this).symm
  rw [Finset.sum_congr rfl step]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact count_mult (p^i) n

/-- Closed form for the denominator valuation. -/
private lemma D_closed (m p : ℕ) (hp : p.Prime) :
    (((Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k)).factorization p
      = ∑ i ∈ Icc 1 m, ∑ k ∈ Icc 1 m, k * (m / (k * p ^ i)) := by
  have hne : ∀ k ∈ Icc 1 m, ((Nat.factorial (m / k)) ^ k) ≠ 0 := by
    intro k hk
    positivity
  rw [Nat.factorization_prod hne, Finsupp.finset_sum_apply]
  have step : ∀ k ∈ Icc 1 m, (((Nat.factorial (m / k)) ^ k).factorization p)
      = ∑ i ∈ Icc 1 m, k * (m / (k * p ^ i)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Nat.factorization_pow]
    rw [Finsupp.smul_apply, smul_eq_mul]
    rw [fact_fact p (m / k) m hp (Nat.div_le_self m k)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.div_div_eq_div_mul]
  rw [Finset.sum_congr rfl step]
  rw [Finset.sum_comm]

private lemma N_ne (m : ℕ) :
    ((Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  rw [Finset.mem_Icc] at hj
  have : 0 < Nat.gcd j k := Nat.gcd_pos_of_pos_left k (by omega)
  omega

private lemma D_ne (m : ℕ) :
    ((Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  positivity

/-- Per-`i` inequality that yields the exact divisibility. -/
private lemma peri_le (m p i : ℕ) :
    ∑ k ∈ Icc 1 m, k * (m / (k * p ^ i)) ≤ (m / p ^ i) ^ 2 := by
  set M := m / p ^ i with hM
  have hterm : ∀ k, m / (k * p ^ i) = M / k := by
    intro k
    rw [hM, Nat.div_div_eq_div_mul, mul_comm]
  simp_rw [hterm]
  have hMm : M ≤ m := Nat.div_le_self m (p ^ i)
  have hsub : ∑ k ∈ Icc 1 m, k * (M / k) = ∑ k ∈ Icc 1 M, k * (M / k) := by
    apply (Finset.sum_subset _ _).symm
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro x hx hnx
      rw [Finset.mem_Icc] at hx hnx
      have hMx : M < x := by omega
      have : M / x = 0 := Nat.div_eq_of_lt hMx
      rw [this, mul_zero]
  rw [hsub]
  calc ∑ k ∈ Icc 1 M, k * (M / k) ≤ ∑ k ∈ Icc 1 M, M := by
          apply Finset.sum_le_sum
          intro k hk
          rw [mul_comm]
          exact Nat.div_mul_le_self M k
    _ = M ^ 2 := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]; simp [sq]

/-- Exact divisibility: the denominator divides the numerator. -/
private lemma D_dvd_N (m : ℕ) :
    ((Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k)
      ∣ ((Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k) := by
  rw [← Nat.factorization_le_iff_dvd (D_ne m) (N_ne m)]
  rw [Finsupp.le_def]
  intro q
  by_cases hq : q.Prime
  · rw [N_closed m q hq, D_closed m q hq]
    apply Finset.sum_le_sum
    intro i hi
    exact peri_le m q i
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq,
        Nat.factorization_eq_zero_of_not_prime _ hq]

/-- Floor invariance for `i ≥ 1`: `(np+k)/p^i = (np)/p^i` when `k < p`. -/
private lemma floor_inv (n p k i : ℕ) (hp : 0 < p) (hk : k < p) (hi : 1 ≤ i) :
    (n * p + k) / p ^ i = (n * p) / p ^ i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [pow_succ]
  rw [mul_comm (p^j) p]
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [mul_comm n p, Nat.mul_add_div hp, Nat.div_eq_of_lt hk, add_zero]
  rw [Nat.mul_div_cancel_left n hp]

private lemma div_pow_zero (x p i : ℕ) (hp : 2 ≤ p) (hxi : x < i) : x / p ^ i = 0 := by
  apply Nat.div_eq_of_lt
  calc x < i := hxi
    _ < 2 ^ i := Nat.lt_two_pow_self
    _ ≤ p ^ i := Nat.pow_le_pow_left hp i

private lemma block_bound (n p k i : ℕ) (hn : 0 < n) (hp : 2 ≤ p) (hk : k < p)
    (hi : n * p < i) : n * p + k < p ^ i := by
  have h1 : n * p + k < 2 * (n * p) := by
    have : p ≤ n * p := Nat.le_mul_of_pos_left p hn
    omega
  have h2 : 2 * (n * p) < 2 ^ (n * p + 1) := by
    have : n * p < 2 ^ (n * p) := Nat.lt_two_pow_self
    calc 2 * (n * p) < 2 * 2 ^ (n * p) := by omega
      _ = 2 ^ (n * p + 1) := by rw [pow_succ]; ring
  have h3 : 2 ^ (n * p + 1) ≤ p ^ (n * p + 1) := Nat.pow_le_pow_left hp _
  have h4 : p ^ (n * p + 1) ≤ p ^ i := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- Block invariance of the numerator valuation. -/
private lemma N_block (n p k : ℕ) (hn : 0 < n) (hp : p.Prime) (hk : k < p) :
    (((Icc 1 (n*p+k)).prod fun j => (Icc 1 (n*p+k)).prod fun k => Nat.gcd j k)).factorization p
      = (((Icc 1 (n*p)).prod fun j => (Icc 1 (n*p)).prod fun k => Nat.gcd j k)).factorization p := by
  rw [N_closed _ p hp, N_closed _ p hp]
  have h2p : 2 ≤ p := hp.two_le
  have e1 : ∑ i ∈ Icc 1 (n*p+k), ((n*p+k)/p^i)^2 = ∑ i ∈ Icc 1 (n*p+k), ((n*p)/p^i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [floor_inv n p k i (by omega) hk hi.1]
  rw [e1]
  apply (Finset.sum_subset ?_ ?_).symm
  · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  · intro x hx hnx
    rw [Finset.mem_Icc] at hx hnx
    have hxgt : n * p < x := by omega
    rw [div_pow_zero (n*p) p x h2p hxgt]; simp

/-- Block invariance of the denominator valuation. -/
private lemma D_block (n p k : ℕ) (hn : 0 < n) (hp : p.Prime) (hk : k < p) :
    (((Icc 1 (n*p+k)).prod fun c => (Nat.factorial ((n*p+k) / c)) ^ c)).factorization p
      = (((Icc 1 (n*p)).prod fun c => (Nat.factorial ((n*p) / c)) ^ c)).factorization p := by
  rw [D_closed _ p hp, D_closed _ p hp]
  have h2p : 2 ≤ p := hp.two_le
  have hpi : ∀ i, 1 ≤ p ^ i := fun i => Nat.one_le_pow _ _ (by omega)
  have e1 : (∑ i ∈ Icc 1 (n*p+k), ∑ c ∈ Icc 1 (n*p+k), c * ((n*p+k) / (c * p ^ i)))
      = ∑ i ∈ Icc 1 (n*p), ∑ c ∈ Icc 1 (n*p+k), c * ((n*p+k) / (c * p ^ i)) := by
    apply (Finset.sum_subset ?_ ?_).symm
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
    · intro i hi hni
      rw [Finset.mem_Icc] at hi hni
      apply Finset.sum_eq_zero
      intro c hc
      have hbound : n*p+k < p ^ i := block_bound n p k i hn h2p hk (by omega)
      have : (n*p+k) / (c * p ^ i) = 0 := by
        apply Nat.div_eq_of_lt
        rw [Finset.mem_Icc] at hc
        calc n*p+k < p^i := hbound
          _ ≤ c * p^i := Nat.le_mul_of_pos_left _ (by omega)
      rw [this, mul_zero]
  rw [e1]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  have hsummand : ∀ c, (n*p+k) / (c * p ^ i) = (n*p) / (c * p ^ i) := by
    intro c
    rw [mul_comm c (p^i), ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        floor_inv n p k i (by omega) hk hi.1]
  rw [Finset.sum_congr rfl (fun c _ => by rw [hsummand c])]
  apply (Finset.sum_subset ?_ ?_).symm
  · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  · intro c hc hnc
    rw [Finset.mem_Icc] at hc hnc
    have : (n*p) / (c * p ^ i) = 0 := by
      apply Nat.div_eq_of_lt
      calc n*p < c := by omega
        _ ≤ c * p^i := Nat.le_mul_of_pos_right _ (hpi i)
    rw [this, mul_zero]

/-- `a m` unfolds to numerator/denominator. -/
private lemma a_eq (m : ℕ) :
    a m = ((Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k)
          / ((Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k) := rfl

/-- The key additive identity: `v_p(a m) + v_p(D m) = v_p(N m)`. -/
private lemma a_factorization (m p : ℕ) :
    (a m).factorization p
      + (((Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k)).factorization p
      = (((Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k)).factorization p := by
  have hdvd := D_dvd_N m
  have hDne := D_ne m
  have hNne := N_ne m
  have hmul : a m * ((Icc 1 m).prod fun k => (Nat.factorial (m / k)) ^ k)
      = ((Icc 1 m).prod fun j => (Icc 1 m).prod fun k => Nat.gcd j k) := by
    rw [a_eq]
    exact Nat.div_mul_cancel hdvd
  have hane : a m ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact hNne hmul.symm
  have hcong := congrArg (fun x => x.factorization p) hmul
  simp only at hcong
  rw [← hcong, Nat.factorization_mul hane hDne]
  rfl

end A129365Proof

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
  (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  have h0 := A129365Proof.a_factorization (n * p) p
  have h1 := A129365Proof.a_factorization (n * p + k) p
  rw [A129365Proof.N_block n p k hn hp hk] at h1
  rw [A129365Proof.D_block n p k hn hp hk] at h1
  omega
