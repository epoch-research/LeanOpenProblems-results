import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `A357674 n = u_A357674 n 2`.
-/
def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

/-- The first factor in `A357674`. -/
def S1 (n : ℕ) : ℕ :=
  Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)

/-- The second factor in `A357674`. -/
def S2 (n : ℕ) : ℕ :=
  Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)

lemma A357674_eq (n : ℕ) : A357674 n = S1 n ^ 4 * S2 n ^ 3 := rfl

/-- For `n ≥ 1`, `C(n+k-1, k) = C(n+k-1, n-1)`. -/
lemma choose_n_add_k_sub_one (n k : ℕ) (hn : 1 ≤ n) :
    (n + k - 1).choose k = (n + k - 1).choose (n - 1) := by
  have hle : k ≤ n + k - 1 := by omega
  rw [← choose_symm hle]
  congr 1
  omega

/-- Hockey-stick: `S1 n = C(3n, n)` for `n ≥ 1`. -/
lemma S1_eq_choose (n : ℕ) (hn : 1 ≤ n) : S1 n = (3 * n).choose n := by
  unfold S1
  have hsum : (∑ i ∈ range (2 * n + 1), (i + (n - 1)).choose (n - 1)) =
      (2 * n + (n - 1) + 1).choose (n - 1 + 1) :=
    sum_range_add_choose (2 * n) (n - 1)
  have hidx : 2 * n + (n - 1) + 1 = 3 * n := by omega
  have hrhs : (2 * n + (n - 1) + 1).choose (n - 1 + 1) = (3 * n).choose n := by
    rw [hidx, Nat.sub_add_cancel hn]
  refine Eq.trans ?_ hrhs
  refine Eq.trans ?_ hsum
  refine sum_congr rfl fun k _hk => ?_
  rw [choose_n_add_k_sub_one n k hn]
  congr 1
  omega

lemma S1_one : S1 1 = 3 := by
  rw [S1_eq_choose 1 le_rfl]; rfl

lemma S2_one : S2 1 = 3 := by
  unfold S2
  simp [sum_range_succ, Nat.choose_self]

lemma A357674_one : A357674 1 = 2187 := by
  rw [A357674_eq, S1_one, S2_one]; norm_num

lemma S1_three : S1 3 = 84 := by
  rw [S1_eq_choose 3 (by norm_num)]; rfl

lemma S2_three : S2 3 = 1596 := by
  unfold S2; decide

lemma A357674_conjecture_1_three :
    A357674 3 ≡ A357674 1 [MOD 3 ^ 5] := by
  rw [A357674_eq, A357674_one, S1_three, S2_three]
  have hA : 3 ^ 5 ∣ 84 ^ 4 * 1596 ^ 3 := by
    have h84 : 84 = 3 * 28 := rfl
    have h1596 : 1596 = 3 * 532 := rfl
    rw [h84, h1596, mul_pow, mul_pow, mul_mul_mul_comm, ← pow_add]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by norm_num : 5 ≤ 7)) _
  have h1 : 3 ^ 5 ∣ 2187 := ⟨9, by norm_num⟩
  exact Nat.ModEq.trans (Nat.modEq_zero_iff_dvd.mpr hA)
    (Nat.modEq_zero_iff_dvd.mpr h1).symm

set_option maxHeartbeats 8000000

lemma S1_five : S1 5 = 3003 := by
  rw [S1_eq_choose 5 (by norm_num)]; rfl

lemma S2_five : S2 5 = 1933503 := by
  unfold S2; decide

lemma A357674_conjecture_1_five :
    A357674 5 ≡ A357674 1 [MOD 5 ^ 5] := by
  rw [A357674_eq, A357674_one, S1_five, S2_five]
  have hS2 : 1933503 ≡ 2253 [MOD 5 ^ 5] := by decide
  have hsq : 3003 ^ 2 ≡ 2384 [MOD 5 ^ 5] := by decide
  have h4 : 3003 ^ 4 ≡ 2206 [MOD 5 ^ 5] :=
    (Nat.ModEq.pow 2 hsq).trans (by decide)
  have hS23 : 1933503 ^ 3 ≡ 1402 [MOD 5 ^ 5] := by
    have h3 : 2253 ^ 3 ≡ 1402 [MOD 5 ^ 5] := by
      have h2 : 2253 ^ 2 ≡ 1009 [MOD 5 ^ 5] := by decide
      exact (Nat.ModEq.mul h2 (Nat.ModEq.refl 2253)).trans (by decide)
    exact (Nat.ModEq.pow 3 hS2).trans h3
  exact (Nat.ModEq.mul h4 hS23).trans (by decide)

/-! ### Combinatorial identity for `S2` -/

/-- Vandermonde specialised: `C(n+k-1, n-1) = ∑_m C(k,m) C(n-1,m)`. -/
lemma choose_n_add_k_sub_one_vandermonde (n k : ℕ) (hn : 1 ≤ n) :
    (n + k - 1).choose (n - 1) =
      ∑ m ∈ range n, k.choose m * (n - 1).choose m := by
  have heq : n + k - 1 = k + (n - 1) := by omega
  rw [heq, Nat.add_choose_eq]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
    k.choose i * (n - 1).choose j]
  have hsucc : (n - 1).succ = n := by omega
  rw [hsucc]
  refine sum_congr rfl fun m hm => ?_
  simp only [mem_range] at hm
  have hm' : m ≤ n - 1 := by omega
  rw [choose_symm hm']

/-- `C(k,m) C(n+k-1, n-1) = C(n+m-1, m) C(n+k-1, n+m-1)`. -/
lemma choose_mul_choose_key (n k m : ℕ) (hn : 1 ≤ n) :
    k.choose m * (n + k - 1).choose (n - 1) =
      (n + m - 1).choose m * (n + k - 1).choose (n + m - 1) := by
  by_cases hkm : k < m
  · rw [choose_eq_zero_of_lt hkm, zero_mul]
    have : n + k - 1 < n + m - 1 := by omega
    rw [choose_eq_zero_of_lt this, mul_zero]
  · have hmk : m ≤ k := Nat.le_of_not_gt hkm
    have h1 : n - 1 ≤ n + k - 1 := by omega
    have h2 : m ≤ n + m - 1 := by omega
    have h3 : n + m - 1 ≤ n + k - 1 := by omega
    suffices (k.choose m * (n + k - 1).choose (n - 1) : ℚ) =
        ((n + m - 1).choose m * (n + k - 1).choose (n + m - 1) : ℚ) by
      exact_mod_cast this
    push_cast
    have c1 : (k.choose m : ℚ) = (k.factorial : ℚ) / (m.factorial * (k - m).factorial) := by
      rw [cast_choose (K := ℚ) hmk]
    have c2 : ((n + k - 1).choose (n - 1) : ℚ) =
        ((n + k - 1).factorial : ℚ) / ((n - 1).factorial * k.factorial) := by
      rw [cast_choose (K := ℚ) h1]
      have : n + k - 1 - (n - 1) = k := by omega
      rw [this]
    have c3 : ((n + m - 1).choose m : ℚ) =
        ((n + m - 1).factorial : ℚ) / (m.factorial * (n - 1).factorial) := by
      rw [cast_choose (K := ℚ) h2]
      have : n + m - 1 - m = n - 1 := by omega
      rw [this]
    have c4 : ((n + k - 1).choose (n + m - 1) : ℚ) =
        ((n + k - 1).factorial : ℚ) / ((n + m - 1).factorial * (k - m).factorial) := by
      rw [cast_choose (K := ℚ) h3]
      have : n + k - 1 - (n + m - 1) = k - m := by omega
      rw [this]
    rw [c1, c2, c3, c4]
    have hf1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero k
    have hf2 : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero m
    have hf3 : ((k - m).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero (k - m)
    have hf4 : ((n - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero (n - 1)
    have hf5 : ((n + k - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero (n + k - 1)
    have hf6 : ((n + m - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero (n + m - 1)
    field_simp [hf1, hf2, hf3, hf4, hf5, hf6]

/-- Hockey-stick form used below. -/
lemma sum_choose_hockey (a N : ℕ) (_h : a ≤ N) :
    ∑ t ∈ Icc a N, t.choose a = (N + 1).choose (a + 1) := by
  simpa using sum_Icc_choose N a

/-- `n + k - 1` is injective for `n ≥ 1`. -/
lemma n_add_k_sub_one_inj {n k1 k2 : ℕ} (hn : 1 ≤ n)
    (h : n + k1 - 1 = n + k2 - 1) : k1 = k2 := by
  have h1 : n + k1 - 1 + 1 = n + k1 := Nat.sub_add_cancel (by omega : 1 ≤ n + k1)
  have h2 : n + k2 - 1 + 1 = n + k2 := Nat.sub_add_cancel (by omega : 1 ≤ n + k2)
  omega

/-- Reindex the hockey-stick sum appearing in `S2`. -/
lemma sum_choose_reindex (n m : ℕ) (hn : 1 ≤ n) (hm : m < n) :
    ∑ k ∈ range (2 * n + 1), (n + k - 1).choose (n + m - 1) =
      (3 * n).choose (n + m) := by
  have hreind :
      ∑ k ∈ range (2 * n + 1), (n + k - 1).choose (n + m - 1) =
        ∑ t ∈ Icc (n - 1) (3 * n - 1), t.choose (n + m - 1) := by
    refine sum_nbij (fun k => n + k - 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_range, mem_Icc] at hk ⊢
      constructor
      · have : n - 1 ≤ n + k - 1 := by
          have : n + k - 1 = n - 1 + k := by omega
          omega
        exact this
      · have : n + k - 1 ≤ 3 * n - 1 := by
          have hk' : k ≤ 2 * n := by omega
          have : n + k - 1 = n - 1 + k := by omega
          omega
        exact this
    · intro k1 _hk1 k2 _hk2 h
      exact n_add_k_sub_one_inj hn h
    · intro t ht
      simp only [Set.SurjOn, Set.mem_image, mem_coe, mem_range, mem_Icc] at ht ⊢
      refine ⟨t + 1 - n, ?_, ?_⟩
      · have : t + 1 - n < 2 * n + 1 := by
          have : t ≤ 3 * n - 1 := ht.2
          have h3 : 3 * n - 1 + 1 = 3 * n := Nat.sub_add_cancel (by omega : 1 ≤ 3 * n)
          omega
        exact this
      · have ht1 : n - 1 ≤ t := ht.1
        have : n + (t + 1 - n) - 1 = t := by omega
        exact this
    · intro k _hk; rfl
  rw [hreind]
  by_cases hme : m = 0
  · subst hme
    have hle : n - 1 ≤ 3 * n - 1 := by
      have : 1 ≤ 3 * n := by omega
      omega
    have hs := sum_choose_hockey (n - 1) (3 * n - 1) hle
    have hr : 3 * n - 1 + 1 = 3 * n := Nat.sub_add_cancel (by omega : 1 ≤ 3 * n)
    have hr2 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simpa [Nat.add_zero, hr, hr2] using hs
  · have hme' : 1 ≤ m := by omega
    have hnm : n + m - 1 = n - 1 + m := by omega
    have hcut : n + m - 1 - 1 = n - 1 + (m - 1) := by omega
    have hdisj :
        Disjoint (Icc (n - 1) (n + m - 1 - 1)) (Icc (n + m - 1) (3 * n - 1)) := by
      refine disjoint_left.mpr ?_
      intro t ht1 ht2
      simp only [mem_Icc] at ht1 ht2
      omega
    have hunion :
        Icc (n - 1) (n + m - 1 - 1) ∪ Icc (n + m - 1) (3 * n - 1) =
          Icc (n - 1) (3 * n - 1) := by
      ext t
      simp only [mem_union, mem_Icc]
      constructor
      · intro ht
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · constructor <;> omega
        · constructor <;> omega
      · intro ht
        rcases ht with ⟨ht1, ht2⟩
        by_cases h : t ≤ n + m - 1 - 1
        · left; exact ⟨ht1, h⟩
        · right
          constructor
          · omega
          · exact ht2
    rw [← hunion, sum_union hdisj]
    have hvan : ∑ t ∈ Icc (n - 1) (n + m - 1 - 1), t.choose (n + m - 1) = 0 := by
      apply sum_eq_zero
      intro t ht
      simp only [mem_Icc] at ht
      apply choose_eq_zero_of_lt
      omega
    rw [hvan, zero_add]
    have hle : n + m - 1 ≤ 3 * n - 1 := by omega
    have hs := sum_choose_hockey (n + m - 1) (3 * n - 1) hle
    have hr : 3 * n - 1 + 1 = 3 * n := Nat.sub_add_cancel (by omega : 1 ≤ 3 * n)
    have hr2 : n + m - 1 + 1 = n + m := by omega
    simpa [hr, hr2] using hs

/-- The key closed-form identity for `S2`. -/
lemma S2_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    S2 n = ∑ m ∈ range n,
      (n - 1).choose m * (n + m - 1).choose m * (3 * n).choose (n + m) := by
  unfold S2
  have hsq : ∀ k ∈ range (2 * n + 1),
      ((n + k - 1).choose k) ^ 2 =
        (n + k - 1).choose (n - 1) * (n + k - 1).choose (n - 1) := by
    intro k _
    rw [choose_n_add_k_sub_one n k hn]
    ring
  refine Eq.trans (sum_congr rfl hsq) ?_
  have : ∑ k ∈ range (2 * n + 1),
      (n + k - 1).choose (n - 1) * (n + k - 1).choose (n - 1) =
    ∑ k ∈ range (2 * n + 1),
      (n + k - 1).choose (n - 1) *
        ∑ m ∈ range n, k.choose m * (n - 1).choose m := by
    refine sum_congr rfl fun k _ => ?_
    rw [choose_n_add_k_sub_one_vandermonde n k hn]
  rw [this]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m hm => ?_
  have : ∑ k ∈ range (2 * n + 1),
      (n + k - 1).choose (n - 1) * (k.choose m * (n - 1).choose m) =
    (n - 1).choose m *
      ∑ k ∈ range (2 * n + 1), (n + k - 1).choose (n - 1) * k.choose m := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [this]
  have hid : ∑ k ∈ range (2 * n + 1), (n + k - 1).choose (n - 1) * k.choose m =
      (n + m - 1).choose m *
        ∑ k ∈ range (2 * n + 1), (n + k - 1).choose (n + m - 1) := by
    have : ∑ k ∈ range (2 * n + 1), (n + k - 1).choose (n - 1) * k.choose m =
        ∑ k ∈ range (2 * n + 1),
          (n + m - 1).choose m * (n + k - 1).choose (n + m - 1) := by
      refine sum_congr rfl fun k _ => ?_
      rw [mul_comm, choose_mul_choose_key n k m hn]
    rw [this, ← mul_sum]
  rw [hid]
  have hm' : m < n := mem_range.mp hm
  rw [sum_choose_reindex n m hn hm']
  ring

lemma Icc_one_eq_image (k : ℕ) :
    Icc 1 k = (range k).image (· + 1) := by
  ext x
  simp only [mem_Icc, mem_image, mem_range]
  constructor
  · intro hx
    exact ⟨x - 1, by omega, by omega⟩
  · rintro ⟨y, hy, rfl⟩
    omega

lemma add_one_injOn {s : Finset ℕ} : Set.InjOn (fun x : ℕ => x + 1) s :=
  fun _ _ _ _ h => Nat.succ_injective h

lemma prod_Icc_cast (k : ℕ) :
    ∏ i ∈ Icc 1 k, (i : ℚ) = k.factorial := by
  rw [Icc_one_eq_image, prod_image add_one_injOn]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, factorial_succ]
    push_cast
    ring

lemma prod_Icc_sub_self (p k : ℕ) (hk : k ≤ p) :
    ∏ i ∈ Icc 1 k, ((p : ℚ) - i) = ((p - 1).descFactorial k : ℚ) := by
  rw [Icc_one_eq_image, prod_image add_one_injOn]
  rw [Nat.descFactorial_eq_prod_range]
  push_cast
  refine prod_congr rfl fun i hi => ?_
  simp only [mem_range] at hi
  have : (p : ℚ) - (i + 1) = ((p - 1 - i : ℕ) : ℚ) := by
    have heq : p - (i + 1) = p - 1 - i := by omega
    rw [← heq, Nat.cast_sub (by omega)]
    push_cast; ring
  simpa using this

/-- `C(n-1, k) = (-1)^k ∏_{i=1}^k (1 - n/i)` for `k ≤ n-1`. -/
lemma choose_pred_eq_prod (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n - 1) :
    ((n - 1).choose k : ℚ) =
      (-1 : ℚ) ^ k * ∏ i ∈ Icc 1 k, (1 - (n : ℚ) / i) := by
  have hprod : ∏ i ∈ Icc 1 k, (1 - (n : ℚ) / i) =
      ∏ i ∈ Icc 1 k, ((i : ℚ) - n) / i := by
    refine prod_congr rfl fun i hi => ?_
    have hi0 : (i : ℚ) ≠ 0 := by
      simp only [mem_Icc] at hi
      exact_mod_cast (show i ≠ 0 by omega)
    field_simp [hi0]
  rw [hprod, prod_div_distrib, prod_Icc_cast]
  have hnum : ∏ i ∈ Icc 1 k, ((i : ℚ) - n) =
      (-1 : ℚ) ^ k * ∏ i ∈ Icc 1 k, ((n : ℚ) - i) := by
    have : ∏ i ∈ Icc 1 k, ((i : ℚ) - n) =
        ∏ i ∈ Icc 1 k, (-1 : ℚ) * ((n : ℚ) - i) := by
      refine prod_congr rfl fun i _ => by ring
    rw [this, prod_mul_distrib, prod_const]
    have : #(Icc 1 k) = k := by
      simp [Nat.card_Icc]
    rw [this]
  rw [hnum]
  have hk' : k ≤ n := by omega
  rw [prod_Icc_sub_self n k hk']
  have : ((n - 1).descFactorial k : ℚ) = (k.factorial : ℚ) * (n - 1).choose k := by
    exact_mod_cast descFactorial_eq_factorial_mul_choose (n - 1) k
  rw [this]
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero k
  field_simp [hf]
  have hsq : ((-1 : ℚ) ^ k) ^ 2 = 1 := by
    rw [sq, ← pow_add]
    have : k + k = 2 * k := by ring
    rw [this, pow_mul, neg_one_sq, one_pow]
  rw [hsq, mul_one]

lemma ascFactorial_cast_prod (n t : ℕ) :
    ((n + 1).ascFactorial t : ℚ) = ∏ j ∈ range t, ((n + 1 + j : ℕ) : ℚ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [ascFactorial_succ, prod_range_succ]
    push_cast
    rw [ih]
    simp [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]
    ring

lemma factorial_div_factorial_asc (n t : ℕ) :
    ((n + t).factorial : ℚ) / n.factorial = (n + 1).ascFactorial t := by
  have hn0 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero n
  have hmul := congrArg (fun x : ℕ => (x : ℚ)) (factorial_mul_ascFactorial n t)
  push_cast at hmul
  field_simp [hn0]
  exact hmul.symm

lemma prod_Icc_add (n k : ℕ) (hk : 1 ≤ k) :
    ∏ i ∈ Icc 1 (k - 1), ((n : ℚ) + i) = ((n + k - 1).factorial : ℚ) / n.factorial := by
  rw [Icc_one_eq_image, prod_image add_one_injOn]
  have ht : n + (k - 1) = n + k - 1 := by omega
  have hprod : ∏ j ∈ range (k - 1), ((n : ℚ) + (j + 1 : ℕ)) =
      ∏ j ∈ range (k - 1), ((n + 1 + j : ℕ) : ℚ) := by
    refine prod_congr rfl fun j _ => ?_
    push_cast; ring
  rw [hprod, ← ascFactorial_cast_prod n (k - 1), ← factorial_div_factorial_asc n (k - 1), ht]

/-- `C(n+k-1, k) = (n/k) ∏_{i=1}^{k-1} (1 + n/i)` for `k ≥ 1`, `n ≥ 1`. -/
lemma choose_rep_eq_prod (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ((n + k - 1).choose k : ℚ) =
      (n : ℚ) / k * ∏ i ∈ Icc 1 (k - 1), (1 + (n : ℚ) / i) := by
  have hle : k ≤ n + k - 1 := by omega
  have c : ((n + k - 1).choose k : ℚ) =
      ((n + k - 1).factorial : ℚ) / (k.factorial * (n - 1).factorial) := by
    rw [cast_choose (K := ℚ) hle]
    have : n + k - 1 - k = n - 1 := by omega
    rw [this]
  rw [c]
  have hprod : ∏ i ∈ Icc 1 (k - 1), (1 + (n : ℚ) / i) =
      ∏ i ∈ Icc 1 (k - 1), ((n : ℚ) + i) / i := by
    refine prod_congr rfl fun i hi => ?_
    have hi0 : (i : ℚ) ≠ 0 := by
      simp only [mem_Icc] at hi
      exact_mod_cast (show i ≠ 0 by omega)
    field_simp [hi0]
    ring
  rw [hprod, prod_div_distrib, prod_Icc_cast, prod_Icc_add n k hk]
  have hf1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero k
  have hf2 : ((n - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero (n - 1)
  have hf3 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero n
  have hf4 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  -- k! = k * (k-1)!, n! = n * (n-1)!
  have hkfac : (k.factorial : ℚ) = k * (k - 1).factorial := by
    have : k = (k - 1) + 1 := by omega
    rw [this, factorial_succ]
    push_cast
    ring
  have hnfac : (n.factorial : ℚ) = n * (n - 1).factorial := by
    have : n = (n - 1) + 1 := by omega
    rw [this, factorial_succ]
    push_cast
    ring
  rw [hkfac, hnfac]
  field_simp [hf1, hf2, hf3, hf4]

lemma factorial_div_factorial_of_le (n k : ℕ) (h : k ≤ n) :
    (n.factorial : ℚ) / (n - k).factorial = n.descFactorial k := by
  have hne : ((n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have heq : (n.factorial : ℚ) = (n.descFactorial k : ℚ) * (n - k).factorial := by
    have : n.factorial = n.choose k * k.factorial * (n - k).factorial :=
      (choose_mul_factorial_mul_factorial h).symm
    have : n.factorial = n.descFactorial k * (n - k).factorial := by
      rw [descFactorial_eq_factorial_mul_choose, this, mul_assoc, mul_left_comm (n.choose k)]
      ac_rfl
    exact_mod_cast this
  field_simp [hne]
  rw [heq]
  ring

lemma range_eq_insert_zero_Icc (k : ℕ) (hk : 1 ≤ k) :
    range k = insert 0 (Icc 1 (k - 1)) := by
  ext x
  simp only [mem_range, mem_insert, mem_Icc]
  omega

lemma descFactorial_cast_split (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n.descFactorial k : ℚ) = n * ∏ i ∈ Icc 1 (k - 1), ((n : ℚ) - i) := by
  rw [Nat.descFactorial_eq_prod_range]
  rw [range_eq_insert_zero_Icc k hk, prod_insert (by simp)]
  push_cast
  congr 1
  refine prod_congr rfl fun i hi => ?_
  simp only [mem_Icc] at hi
  have : i ≤ n := by omega
  rw [Nat.cast_sub this]

lemma factorial_ratio_succ_split (n k : ℕ) (hk : 1 ≤ k) :
    ((n + k).factorial : ℚ) / n.factorial =
      ((n : ℚ) + k) * ∏ i ∈ Icc 1 (k - 1), ((n : ℚ) + i) := by
  rw [factorial_div_factorial_asc n k]
  have hk' : k = (k - 1).succ := (Nat.sub_add_cancel hk).symm
  rw [hk', ascFactorial_succ]
  have : n + 1 + (k - 1) = n + k := by omega
  rw [this]
  push_cast
  have hprod : ((n + 1).ascFactorial (k - 1) : ℚ) =
      ∏ i ∈ Icc 1 (k - 1), ((n : ℚ) + i) := by
    rw [prod_Icc_add n k hk]
    have ht : n + k - 1 = n + (k - 1) := by omega
    rw [ht, factorial_div_factorial_asc n (k - 1)]
  rw [hprod]
  congr 1
  have : (k : ℚ) = ((k - 1 : ℕ) : ℚ) + 1 := by
    have hk'' : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
    exact_mod_cast hk''
  rw [this]

lemma prod_two_n_sub_div (n k : ℕ) (hk : 1 ≤ k) :
    ∏ i ∈ Icc 1 (k - 1), ((2 * n : ℚ) - i) / ((n : ℚ) + i) =
      (-1 : ℚ) ^ (k - 1) *
        ∏ i ∈ Icc 1 (k - 1), (1 - 2 * (n : ℚ) / i) / (1 + (n : ℚ) / i) := by
  have hterm : ∀ i ∈ Icc 1 (k - 1),
      ((2 * n : ℚ) - i) / ((n : ℚ) + i) =
        (-1 : ℚ) * (1 - 2 * (n : ℚ) / i) / (1 + (n : ℚ) / i) := by
    intro i hi
    have hi0 : (i : ℚ) ≠ 0 := by
      simp only [mem_Icc] at hi
      exact_mod_cast (show i ≠ 0 by omega)
    have hden : (n : ℚ) + i ≠ 0 := by
      have : (0 : ℕ) < n + i := by
        simp only [mem_Icc] at hi; omega
      exact_mod_cast this.ne'
    have hden' : 1 + (n : ℚ) / i ≠ 0 := by
      have : 1 + (n : ℚ) / i = (i + n) / i := by field_simp [hi0]
      rw [this]
      apply div_ne_zero _ hi0
      convert hden using 1
      ring
    field_simp [hi0, hden, hden']
    ring
  have : ∏ i ∈ Icc 1 (k - 1), ((2 * n : ℚ) - i) / ((n : ℚ) + i) =
      ∏ i ∈ Icc 1 (k - 1),
        (-1 : ℚ) * ((1 - 2 * (n : ℚ) / i) / (1 + (n : ℚ) / i)) := by
    refine prod_congr rfl fun i hi => ?_
    rw [hterm i hi]
    ring
  rw [this, prod_mul_distrib, prod_const]
  have : #(Icc 1 (k - 1)) = k - 1 := by simp [Nat.card_Icc]
  rw [this]

/-- `C(3n, n+k) / C(3n, n)` product formula. -/
lemma choose_three_ratio (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ 2 * n) :
    ((3 * n).choose (n + k) : ℚ) / (3 * n).choose n =
      (2 * (n : ℚ) / (n + k)) * (-1 : ℚ) ^ (k - 1) *
        ∏ i ∈ Icc 1 (k - 1), (1 - 2 * (n : ℚ) / i) / (1 + (n : ℚ) / i) := by
  have hle1 : n + k ≤ 3 * n := by omega
  have hle2 : n ≤ 3 * n := by omega
  have c1 : ((3 * n).choose (n + k) : ℚ) =
      ((3 * n).factorial : ℚ) / ((n + k).factorial * (2 * n - k).factorial) := by
    rw [cast_choose (K := ℚ) hle1]
    have : 3 * n - (n + k) = 2 * n - k := by omega
    rw [this]
  have c2 : ((3 * n).choose n : ℚ) =
      ((3 * n).factorial : ℚ) / (n.factorial * (2 * n).factorial) := by
    rw [cast_choose (K := ℚ) hle2]
    have : 3 * n - n = 2 * n := by omega
    rw [this]
  have hf3 : ((3 * n).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have hfn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero n
  have hf2 : ((2 * n).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have hfnk : ((n + k).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have hf2k : ((2 * n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  have hnk0 : ((n + k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show n + k ≠ 0 by omega)
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnki : (n : ℚ) + k ≠ 0 := by
    have : ((n + k : ℕ) : ℚ) = n + k := by push_cast; rfl
    rw [← this]; exact hnk0
  have hLHS :
      ((3 * n).choose (n + k) : ℚ) / (3 * n).choose n =
        ((2 * n).descFactorial k : ℚ) /
          (((n : ℚ) + k) * ∏ i ∈ Icc 1 (k - 1), ((n : ℚ) + i)) := by
    rw [c1, c2]
    have hquot :
        ((3 * n).factorial : ℚ) / ((n + k).factorial * (2 * n - k).factorial) /
          (((3 * n).factorial : ℚ) / (n.factorial * (2 * n).factorial)) =
          ((2 * n).factorial : ℚ) / (2 * n - k).factorial /
            (((n + k).factorial : ℚ) / n.factorial) := by
      field_simp [hf3, hfn, hf2, hfnk, hf2k]
    rw [hquot, factorial_div_factorial_of_le (2 * n) k hkn,
      factorial_ratio_succ_split n k hk]
  rw [hLHS, descFactorial_cast_split (2 * n) k hk hkn]
  have h2n : ((2 * n : ℕ) : ℚ) = 2 * (n : ℚ) := by push_cast; rfl
  rw [h2n]
  have hquot2 :
      (2 * (n : ℚ) * ∏ i ∈ Icc 1 (k - 1), ((2 * n : ℚ) - i)) /
        (((n : ℚ) + k) * ∏ i ∈ Icc 1 (k - 1), ((n : ℚ) + i)) =
        (2 * (n : ℚ) / (n + k)) *
          ∏ i ∈ Icc 1 (k - 1), ((2 * n : ℚ) - i) / ((n : ℚ) + i) := by
    have hpd : ∏ i ∈ Icc 1 (k - 1), ((2 * n : ℚ) - i) / ((n : ℚ) + i) =
        (∏ i ∈ Icc 1 (k - 1), ((2 * n : ℚ) - i)) /
          ∏ i ∈ Icc 1 (k - 1), ((n : ℚ) + i) :=
      prod_div_distrib _ _
    rw [hpd]
    field_simp [hnki]
  rw [hquot2, prod_two_n_sub_div n k hk]
  have : ((n : ℚ) + k) = (n + k : ℕ) := by push_cast; rfl
  rw [this]
  ring

/-- The weight appearing in the closed form of `S2 / S1`. -/
def Wrat (n : ℕ) : ℚ :=
  ∑ k ∈ Icc 1 (n - 1),
    (1 / (k : ℚ) ^ 2) * ((1 - (n : ℚ) / k) / (1 + (n : ℚ) / k)) *
      ∏ i ∈ Icc 1 (k - 1), (1 - 3 * (n : ℚ) / i + 2 * (n : ℚ) ^ 2 / i ^ 2)

lemma prod_quad_factor (n k : ℕ) :
    ∏ i ∈ Icc 1 (k - 1), (1 - 3 * (n : ℚ) / i + 2 * (n : ℚ) ^ 2 / i ^ 2) =
      (∏ i ∈ Icc 1 (k - 1), (1 - (n : ℚ) / i)) *
        ∏ i ∈ Icc 1 (k - 1), (1 - 2 * (n : ℚ) / i) := by
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  have hi0 : (i : ℚ) ≠ 0 := by
    simp only [mem_Icc] at hi
    exact_mod_cast (show i ≠ 0 by omega)
  field_simp [hi0]
  ring

lemma Icc_succ_split (k : ℕ) (hk : 1 ≤ k) :
    Icc 1 k = insert k (Icc 1 (k - 1)) := by
  ext x
  simp only [mem_insert, mem_Icc]
  omega

/-- Ratio of a positive-index summand of `S2` to `S1`. -/
lemma S2_summand_ratio (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n - 1) :
    ((n - 1).choose k * (n + k - 1).choose k * (3 * n).choose (n + k) : ℚ) /
      (3 * n).choose n =
      - (2 * (n : ℚ) ^ 2 / (k : ℚ) ^ 2) * ((1 - (n : ℚ) / k) / (1 + (n : ℚ) / k)) *
        ∏ i ∈ Icc 1 (k - 1), (1 - 3 * (n : ℚ) / i + 2 * (n : ℚ) ^ 2 / i ^ 2) := by
  have hkn' : k ≤ 2 * n := by omega
  have h1 := choose_pred_eq_prod n k hn hkn
  have h2 := choose_rep_eq_prod n k hn hk
  have h3 := choose_three_ratio n k hn hk hkn'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hS : ((3 * n).choose n : ℚ) ≠ 0 := by
    exact_mod_cast (choose_pos (by omega : n ≤ 3 * n)).ne'
  have hsplit : ∏ i ∈ Icc 1 k, (1 - (n : ℚ) / i) =
      (1 - (n : ℚ) / k) * ∏ i ∈ Icc 1 (k - 1), (1 - (n : ℚ) / i) := by
    rw [Icc_succ_split k hk, prod_insert (by simp [mem_Icc]; omega)]
  have hsign : (-1 : ℚ) ^ k * (-1 : ℚ) ^ (k - 1) = -1 := by
    rw [← pow_add]
    have : k + (k - 1) = 2 * (k - 1) + 1 := by omega
    rw [this, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  have hnk0 : 1 + (n : ℚ) / k ≠ 0 := by
    have hknz : (k : ℚ) + n ≠ 0 := by
      have : (0 : ℕ) < k + n := by omega
      exact_mod_cast this.ne'
    have : 1 + (n : ℚ) / k = (k + n) / k := by field_simp [hk0]
    rw [this]
    exact div_ne_zero hknz hk0
  calc
    ((n - 1).choose k * (n + k - 1).choose k * (3 * n).choose (n + k) : ℚ) /
        (3 * n).choose n =
      ((n - 1).choose k : ℚ) * ((n + k - 1).choose k : ℚ) *
        (((3 * n).choose (n + k) : ℚ) / (3 * n).choose n) := by
      field_simp [hS]
    _ = ((-1 : ℚ) ^ k * ∏ i ∈ Icc 1 k, (1 - (n : ℚ) / i)) *
          ((n : ℚ) / k * ∏ i ∈ Icc 1 (k - 1), (1 + (n : ℚ) / i)) *
          ((2 * (n : ℚ) / (n + k)) * (-1 : ℚ) ^ (k - 1) *
            ∏ i ∈ Icc 1 (k - 1), (1 - 2 * (n : ℚ) / i) / (1 + (n : ℚ) / i)) := by
      rw [h1, h2, h3]
    _ = ((-1 : ℚ) ^ k * ((1 - (n : ℚ) / k) * ∏ i ∈ Icc 1 (k - 1), (1 - (n : ℚ) / i))) *
          ((n : ℚ) / k * ∏ i ∈ Icc 1 (k - 1), (1 + (n : ℚ) / i)) *
          ((2 * (n : ℚ) / (n + k)) * (-1 : ℚ) ^ (k - 1) *
            ∏ i ∈ Icc 1 (k - 1), (1 - 2 * (n : ℚ) / i) / (1 + (n : ℚ) / i)) := by
      rw [hsplit]
    _ = - (2 * (n : ℚ) ^ 2 / (k : ℚ) ^ 2) * ((1 - (n : ℚ) / k) / (1 + (n : ℚ) / k)) *
          ∏ i ∈ Icc 1 (k - 1), (1 - 3 * (n : ℚ) / i + 2 * (n : ℚ) ^ 2 / i ^ 2) := by
      set P1 := ∏ i ∈ Icc 1 (k - 1), (1 - (n : ℚ) / i)
      set Q := ∏ i ∈ Icc 1 (k - 1), (1 + (n : ℚ) / i)
      set R := ∏ i ∈ Icc 1 (k - 1), (1 - 2 * (n : ℚ) / i) / (1 + (n : ℚ) / i)
      set P2 := ∏ i ∈ Icc 1 (k - 1), (1 - 2 * (n : ℚ) / i)
      have hRQ : R * Q = P2 := by
        unfold R Q P2
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun i hi => ?_
        have hi0 : (i : ℚ) ≠ 0 := by
          simp only [mem_Icc] at hi
          exact_mod_cast (show i ≠ 0 by omega)
        have hqi : 1 + (n : ℚ) / i ≠ 0 := by
          have : (i : ℚ) + n ≠ 0 := by
            have : (0 : ℕ) < i + n := by
              simp only [mem_Icc] at hi; omega
            exact_mod_cast this.ne'
          have heq : 1 + (n : ℚ) / i = (i + n) / i := by field_simp [hi0]
          rw [heq]
          exact div_ne_zero this hi0
        field_simp [hqi]
      have hnk : ((n : ℚ) + k) = (n + k : ℕ) := by push_cast; rfl
      have hnk0' : (n : ℚ) + k ≠ 0 := by
        rw [hnk]; exact_mod_cast (show n + k ≠ 0 by omega)
      have hfac :
          (n : ℚ) / k * (2 * (n : ℚ) / (n + k)) =
            (2 * (n : ℚ) ^ 2 / (k : ℚ) ^ 2) / (1 + (n : ℚ) / k) := by
        field_simp [hk0, hn0, hnk0, hnk0']
        ring
      rw [prod_quad_factor]
      -- LHS = (-1)^k * (1-n/k) * P1 * (n/k) * Q * (2n/(n+k)) * (-1)^{k-1} * R
      --     = [(-1)^k * (-1)^{k-1}] * (1-n/k) * (n/k * 2n/(n+k)) * P1 * (R*Q)
      --     = (-1) * (1-n/k) * ((2n²/k²)/(1+n/k)) * P1 * P2
      convert_to
        (-1 : ℚ) ^ k * (1 - (n : ℚ) / k) * P1 * ((n : ℚ) / k * Q) *
            (2 * (n : ℚ) / (n + k) * (-1 : ℚ) ^ (k - 1) * R) =
          - (2 * (n : ℚ) ^ 2 / (k : ℚ) ^ 2) *
            ((1 - (n : ℚ) / k) / (1 + (n : ℚ) / k)) * (P1 * P2)
      · ring
      have hrearr :
          (-1 : ℚ) ^ k * (1 - (n : ℚ) / k) * P1 * ((n : ℚ) / k * Q) *
              (2 * (n : ℚ) / (n + k) * (-1 : ℚ) ^ (k - 1) * R) =
            (-1 : ℚ) ^ k * (-1 : ℚ) ^ (k - 1) * (1 - (n : ℚ) / k) *
              ((n : ℚ) / k * (2 * (n : ℚ) / (n + k))) * P1 * (R * Q) := by
        ring
      rw [hrearr, hsign, hfac, hRQ]
      ring

lemma S2_eq_S1_mul_W (n : ℕ) (hn : 1 ≤ n) :
    (S2 n : ℚ) = (S1 n : ℚ) * (1 - 2 * (n : ℚ) ^ 2 * Wrat n) := by
  have hS1 : (S1 n : ℚ) = (3 * n).choose n := by
    exact_mod_cast S1_eq_choose n hn
  have hS2 : (S2 n : ℚ) =
      ∑ m ∈ range n,
        ((n - 1).choose m * (n + m - 1).choose m * (3 * n).choose (n + m) : ℚ) := by
    exact_mod_cast S2_eq_sum n hn
  rw [hS2, hS1]
  have h0 : (0 : ℕ) ∈ range n := mem_range.mpr (by omega)
  rw [← sum_erase_add (range n) _ h0]
  have hz : ((n - 1).choose 0 * (n + 0 - 1).choose 0 * (3 * n).choose (n + 0) : ℚ) =
      (3 * n).choose n := by
    simp
  rw [hz]
  have herase : (range n).erase 0 = Icc 1 (n - 1) := by
    ext x
    simp only [mem_erase, mem_range, mem_Icc]
    omega
  rw [herase]
  have hS : ((3 * n).choose n : ℚ) ≠ 0 := by
    exact_mod_cast (choose_pos (by omega : n ≤ 3 * n)).ne'
  have hrest :
      ∑ m ∈ Icc 1 (n - 1),
          ((n - 1).choose m * (n + m - 1).choose m * (3 * n).choose (n + m) : ℚ) =
        (3 * n).choose n * (- (2 * (n : ℚ) ^ 2 * Wrat n)) := by
    have : ∑ m ∈ Icc 1 (n - 1),
        ((n - 1).choose m * (n + m - 1).choose m * (3 * n).choose (n + m) : ℚ) =
        ∑ m ∈ Icc 1 (n - 1),
          ((3 * n).choose n : ℚ) *
            (- (2 * (n : ℚ) ^ 2 / (m : ℚ) ^ 2) * ((1 - (n : ℚ) / m) / (1 + (n : ℚ) / m)) *
              ∏ i ∈ Icc 1 (m - 1), (1 - 3 * (n : ℚ) / i + 2 * (n : ℚ) ^ 2 / i ^ 2)) := by
      refine sum_congr rfl fun m hm => ?_
      simp only [mem_Icc] at hm
      have hm1 : 1 ≤ m := hm.1
      have hm2 : m ≤ n - 1 := hm.2
      have hr := S2_summand_ratio n m hn hm1 hm2
      have : ((n - 1).choose m * (n + m - 1).choose m * (3 * n).choose (n + m) : ℚ) =
          ((3 * n).choose n : ℚ) *
            (((n - 1).choose m * (n + m - 1).choose m * (3 * n).choose (n + m) : ℚ) /
              (3 * n).choose n) := by
        field_simp [hS]
      rw [this, hr]
    rw [this, ← mul_sum]
    congr 1
    have hterm : ∀ m ∈ Icc 1 (n - 1),
        - (2 * (n : ℚ) ^ 2 / (m : ℚ) ^ 2) * ((1 - (n : ℚ) / m) / (1 + (n : ℚ) / m)) *
            ∏ i ∈ Icc 1 (m - 1), (1 - 3 * (n : ℚ) / i + 2 * (n : ℚ) ^ 2 / i ^ 2) =
          - (2 * (n : ℚ) ^ 2) *
            ((1 / (m : ℚ) ^ 2) * ((1 - (n : ℚ) / m) / (1 + (n : ℚ) / m)) *
              ∏ i ∈ Icc 1 (m - 1), (1 - 3 * (n : ℚ) / i + 2 * (n : ℚ) ^ 2 / i ^ 2)) := by
      intro m _; ring
    refine Eq.trans (sum_congr rfl hterm) ?_
    rw [← mul_sum]
    unfold Wrat
    ring
  rw [hrest]
  ring

lemma choose_three_n_eq_prod (n : ℕ) (hn : 1 ≤ n) :
    ((3 * n).choose n : ℚ) =
      3 * ∏ k ∈ Icc 1 (n - 1), (1 + 2 * (n : ℚ) / k) := by
  have hle : n ≤ 3 * n := by omega
  have c : ((3 * n).choose n : ℚ) =
      ((3 * n).factorial : ℚ) / (n.factorial * (2 * n).factorial) := by
    rw [cast_choose (K := ℚ) hle]
    have : 3 * n - n = 2 * n := by omega
    rw [this]
  -- (3n)! / (2n)! = (2n+1)*...*(3n) = (n+1).ascFactorial n wait
  -- (2n+1)*...*(3n) = (2n+1).ascFactorial n? 
  -- (2n+1).ascFactorial n = (2n+1)*(2n+2)*...*(2n+n) = (2n+1)*...*(3n) yes
  have htop : ((3 * n).factorial : ℚ) / (2 * n).factorial = (2 * n + 1).ascFactorial n := by
    have := factorial_mul_ascFactorial (2 * n) n
    have hn0 : ((2 * n).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
    have heq : ((2 * n).factorial : ℚ) * (2 * n + 1).ascFactorial n = (2 * n + n).factorial := by
      exact_mod_cast this
    have : 2 * n + n = 3 * n := by omega
    rw [this] at heq
    field_simp [hn0]
    exact heq.symm
  have hsplit : ((2 * n + 1).ascFactorial n : ℚ) =
      (3 * (n : ℚ)) * ∏ k ∈ Icc 1 (n - 1), ((2 * n : ℚ) + k) := by
    have hsucc : (2 * n + 1).ascFactorial n =
        (3 * n) * (2 * n + 1).ascFactorial (n - 1) := by
      have h := ascFactorial_succ (n := 2 * n + 1) (k := n - 1)
      have hn1 : (n - 1).succ = n := Nat.sub_add_cancel hn
      rw [hn1] at h
      have hidx : 2 * n + 1 + (n - 1) = 3 * n := by omega
      rwa [hidx] at h
    rw [hsucc]
    push_cast
    have hprod : ((2 * n + 1).ascFactorial (n - 1) : ℚ) =
        ∏ k ∈ Icc 1 (n - 1), ((2 * n : ℚ) + k) := by
      rw [ascFactorial_cast_prod (2 * n) (n - 1)]
      rw [Icc_one_eq_image, prod_image add_one_injOn]
      refine prod_congr rfl fun j _ => ?_
      push_cast; ring
    rw [hprod]
  have hquot : ((3 * n).factorial : ℚ) / (n.factorial * (2 * n).factorial) =
      (((3 * n).factorial : ℚ) / (2 * n).factorial) / n.factorial := by
    have hn0 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero n
    have h2 : ((2 * n).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
    field_simp [hn0, h2]
  rw [c, hquot, htop, hsplit]
  have hn0 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero n
  have hnf : (n.factorial : ℚ) = n * (n - 1).factorial := by
    have : n = (n - 1) + 1 := by omega
    rw [this, factorial_succ]; push_cast; ring
  rw [hnf]
  have hden : ((n - 1).factorial : ℚ) = ∏ k ∈ Icc 1 (n - 1), (k : ℚ) :=
    (prod_Icc_cast (n - 1)).symm
  have hpr : ∏ k ∈ Icc 1 (n - 1), (1 + 2 * (n : ℚ) / k) =
      ∏ k ∈ Icc 1 (n - 1), ((2 * n : ℚ) + k) / k := by
    refine prod_congr rfl fun k hk => ?_
    have hk0 : (k : ℚ) ≠ 0 := by
      simp only [mem_Icc] at hk
      exact_mod_cast (show k ≠ 0 by omega)
    field_simp [hk0]
    ring
  rw [hpr, prod_div_distrib, hden]
  have hn0' : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hf' : ((n - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  field_simp [hn0', hf']

/-- `β = C(3n,n)/3`. -/
def betaRat (n : ℕ) : ℚ := (3 * n).choose n / 3

lemma betaRat_eq_prod (n : ℕ) (hn : 1 ≤ n) :
    betaRat n = ∏ k ∈ Icc 1 (n - 1), (1 + 2 * (n : ℚ) / k) := by
  unfold betaRat
  have hprod := choose_three_n_eq_prod n hn
  have h3 : (3 : ℚ) ≠ 0 := by norm_num
  field_simp [h3]
  linarith [hprod]

noncomputable def ratZMod (q : ℕ) [NeZero q] (a : ℚ) : ZMod q :=
  a.num * (a.den : ZMod q)⁻¹

lemma ratZMod_nat (q n : ℕ) [NeZero q] : ratZMod q n = n := by
  simp [ratZMod]

lemma ratZMod_int (q : ℕ) [NeZero q] (z : ℤ) : ratZMod q z = z := by
  simp [ratZMod]

lemma ratZMod_zero (q : ℕ) [NeZero q] : ratZMod q 0 = 0 := by
  simp [ratZMod]

lemma ratZMod_one (q : ℕ) [NeZero q] : ratZMod q 1 = 1 := by
  simp [ratZMod]

lemma isUnit_natCast_of_dvd {q n m : ℕ} [NeZero q] (hdvd : n ∣ m)
    (hu : IsUnit (m : ZMod q)) : IsUnit (n : ZMod q) := by
  obtain ⟨k, hk⟩ := hdvd
  have hcomm : Commute (n : ZMod q) (k : ZMod q) := Commute.all _ _
  rw [hk, Nat.cast_mul, hcomm.isUnit_mul_iff] at hu
  exact hu.1

lemma den_isUnit_of_mul {q : ℕ} [NeZero q] {a b : ℚ}
    (ha : IsUnit (a.den : ZMod q)) (hb : IsUnit (b.den : ZMod q)) :
    IsUnit ((a * b).den : ZMod q) :=
  isUnit_natCast_of_dvd (Rat.mul_den_dvd a b) (by rw [Nat.cast_mul]; exact ha.mul hb)

lemma den_isUnit_of_add {q : ℕ} [NeZero q] {a b : ℚ}
    (ha : IsUnit (a.den : ZMod q)) (hb : IsUnit (b.den : ZMod q)) :
    IsUnit ((a + b).den : ZMod q) :=
  isUnit_natCast_of_dvd (Rat.add_den_dvd a b) (by rw [Nat.cast_mul]; exact ha.mul hb)

lemma den_isUnit_of_sub {q : ℕ} [NeZero q] {a b : ℚ}
    (ha : IsUnit (a.den : ZMod q)) (hb : IsUnit (b.den : ZMod q)) :
    IsUnit ((a - b).den : ZMod q) :=
  isUnit_natCast_of_dvd (Rat.sub_den_dvd a b) (by rw [Nat.cast_mul]; exact ha.mul hb)

lemma ratZMod_mul_den {q : ℕ} [NeZero q] (a : ℚ) (ha : IsUnit (a.den : ZMod q)) :
    ratZMod q a * (a.den : ZMod q) = (a.num : ZMod q) := by
  rw [ratZMod, mul_assoc, ZMod.inv_mul_of_unit _ ha, mul_one]

lemma isUnit_natAbs_iff {q : ℕ} [NeZero q] (n : ℤ) :
    IsUnit (n.natAbs : ZMod q) ↔ IsUnit (n : ZMod q) := by
  have h : (n.natAbs : ZMod q) = n ∨ (n.natAbs : ZMod q) = -n := by
    rcases le_or_gt 0 n with hn | hn
    · left
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hn]
    · right
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hn, Int.cast_neg]
  rcases h with h | h
  · rw [h]
  · rw [h, IsUnit.neg_iff]

lemma ratZMod_eq_div {q : ℕ} [NeZero q] (n : ℤ) {d : ℕ}
    (hd0 : d ≠ 0) (hd : IsUnit (d : ZMod q)) :
    ratZMod q ((n : ℚ) / d) = (n : ZMod q) * (d : ZMod q)⁻¹ := by
  have hd0z : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  obtain ⟨c, hn, hden⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den n hd0z
  set a : ℚ := (n : ℚ) / d
  have hdZ : (d : ZMod q) = (c : ZMod q) * (a.den : ZMod q) := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) hden
    push_cast at this
    exact this
  have hcu := (Commute.all (c : ZMod q) (a.den : ZMod q)).isUnit_mul_iff.mp (hdZ ▸ hd)
  have hc : IsUnit (c : ZMod q) := hcu.1
  have ha : IsUnit (a.den : ZMod q) := hcu.2
  have hnZ : (n : ZMod q) = (c : ZMod q) * (a.num : ZMod q) := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) hn
    push_cast at this
    exact this
  have hinv : ((c : ZMod q) * (a.den : ZMod q))⁻¹ =
      (a.den : ZMod q)⁻¹ * (c : ZMod q)⁻¹ := by
    refine ZMod.inv_eq_of_mul_eq_one q _ _ ?_
    rw [mul_assoc, ← mul_assoc (a.den : ZMod q), ZMod.mul_inv_of_unit _ ha, one_mul,
      ZMod.mul_inv_of_unit _ hc]
  refine ha.mul_left_inj.mp ?_
  rw [ratZMod_mul_den a ha, hnZ, hdZ, hinv]
  have : (c : ZMod q) * (a.num : ZMod q) * ((a.den : ZMod q)⁻¹ * (c : ZMod q)⁻¹) *
      (a.den : ZMod q) =
      ((c : ZMod q) * (c : ZMod q)⁻¹) * (a.num : ZMod q) *
        ((a.den : ZMod q)⁻¹ * (a.den : ZMod q)) := by ring
  rw [this, ZMod.mul_inv_of_unit _ hc, ZMod.inv_mul_of_unit _ ha, one_mul, mul_one]

lemma ratZMod_mul {q : ℕ} [NeZero q] {a b : ℚ}
    (ha : IsUnit (a.den : ZMod q)) (hb : IsUnit (b.den : ZMod q)) :
    ratZMod q (a * b) = ratZMod q a * ratZMod q b := by
  have hab : IsUnit ((a * b).den : ZMod q) := den_isUnit_of_mul ha hb
  have hZ : ((a * b).num : ZMod q) * (a.den : ZMod q) * (b.den : ZMod q) =
      (a.num : ZMod q) * (b.num : ZMod q) * ((a * b).den : ZMod q) := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) (Rat.mul_num_den' a b)
    push_cast at this
    exact this
  have hL := ratZMod_mul_den (a * b) hab
  have hA := ratZMod_mul_den a ha
  have hB := ratZMod_mul_den b hb
  have hcancel :
      ratZMod q (a * b) * ((a * b).den : ZMod q) * (a.den : ZMod q) * (b.den : ZMod q) =
        ratZMod q a * ratZMod q b * ((a * b).den : ZMod q) * (a.den : ZMod q) *
          (b.den : ZMod q) := by
    calc
      ratZMod q (a * b) * ((a * b).den : ZMod q) * (a.den : ZMod q) * (b.den : ZMod q)
          = ((a * b).num : ZMod q) * (a.den : ZMod q) * (b.den : ZMod q) := by
            rw [hL]
      _ = (a.num : ZMod q) * (b.num : ZMod q) * ((a * b).den : ZMod q) := hZ
      _ = (ratZMod q a * (a.den : ZMod q)) * (ratZMod q b * (b.den : ZMod q)) *
            ((a * b).den : ZMod q) := by rw [hA, hB]
      _ = ratZMod q a * ratZMod q b * ((a * b).den : ZMod q) * (a.den : ZMod q) *
            (b.den : ZMod q) := by ring
  exact hab.mul_right_cancel <| ha.mul_right_cancel <| hb.mul_right_cancel hcancel

lemma ratZMod_add {q : ℕ} [NeZero q] {a b : ℚ}
    (ha : IsUnit (a.den : ZMod q)) (hb : IsUnit (b.den : ZMod q)) :
    ratZMod q (a + b) = ratZMod q a + ratZMod q b := by
  have hab : IsUnit ((a + b).den : ZMod q) := den_isUnit_of_add ha hb
  have hZ : ((a + b).num : ZMod q) * (a.den : ZMod q) * (b.den : ZMod q) =
      ((a.num : ZMod q) * (b.den : ZMod q) + (b.num : ZMod q) * (a.den : ZMod q)) *
        ((a + b).den : ZMod q) := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) (Rat.add_num_den' a b)
    push_cast at this
    exact this
  have hL := ratZMod_mul_den (a + b) hab
  have hA := ratZMod_mul_den a ha
  have hB := ratZMod_mul_den b hb
  have hcancel :
      ratZMod q (a + b) * ((a + b).den : ZMod q) * (a.den : ZMod q) * (b.den : ZMod q) =
        (ratZMod q a + ratZMod q b) * ((a + b).den : ZMod q) * (a.den : ZMod q) *
          (b.den : ZMod q) := by
    calc
      ratZMod q (a + b) * ((a + b).den : ZMod q) * (a.den : ZMod q) * (b.den : ZMod q)
          = ((a + b).num : ZMod q) * (a.den : ZMod q) * (b.den : ZMod q) := by
            rw [hL]
      _ = ((a.num : ZMod q) * (b.den : ZMod q) + (b.num : ZMod q) * (a.den : ZMod q)) *
            ((a + b).den : ZMod q) := hZ
      _ = ((ratZMod q a * (a.den : ZMod q)) * (b.den : ZMod q) +
            (ratZMod q b * (b.den : ZMod q)) * (a.den : ZMod q)) *
            ((a + b).den : ZMod q) := by rw [hA, hB]
      _ = (ratZMod q a + ratZMod q b) * ((a + b).den : ZMod q) * (a.den : ZMod q) *
            (b.den : ZMod q) := by ring
  exact hab.mul_right_cancel <| ha.mul_right_cancel <| hb.mul_right_cancel hcancel

lemma ratZMod_neg {q : ℕ} [NeZero q] (a : ℚ) :
    ratZMod q (-a) = -ratZMod q a := by
  simp [ratZMod, Rat.neg_num]

lemma ratZMod_sub {q : ℕ} [NeZero q] {a b : ℚ}
    (ha : IsUnit (a.den : ZMod q)) (hb : IsUnit (b.den : ZMod q)) :
    ratZMod q (a - b) = ratZMod q a - ratZMod q b := by
  rw [sub_eq_add_neg, ratZMod_add ha (by simpa [Rat.neg_den] using hb), ratZMod_neg,
    sub_eq_add_neg]

lemma ratZMod_inv {q : ℕ} [NeZero q] {a : ℚ} (ha0 : a ≠ 0)
    (ha : IsUnit (a.den : ZMod q)) (hn : IsUnit (a.num : ZMod q)) :
    ratZMod q a⁻¹ = (ratZMod q a)⁻¹ := by
  have hainv : IsUnit ((a⁻¹).den : ZMod q) := by
    rw [Rat.den_inv_of_ne_zero ha0]
    exact (isUnit_natAbs_iff a.num).mpr hn
  have hmul : ratZMod q a * ratZMod q a⁻¹ = 1 := by
    rw [← ratZMod_mul ha hainv, mul_inv_cancel₀ ha0, ratZMod_one]
  exact (ZMod.inv_eq_of_mul_eq_one q (ratZMod q a) (ratZMod q a⁻¹) hmul).symm

lemma ratZMod_div {q : ℕ} [NeZero q] {a b : ℚ} (hb0 : b ≠ 0)
    (ha : IsUnit (a.den : ZMod q)) (hb : IsUnit (b.den : ZMod q))
    (hn : IsUnit (b.num : ZMod q)) :
    ratZMod q (a / b) = ratZMod q a * (ratZMod q b)⁻¹ := by
  rw [div_eq_mul_inv, ratZMod_mul ha, ratZMod_inv hb0 hb hn]
  · rw [Rat.den_inv_of_ne_zero hb0]
    exact (isUnit_natAbs_iff b.num).mpr hn

lemma den_isUnit_pow {q : ℕ} [NeZero q] {a : ℚ} (ha : IsUnit (a.den : ZMod q)) :
    ∀ n : ℕ, IsUnit ((a ^ n).den : ZMod q)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ]
    exact den_isUnit_of_mul (den_isUnit_pow ha n) ha

lemma ratZMod_pow {q : ℕ} [NeZero q] {a : ℚ} (ha : IsUnit (a.den : ZMod q)) (n : ℕ) :
    ratZMod q (a ^ n) = ratZMod q a ^ n := by
  induction n with
  | zero => simp [ratZMod_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, ratZMod_mul (den_isUnit_pow ha n) ha, ih]

lemma den_isUnit_sum {q : ℕ} [NeZero q] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsUnit ((f i).den : ZMod q)) :
    IsUnit ((∑ i ∈ s, f i).den : ZMod q) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact den_isUnit_of_add (hf a (mem_insert_self _ _))
      (ih (fun i hi => hf i (mem_insert_of_mem hi)))

lemma ratZMod_sum {q : ℕ} [NeZero q] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsUnit ((f i).den : ZMod q)) :
    ratZMod q (∑ i ∈ s, f i) = ∑ i ∈ s, ratZMod q (f i) := by
  induction s using Finset.induction with
  | empty => simp [ratZMod_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha,
      ratZMod_add (hf a (mem_insert_self _ _))
        (den_isUnit_sum s f (fun i hi => hf i (mem_insert_of_mem hi))),
      ih (fun i hi => hf i (mem_insert_of_mem hi))]

lemma den_isUnit_prod {q : ℕ} [NeZero q] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsUnit ((f i).den : ZMod q)) :
    IsUnit ((∏ i ∈ s, f i).den : ZMod q) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact den_isUnit_of_mul (hf a (mem_insert_self _ _))
      (ih (fun i hi => hf i (mem_insert_of_mem hi)))

lemma ratZMod_prod {q : ℕ} [NeZero q] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, IsUnit ((f i).den : ZMod q)) :
    ratZMod q (∏ i ∈ s, f i) = ∏ i ∈ s, ratZMod q (f i) := by
  induction s using Finset.induction with
  | empty => simp [ratZMod_one]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha,
      ratZMod_mul (hf a (mem_insert_self _ _))
        (den_isUnit_prod s f (fun i hi => hf i (mem_insert_of_mem hi))),
      ih (fun i hi => hf i (mem_insert_of_mem hi))]

lemma neZero_pow_of_prime {p r : ℕ} [Fact p.Prime] : NeZero (p ^ r) :=
  ⟨pow_ne_zero r (Nat.Prime.ne_zero Fact.out)⟩

lemma isUnit_natCast_of_lt {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : 0 < k) (hkp : k < p) : IsUnit (k : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right r <|
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk hkp)).symm

lemma mem_Icc_lt_prime {p k : ℕ} [Fact p.Prime] (hk : k ∈ Icc 1 (p - 1)) :
    0 < k ∧ k < p := by
  have := mem_Icc.mp hk
  have : 1 ≤ p := (Fact.out : p.Prime).one_le
  omega

lemma isUnit_of_mem_Icc {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) : IsUnit (k : ZMod (p ^ r)) :=
  isUnit_natCast_of_lt (mem_Icc_lt_prime hk).1 (mem_Icc_lt_prime hk).2

lemma isUnit_two_zmod {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] (hp : 2 < p) :
    IsUnit (2 : ZMod (p ^ r)) :=
  isUnit_natCast_of_lt (by norm_num) hp

lemma isUnit_three_zmod {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] (hp : 3 < p) :
    IsUnit (3 : ZMod (p ^ r)) :=
  isUnit_natCast_of_lt (by norm_num) hp

lemma pow_p_mul_eq_zero {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (a : ZMod (p ^ r)) : ((p : ZMod (p ^ r)) * a) ^ r = 0 := by
  rw [mul_pow]
  have : (p : ZMod (p ^ r)) ^ r = 0 := by
    rw [← Nat.cast_pow]
    exact CharP.cast_eq_zero (ZMod (p ^ r)) _
  rw [this, zero_mul]

lemma inv_one_sub_of_pow_eq_zero {q n : ℕ} [NeZero q] (x : ZMod q)
    (hx : x ^ n = 0) : (1 - x)⁻¹ = ∑ i ∈ range n, x ^ i := by
  refine ZMod.inv_eq_of_mul_eq_one q _ _ ?_
  rw [mul_comm, geom_sum_mul_neg, hx, sub_zero]

lemma inv_one_add_of_pow_eq_zero {q n : ℕ} [NeZero q] (x : ZMod q)
    (hx : x ^ n = 0) : (1 + x)⁻¹ = ∑ i ∈ range n, (-x) ^ i := by
  have hx' : (-x) ^ n = 0 := by rw [neg_pow, hx, mul_zero]
  have : (1 + x) = 1 - (-x) := by ring
  rw [this, inv_one_sub_of_pow_eq_zero (-x) hx']

/-- Cast of a `ZMod (p^a)` element to `ZMod (p^b)` when `b ≤ a`. -/
lemma eq_mul_pow_of_cast_eq_zero {a b : ℕ} [NeZero a] [NeZero b] (hba : b ∣ a)
    {x : ZMod a} (hx : ZMod.castHom hba (ZMod b) x = 0) :
    ∃ y : ZMod a, x = (b : ZMod a) * y := by
  have : (x.val : ZMod b) = 0 := by
    simpa [ZMod.castHom_apply, ZMod.natCast_val] using hx
  have hdvd : b ∣ x.val := (CharP.cast_eq_zero_iff (ZMod b) b x.val).mp this
  obtain ⟨y, hy⟩ := hdvd
  refine ⟨y, ?_⟩
  rw [← ZMod.natCast_zmod_val x, hy, Nat.cast_mul]

lemma castHom_inv {a b k : ℕ} [NeZero a] [NeZero b] (hba : b ∣ a)
    (hu : IsUnit (k : ZMod a)) :
    ZMod.castHom hba (ZMod b) (k : ZMod a)⁻¹ = (k : ZMod b)⁻¹ := by
  have h := ZMod.inv_eq_of_mul_eq_one b (k : ZMod b)
    (ZMod.castHom hba (ZMod b) (k : ZMod a)⁻¹) ?_
  · exact h.symm
  · have : (k : ZMod b) = ZMod.castHom hba (ZMod b) (k : ZMod a) := by
      rw [ZMod.castHom_apply, ZMod.cast_natCast hba]
    rw [this, ← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]

def harmZ (p r m n : ℕ) [NeZero (p ^ r)] : ZMod (p ^ r) :=
  ∑ k ∈ Icc 1 n, ((k : ZMod (p ^ r))⁻¹) ^ m

def SZ (p r : ℕ) [NeZero (p ^ r)] : ZMod (p ^ r) :=
  ∑ k ∈ Icc 1 (p - 1), harmZ p r 1 (k - 1) * ((k : ZMod (p ^ r))⁻¹) ^ 2

def betaZ (p r : ℕ) [NeZero (p ^ r)] : ZMod (p ^ r) :=
  ∏ k ∈ Icc 1 (p - 1), (1 + (2 : ZMod (p ^ r)) * p * (k : ZMod (p ^ r))⁻¹)

def Wz (p r : ℕ) [NeZero (p ^ r)] : ZMod (p ^ r) :=
  ∑ k ∈ Icc 1 (p - 1),
    ((k : ZMod (p ^ r))⁻¹) ^ 2 *
      ((1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
        (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)⁻¹) *
      ∏ i ∈ Icc 1 (k - 1),
        (1 - (3 : ZMod (p ^ r)) * p * (i : ZMod (p ^ r))⁻¹ +
          (2 : ZMod (p ^ r)) * p ^ 2 * ((i : ZMod (p ^ r))⁻¹) ^ 2)

lemma Icc_image_eq_nonzero (p : ℕ) [Fact p.Prime] [NeZero p] :
    (Icc 1 (p - 1)).image (fun k : ℕ => (k : ZMod p)) =
      (univ : Finset (ZMod p)).filter (fun x => x ≠ 0) := by
  ext x
  simp only [mem_image, mem_Icc, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨k, ⟨hk1, hkp⟩, rfl⟩
    have hp := Fact.out (p := p.Prime)
    have : k < p := by omega
    exact (CharP.cast_eq_zero_iff (ZMod p) p k).not.mpr (Nat.not_dvd_of_pos_of_lt hk1 this)
  · intro hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    have hpos : 0 < x.val := Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero x).mp hx)
    have hlt : x.val < p := ZMod.val_lt x
    have : 1 ≤ p := (Fact.out : p.Prime).one_le
    omega

lemma sum_Icc_eq_sum_nonzero {α : Type*} [AddCommMonoid α] {p : ℕ}
    [Fact p.Prime] [NeZero p] (f : ZMod p → α) :
    ∑ k ∈ Icc 1 (p - 1), f (k : ZMod p) = ∑ x ∈ univ.filter (fun x : ZMod p => x ≠ 0), f x := by
  rw [← sum_image]
  · rw [Icc_image_eq_nonzero]
  · intro a ha b hb h
    have ha' := mem_Icc_lt_prime (p := p) ha
    have hb' := mem_Icc_lt_prime (p := p) hb
    have hab : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp h
    have ha_mod : a % p = a := Nat.mod_eq_of_lt ha'.2
    have hb_mod : b % p = b := Nat.mod_eq_of_lt hb'.2
    rwa [Nat.ModEq, ha_mod, hb_mod] at hab

lemma sum_nonzero_eq_sum_units {α : Type*} [AddCommMonoid α] {p : ℕ}
    [Fact p.Prime] (f : ZMod p → α) :
    ∑ x ∈ univ.filter (fun x : ZMod p => x ≠ 0), f x = ∑ u : (ZMod p)ˣ, f u := by
  have himg : (univ : Finset (ZMod p)ˣ).image Units.val =
      univ.filter (fun x : ZMod p => x ≠ 0) := by
    ext x
    simp only [mem_image, mem_univ, true_and, mem_filter, Units.val]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero,
      fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [← himg, sum_image]
  intro u _ v _ h
  exact Units.ext h

lemma sum_pow_Icc {p : ℕ} [Fact p.Prime] [NeZero p] (i : ℕ) :
    ∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ i =
      if p - 1 ∣ i then -1 else 0 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have := FiniteField.sum_pow_units (ZMod p) i
  rw [hcard] at this
  have h1 : ∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ i =
      ∑ u : (ZMod p)ˣ, ((u : ZMod p) ^ i) := by
    rw [sum_Icc_eq_sum_nonzero (fun x => x ^ i), sum_nonzero_eq_sum_units]
  rw [h1, this]

lemma isUnit_zmod_prime {p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Icc 1 (p - 1)) : IsUnit (k : ZMod p) := by
  have h := mem_Icc_lt_prime (p := p) hk
  rw [ZMod.isUnit_iff_coprime]
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt h.1 h.2)).symm

lemma sum_inv_pow_Icc {p m : ℕ} [Fact p.Prime] [NeZero p] (hm : m < p - 1) :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ m = if m = 0 then -1 else 0 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases hm0 : m = 0
  · subst hm0
    simp only [pow_zero, sum_const, nsmul_one]
    have hcard : #(Icc 1 (p - 1)) = p - 1 := by simp [Nat.card_Icc]
    rw [hcard]
    have : ((p - 1 : ℕ) : ZMod p) = -1 := by
      rw [Nat.cast_sub (Nat.le_of_lt hp), Nat.cast_one, CharP.cast_eq_zero, zero_sub]
    simpa [this]
  · have hfermat : ∀ k ∈ Icc 1 (p - 1),
        ((k : ZMod p)⁻¹) ^ m = (k : ZMod p) ^ (p - 1 - m) := by
      intro k hk
      have hu : IsUnit (k : ZMod p) := isUnit_zmod_prime hk
      have hpow : (k : ZMod p) ^ (p - 1) = 1 :=
        ZMod.pow_card_sub_one_eq_one hu.ne_zero
      refine (hu.pow m).mul_left_inj.mp ?_
      rw [← mul_pow, ZMod.inv_mul_of_unit _ hu, one_pow, ← pow_add]
      have : p - 1 - m + m = p - 1 := by omega
      rw [this, hpow]
    rw [sum_congr rfl hfermat, sum_pow_Icc]
    have : ¬ p - 1 ∣ p - 1 - m := by
      intro h
      have : p - 1 ≤ p - 1 - m := Nat.le_of_dvd (by omega) h
      omega
    simp [this, hm0]

lemma harmFp_eq_zero {p m : ℕ} [Fact p.Prime] [NeZero p]
    (hm : 0 < m) (hm' : m < p - 1) :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ m = 0 := by
  rw [sum_inv_pow_Icc hm', if_neg hm.ne']

lemma castHom_harmZ {p r s m n : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero (p ^ s)]
    (hsr : s ≤ r) (hn : n < p) :
    ZMod.castHom (pow_dvd_pow p hsr) (ZMod (p ^ s)) (harmZ p r m n) = harmZ p s m n := by
  simp only [harmZ, map_sum]
  refine sum_congr rfl fun k hk => ?_
  have hkI : k ∈ Icc 1 (p - 1) := by
    have := mem_Icc.mp hk
    have : 1 ≤ p := (Fact.out : p.Prime).one_le
    simp only [mem_Icc]
    omega
  have hu : IsUnit (k : ZMod (p ^ r)) := isUnit_of_mem_Icc hkI
  rw [map_pow, castHom_inv (pow_dvd_pow p hsr) hu]

lemma inv_neg_of_unit {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    (-a)⁻¹ = -a⁻¹ :=
  ZMod.inv_eq_of_mul_eq_one q (-a) (-a⁻¹) (by
    rw [neg_mul_neg, ZMod.mul_inv_of_unit _ ha])

lemma inv_mul_of_units {q : ℕ} [NeZero q] {a b : ZMod q}
    (ha : IsUnit a) (hb : IsUnit b) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  ZMod.inv_eq_of_mul_eq_one q (a * b) (b⁻¹ * a⁻¹) (by
    rw [mul_assoc, ← mul_assoc b, ZMod.mul_inv_of_unit _ hb, one_mul,
      ZMod.mul_inv_of_unit _ ha])

lemma isUnit_one_sub_p_div {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by
  refine isUnit_iff_exists_inv.mpr
    ⟨∑ j ∈ range r, ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) ^ j, ?_⟩
  rw [mul_comm, geom_sum_mul_neg, pow_p_mul_eq_zero, sub_zero]

lemma p_sub_k_factor {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ((p - k : ℕ) : ZMod (p ^ r)) =
      -((k : ZMod (p ^ r)) * (1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)) := by
  have hu := isUnit_of_mem_Icc (p := p) (r := r) hk
  have hpk : k ≤ p := (mem_Icc_lt_prime (p := p) hk).2.le
  have hk1 : (k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hu
  rw [Nat.cast_sub hpk]
  calc
    (p : ZMod (p ^ r)) - k
        = -k + p * 1 := by ring
    _ = -k + p * ((k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by rw [hk1]
    _ = -((k : ZMod (p ^ r)) * (1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)) := by
          ring

lemma inv_p_sub {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ((p - k : ℕ) : ZMod (p ^ r))⁻¹ =
      -((k : ZMod (p ^ r))⁻¹) *
        ∑ j ∈ range r, ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) ^ j := by
  have hu := isUnit_of_mem_Icc (p := p) (r := r) hk
  have h1s := isUnit_one_sub_p_div (p := p) (r := r) hk
  have hx : ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) ^ r = 0 :=
    pow_p_mul_eq_zero _
  have hinv := inv_one_sub_of_pow_eq_zero
    ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) hx
  rw [p_sub_k_factor hk, inv_neg_of_unit (hu.mul h1s), inv_mul_of_units hu h1s, hinv]
  ring

lemma le_p_of_mem_Icc {p k : ℕ} [Fact p.Prime] (hk : k ∈ Icc 1 (p - 1)) : k ≤ p :=
  (mem_Icc_lt_prime (p := p) hk).2.le

lemma mem_Icc_p_sub {p k : ℕ} [Fact p.Prime] (hk : k ∈ Icc 1 (p - 1)) :
    p - k ∈ Icc 1 (p - 1) := by
  have h := mem_Icc.mp hk
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hk_le : k ≤ p := le_p_of_mem_Icc hk
  refine mem_Icc.mpr ⟨?_, ?_⟩
  · exact Nat.le_sub_of_add_le (by omega)
  · exact Nat.sub_le_sub_left h.1 p

lemma p_sub_p_sub_eq {p k : ℕ} (hk : k ≤ p) : p - (p - k) = k :=
  Nat.sub_sub_self hk

lemma sum_reflect_Icc {α : Type*} [AddCommMonoid α] {p : ℕ} [Fact p.Prime]
    (f : ℕ → α) :
    ∑ k ∈ Icc 1 (p - 1), f (p - k) = ∑ k ∈ Icc 1 (p - 1), f k := by
  refine (sum_nbij (fun k => p - k) ?_ ?_ ?_ ?_)
  · intro k hk; exact mem_Icc_p_sub hk
  · intro a ha b hb heq
    have ha' : a ≤ p := le_p_of_mem_Icc ha
    have hb' : b ≤ p := le_p_of_mem_Icc hb
    exact (tsub_right_inj ha' hb').mp heq
  · intro b hb
    refine ⟨p - b, mem_Icc_p_sub hb, ?_⟩
    exact p_sub_p_sub_eq (le_p_of_mem_Icc hb)
  · intro k hk; rfl

/-- Pairing: `k⁻¹ + (p-k)⁻¹ = -∑_{j=1}^{r-1} p^j k⁻(j+1)` in `ZMod (p^r)`. -/
lemma inv_add_inv_p_sub {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)] (hr : 0 < r)
    (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod (p ^ r))⁻¹ + ((p - k : ℕ) : ZMod (p ^ r))⁻¹ =
      -∑ j ∈ Icc 1 (r - 1),
        ((p : ZMod (p ^ r)) ^ j) * ((k : ZMod (p ^ r))⁻¹) ^ (j + 1) := by
  have hrange : range r = insert 0 (Icc 1 (r - 1)) := by
    ext x; simp only [mem_range, mem_insert, mem_Icc]; omega
  have hsum :
      ∑ j ∈ range r, ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) ^ j =
        1 + ∑ j ∈ Icc 1 (r - 1), ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) ^ j := by
    rw [hrange, sum_insert (by simp), pow_zero]
  rw [inv_p_sub hk, hsum]
  have hrearr :
      (k : ZMod (p ^ r))⁻¹ +
          (-((k : ZMod (p ^ r))⁻¹) *
            (1 + ∑ j ∈ Icc 1 (r - 1),
              ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) ^ j)) =
        -((k : ZMod (p ^ r))⁻¹ *
            ∑ j ∈ Icc 1 (r - 1),
              ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) ^ j) := by
    ring
  rw [hrearr, mul_sum]
  refine congrArg Neg.neg (sum_congr rfl fun j hj => ?_)
  rw [mul_pow]
  ring

/-- Wolstenholme: `H_{p-1}^{(m)} ≡ 0 (mod p)` for `0 < m < p-1`. -/
lemma harmFp_one_to_four {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 1 = 0) ∧
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = 0) ∧
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 3 = 0) ∧
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4 = 0) := by
  have h1 : 1 < p - 1 := by omega
  have h2 : 2 < p - 1 := by omega
  have h3 : 3 < p - 1 := by omega
  have h4 : 4 < p - 1 := by omega
  exact ⟨harmFp_eq_zero (by norm_num) h1,
    harmFp_eq_zero (by norm_num) h2,
    harmFp_eq_zero (by norm_num) h3,
    harmFp_eq_zero (by norm_num) h4⟩

lemma nat_cast_p_pow_eq_zero (p r : ℕ) [NeZero (p ^ r)] :
    (p : ZMod (p ^ r)) ^ r = 0 := by
  rw [← Nat.cast_pow]
  exact CharP.cast_eq_zero (ZMod (p ^ r)) _

lemma dvd_prime_self_pow {p r : ℕ} (hr : 0 < r) : p ∣ p ^ r :=
  dvd_pow_self p hr.ne'

lemma castHom_sum_inv_pow_Fp {p r m : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero p]
    (hr : 0 < r) :
    ZMod.castHom (dvd_prime_self_pow hr) (ZMod p)
      (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ r))⁻¹) ^ m) =
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ m := by
  rw [map_sum]
  refine sum_congr rfl fun k hk => ?_
  have hu := isUnit_of_mem_Icc (p := p) (r := r) hk
  rw [map_pow, castHom_inv (dvd_prime_self_pow hr) hu]

/-- If `x ≡ 0 (mod p)` in `ZMod (p^r)`, then `p^{r-1} * x = 0`. -/
lemma pow_mul_of_cast_mod_p {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero p]
    (hr : 1 ≤ r) {x : ZMod (p ^ r)}
    (hx : ZMod.castHom (dvd_prime_self_pow (by omega : 0 < r)) (ZMod p) x = 0) :
    (p : ZMod (p ^ r)) ^ (r - 1) * x = 0 := by
  obtain ⟨y, hy⟩ :=
    eq_mul_pow_of_cast_eq_zero (dvd_prime_self_pow (by omega : 0 < r)) hx
  rw [hy, ← mul_assoc, ← pow_succ]
  have : r - 1 + 1 = r := by omega
  rw [this, nat_cast_p_pow_eq_zero, zero_mul]

lemma two_mul_sum_reflect {p : ℕ} [Fact p.Prime] {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) :
    ∑ k ∈ Icc 1 (p - 1), (f k + f (p - k)) = 2 • ∑ k ∈ Icc 1 (p - 1), f k := by
  rw [sum_add_distrib, sum_reflect_Icc, two_nsmul]

/-- Pairing in `ZMod (p^2)`: `k⁻¹ + (p-k)⁻¹ = -p k⁻²`. -/
lemma inv_add_inv_p_sub_mod_p2 {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 2)]
    (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
      -((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
  have h := inv_add_inv_p_sub (p := p) (r := 2) (by norm_num) hk
  have : Icc 1 (2 - 1) = {1} := by simp
  rw [this, sum_singleton, pow_one] at h
  exact h

lemma p_pow_two_eq_zero (p : ℕ) [NeZero (p ^ 2)] :
    (p : ZMod (p ^ 2)) ^ 2 = 0 :=
  nat_cast_p_pow_eq_zero p 2

/-- `H^{(odd)} ≡ 0 (mod p²)` via pairing. -/
lemma harmZ_odd_mod_p2 {p : ℕ} [Fact p.Prime] [NeZero (p ^ 2)] (hp : 7 ≤ p) :
    harmZ p 2 1 (p - 1) = 0 ∧ harmZ p 2 3 (p - 1) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h2unit : IsUnit (2 : ZMod (p ^ 2)) := isUnit_two_zmod (by omega)
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := p_pow_two_eq_zero p
  -- H^{(1)}
  have hsum1 : 2 * harmZ p 2 1 (p - 1) =
      -((p : ZMod (p ^ 2)) * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
    unfold harmZ
    have hre := sum_reflect_Icc (p := p) (fun k => (k : ZMod (p ^ 2))⁻¹)
    have hpair := sum_congr rfl
      (fun k hk => inv_add_inv_p_sub_mod_p2 (p := p) hk)
    calc
      2 * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 1
          = 2 * ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ := by
            refine congrArg _ (sum_congr rfl fun k _ => pow_one _)
      _ = ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) := by
            rw [sum_add_distrib, hre]; ring
      _ = ∑ k ∈ Icc 1 (p - 1),
            -((p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2))⁻¹) ^ 2) := hpair
      _ = -((p : ZMod (p ^ 2)) *
            ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) := by
            rw [sum_neg_distrib, ← mul_sum]
  have h2cast :
      ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 2)) (ZMod p)
        (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2) = 0 := by
    rw [castHom_sum_inv_pow_Fp (by norm_num : 0 < 2)]
    exact (harmFp_one_to_four (p := p) hp).2.1
  have hpH2 : (p : ZMod (p ^ 2)) *
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 2 = 0 := by
    have := pow_mul_of_cast_mod_p (p := p) (r := 2) (by norm_num) h2cast
    simpa [pow_one] using this
  have hH1 : harmZ p 2 1 (p - 1) = 0 := by
    apply h2unit.mul_left_cancel
    rw [hsum1, hpH2, mul_zero, neg_zero]
  -- H^{(3)}
  have hpair3 : ∀ k ∈ Icc 1 (p - 1),
      ((k : ZMod (p ^ 2))⁻¹) ^ 3 + (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3 =
        -((3 : ZMod (p ^ 2)) * p * ((k : ZMod (p ^ 2))⁻¹) ^ 4) := by
    intro k hk
    have hpinv := inv_p_sub (p := p) (r := 2) hk
    have hsum : ∑ j ∈ range 2, ((p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) ^ j =
        1 + (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ := by
      simp [sum_range_succ, pow_zero, pow_one]
    rw [hpinv, hsum]
    have hp3 : (p : ZMod (p ^ 2)) ^ 3 = 0 :=
      pow_eq_zero_of_le (by norm_num : 2 ≤ 3) hp2
    ring_nf
    simp [hp2, hp3]
  have hsum3 : 2 * harmZ p 2 3 (p - 1) =
      -((3 : ZMod (p ^ 2)) * p *
        ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4) := by
    unfold harmZ
    have hre := sum_reflect_Icc (p := p) (fun k => ((k : ZMod (p ^ 2))⁻¹) ^ 3)
    have hpair := sum_congr rfl hpair3
    calc
      2 * ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 3
          = ∑ k ∈ Icc 1 (p - 1),
              (((k : ZMod (p ^ 2))⁻¹) ^ 3 +
                (((p - k : ℕ) : ZMod (p ^ 2))⁻¹) ^ 3) := by
            rw [sum_add_distrib, hre]; ring
      _ = ∑ k ∈ Icc 1 (p - 1),
            -((3 : ZMod (p ^ 2)) * p * ((k : ZMod (p ^ 2))⁻¹) ^ 4) := hpair
      _ = -((3 : ZMod (p ^ 2)) * p *
            ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4) := by
            rw [sum_neg_distrib, ← mul_sum]
  have h4cast :
      ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 2)) (ZMod p)
        (∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4) = 0 := by
    rw [castHom_sum_inv_pow_Fp (by norm_num : 0 < 2)]
    exact (harmFp_one_to_four (p := p) hp).2.2.2
  have hpH4 : (p : ZMod (p ^ 2)) *
      ∑ k ∈ Icc 1 (p - 1), ((k : ZMod (p ^ 2))⁻¹) ^ 4 = 0 := by
    have := pow_mul_of_cast_mod_p (p := p) (r := 2) (by norm_num) h4cast
    simpa [pow_one] using this
  have hH3 : harmZ p 2 3 (p - 1) = 0 := by
    apply h2unit.mul_left_cancel
    rw [hsum3, mul_assoc (3 : ZMod (p ^ 2)), hpH4, mul_zero, neg_zero]
    simp
  exact ⟨hH1, hH3⟩

/-- `p^n = 0` in `ZMod (p^r)` for `n ≥ r`. -/
lemma nat_cast_p_pow_eq_zero_of_le {p r n : ℕ} [NeZero (p ^ r)] (hn : r ≤ n) :
    (p : ZMod (p ^ r)) ^ n = 0 :=
  pow_eq_zero_of_le hn (nat_cast_p_pow_eq_zero p r)

lemma harmZ_even_mod_p {p r m : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero p]
    (hr : 0 < r) (hm : 0 < m) (hm' : m < p - 1) :
    ZMod.castHom (dvd_prime_self_pow hr) (ZMod p) (harmZ p r m (p - 1)) = 0 := by
  unfold harmZ
  rw [castHom_sum_inv_pow_Fp hr]
  exact harmFp_eq_zero hm hm'

/-- Refined Wolstenholme: `H ≡ -(p/2) H^{(2)} (mod p^4)`. -/
lemma harmZ_wolstenholme_p4 {p : ℕ} [Fact p.Prime] [NeZero (p ^ 4)] (hp : 7 ≤ p) :
    (2 : ZMod (p ^ 4)) * harmZ p 4 1 (p - 1) =
      -((p : ZMod (p ^ 4)) * harmZ p 4 2 (p - 1)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Nat.Prime.ne_zero Fact.out)⟩
  have hp4 : (p : ZMod (p ^ 4)) ^ 4 = 0 := nat_cast_p_pow_eq_zero p 4
  have hpair : ∀ k ∈ Icc 1 (p - 1),
      (k : ZMod (p ^ 4))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 4))⁻¹ =
        -((p : ZMod (p ^ 4)) * ((k : ZMod (p ^ 4))⁻¹) ^ 2
          + (p : ZMod (p ^ 4)) ^ 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 3
          + (p : ZMod (p ^ 4)) ^ 3 * ((k : ZMod (p ^ 4))⁻¹) ^ 4) := by
    intro k hk
    have h := inv_add_inv_p_sub (p := p) (r := 4) (by norm_num) hk
    have hI : Icc 1 (4 - 1) = {1, 2, 3} := by
      ext x; simp only [mem_Icc, mem_insert, mem_singleton]; omega
    rw [hI, sum_insert (by simp), sum_insert (by simp), sum_singleton] at h
    convert h using 1
    ring
  have hre1 := sum_reflect_Icc (p := p) (fun k => (k : ZMod (p ^ 4))⁻¹)
  have hsum :
      2 * ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 4))⁻¹ =
        ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 4))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 4))⁻¹) := by
    rw [sum_add_distrib, hre1]; ring
  have hsum' :
      2 * harmZ p 4 1 (p - 1) =
        ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 4))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 4))⁻¹) := by
    unfold harmZ
    convert hsum using 2
    refine sum_congr rfl fun k _ => pow_one _
  rw [hsum', sum_congr rfl hpair]
  have hsplit :
      ∑ k ∈ Icc 1 (p - 1),
          -((p : ZMod (p ^ 4)) * ((k : ZMod (p ^ 4))⁻¹) ^ 2
            + (p : ZMod (p ^ 4)) ^ 2 * ((k : ZMod (p ^ 4))⁻¹) ^ 3
            + (p : ZMod (p ^ 4)) ^ 3 * ((k : ZMod (p ^ 4))⁻¹) ^ 4) =
        -((p : ZMod (p ^ 4)) * harmZ p 4 2 (p - 1)
          + (p : ZMod (p ^ 4)) ^ 2 * harmZ p 4 3 (p - 1)
          + (p : ZMod (p ^ 4)) ^ 3 * harmZ p 4 4 (p - 1)) := by
    unfold harmZ
    rw [sum_neg_distrib]
    congr 1
    rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, mul_sum]
  rw [hsplit]
  -- p² H3 = 0 and p³ H4 = 0 in ZMod(p^4)
  have hH3p2 : (p : ZMod (p ^ 4)) ^ 2 * harmZ p 4 3 (p - 1) = 0 := by
    have hcast :
        ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 4)) (ZMod (p ^ 2))
          (harmZ p 4 3 (p - 1)) = harmZ p 2 3 (p - 1) :=
      castHom_harmZ (by norm_num : 2 ≤ 4) (by
        have : 1 ≤ p := (Fact.out : p.Prime).one_le; omega)
    have h0 : harmZ p 2 3 (p - 1) = 0 := (harmZ_odd_mod_p2 (p := p) hp).2
    have : ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 4)) (ZMod (p ^ 2))
        (harmZ p 4 3 (p - 1)) = 0 := by rw [hcast, h0]
    obtain ⟨y, hy⟩ :=
      eq_mul_pow_of_cast_eq_zero (pow_dvd_pow p (by norm_num : 2 ≤ 4)) this
    rw [hy, ← mul_assoc, ← Nat.cast_pow, ← Nat.cast_mul]
    have : (p ^ 2 : ℕ) * (p ^ 2 : ℕ) = p ^ 4 := by ring
    rw [this, CharP.cast_eq_zero, zero_mul]
  have hH4p3 : (p : ZMod (p ^ 4)) ^ 3 * harmZ p 4 4 (p - 1) = 0 := by
    have hcast :
        ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 4)) (ZMod p)
          (harmZ p 4 4 (p - 1)) = 0 :=
      harmZ_even_mod_p (by norm_num : 0 < 4) (by norm_num) (by omega)
    have := pow_mul_of_cast_mod_p (p := p) (r := 4) (by norm_num) hcast
    -- p^3 * H4 = 0, which is exactly this
    simpa using this
  rw [hH3p2, hH4p3, add_zero, add_zero]

lemma two_inv_mul_two {q : ℕ} [NeZero q] (h : IsUnit (2 : ZMod q)) :
    (2 : ZMod q)⁻¹ * 2 = 1 :=
  ZMod.inv_mul_of_unit _ h

/-- `H ≡ -(p/2) H2` in `ZMod (p^4)`. -/
lemma harmZ_eq_neg_p_div_two_H2 {p : ℕ} [Fact p.Prime] [NeZero (p ^ 4)] (hp : 7 ≤ p) :
    harmZ p 4 1 (p - 1) =
      -((p : ZMod (p ^ 4)) * (2 : ZMod (p ^ 4))⁻¹ * harmZ p 4 2 (p - 1)) := by
  have h2 : IsUnit (2 : ZMod (p ^ 4)) := isUnit_two_zmod (by omega)
  have h := harmZ_wolstenholme_p4 (p := p) hp
  have h' := congrArg (fun z : ZMod (p ^ 4) => (2 : ZMod (p ^ 4))⁻¹ * z) h
  dsimp at h'
  rw [← mul_assoc, two_inv_mul_two h2, one_mul] at h'
  rw [h']
  ring

lemma inv_p_sub_Fp {p k : ℕ} [Fact p.Prime] [NeZero p] (hk : k ∈ Icc 1 (p - 1)) :
    ((p - k : ℕ) : ZMod p)⁻¹ = -((k : ZMod p)⁻¹) := by
  have hk_le : k ≤ p := le_p_of_mem_Icc hk
  have hu : IsUnit (k : ZMod p) := isUnit_zmod_prime hk
  have : ((p - k : ℕ) : ZMod p) = - (k : ZMod p) := by
    rw [Nat.cast_sub hk_le, CharP.cast_eq_zero, zero_sub]
  rw [this, inv_neg_of_unit hu]

lemma harmFp_sum {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1), (k : ZMod p)⁻¹ = 0 := by
  simpa [pow_one] using (harmFp_one_to_four (p := p) hp).1

lemma Icc_split_at {p k : ℕ} [Fact p.Prime] (hk : k ∈ Icc 1 (p - 1)) :
    Icc 1 (p - 1) = Icc 1 (k - 1) ∪ Icc k (p - 1) := by
  ext x; simp only [mem_Icc, mem_union]
  have := mem_Icc.mp hk
  omega

lemma disjoint_Icc_split {p k : ℕ} [Fact p.Prime] (hk : k ∈ Icc 1 (p - 1)) :
    Disjoint (Icc 1 (k - 1)) (Icc k (p - 1)) := by
  refine disjoint_left.mpr ?_
  intro a ha hb
  simp only [mem_Icc] at ha hb
  omega

lemma mem_Icc_p_sub_of_ge {p k j : ℕ} [Fact p.Prime]
    (hk : k ∈ Icc 1 (p - 1)) (hj : j ∈ Icc k (p - 1)) :
    p - j ∈ Icc 1 (p - k) := by
  simp only [mem_Icc] at hk hj ⊢
  omega

lemma mem_Icc_ge_of_p_sub {p k b : ℕ} [Fact p.Prime]
    (hk : k ∈ Icc 1 (p - 1)) (hb : b ∈ Icc 1 (p - k)) :
    p - b ∈ Icc k (p - 1) := by
  simp only [mem_Icc] at hk hb ⊢
  omega

lemma sum_Icc_ge_inv {p k : ℕ} [Fact p.Prime] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    ∑ j ∈ Icc k (p - 1), (j : ZMod p)⁻¹ =
      -∑ j ∈ Icc 1 (p - k), (j : ZMod p)⁻¹ := by
  have hle : ∀ j ∈ Icc k (p - 1), j ≤ p := by
    intro j hj; simp only [mem_Icc] at hj; omega
  have hbij :
      ∑ j ∈ Icc k (p - 1), (j : ZMod p)⁻¹ =
        ∑ i ∈ Icc 1 (p - k), ((p - i : ℕ) : ZMod p)⁻¹ := by
    refine sum_nbij (fun j => p - j) ?_ ?_ ?_ ?_
    · intro j hj; exact mem_Icc_p_sub_of_ge hk hj
    · intro a ha b hb heq
      exact (tsub_right_inj (hle a ha) (hle b hb)).mp heq
    · intro b hb
      have hbI : b ∈ Icc 1 (p - k) := by
        simpa using hb
      refine ⟨p - b, mem_Icc_ge_of_p_sub hk hbI, ?_⟩
      have hk' := mem_Icc.mp hk
      have hb' := mem_Icc.mp hbI
      exact Nat.sub_sub_self (by omega)
    · intro j hj
      have : p - (p - j) = j := Nat.sub_sub_self (hle j hj)
      simp [this]
  rw [hbij]
  have hcongr : ∑ i ∈ Icc 1 (p - k), ((p - i : ℕ) : ZMod p)⁻¹ =
      ∑ i ∈ Icc 1 (p - k), -((i : ZMod p)⁻¹) := by
    refine sum_congr rfl fun i hi => ?_
    have hiI : i ∈ Icc 1 (p - 1) := by
      have := mem_Icc.mp hi
      have := mem_Icc.mp hk
      simp only [mem_Icc]; omega
    exact inv_p_sub_Fp hiI
  rw [hcongr, sum_neg_distrib]

/-- `H_{p-k} = H_{k-1}` in `F_p`. -/
lemma harmFp_reflect_prefix {p k : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p)
    (hk : k ∈ Icc 1 (p - 1)) :
    ∑ j ∈ Icc 1 (p - k), (j : ZMod p)⁻¹ =
      ∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹ := by
  have hfull := harmFp_sum (p := p) hp
  have hsum0 : ∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹ +
      ∑ j ∈ Icc k (p - 1), (j : ZMod p)⁻¹ = 0 := by
    rw [← sum_union (disjoint_Icc_split hk), ← Icc_split_at hk, hfull]
  rw [sum_Icc_ge_inv hk] at hsum0
  -- H_{k-1} + (- H_{p-k}) = 0
  exact (add_neg_eq_zero.mp hsum0).symm

lemma inv_p_sub_Fp_pow {p k m : ℕ} [Fact p.Prime] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    (((p - k : ℕ) : ZMod p)⁻¹) ^ m = ((-1 : ZMod p) ^ m) * (((k : ZMod p)⁻¹) ^ m) := by
  rw [inv_p_sub_Fp hk, neg_pow]

lemma inv_p_sub_Fp_sq {p k : ℕ} [Fact p.Prime] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    (((p - k : ℕ) : ZMod p)⁻¹) ^ 2 = ((k : ZMod p)⁻¹) ^ 2 := by
  rw [inv_p_sub_Fp_pow hk, neg_one_sq, one_mul]

lemma inv_p_sub_Fp_cube {p k : ℕ} [Fact p.Prime] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    (((p - k : ℕ) : ZMod p)⁻¹) ^ 3 = -(((k : ZMod p)⁻¹) ^ 3) := by
  rw [inv_p_sub_Fp_pow hk, pow_succ, neg_one_sq, one_mul, neg_one_mul]

lemma harmFp2_sum {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = 0 :=
  (harmFp_one_to_four (p := p) hp).2.1

lemma harmFp4_sum {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4 = 0 :=
  (harmFp_one_to_four (p := p) hp).2.2.2

lemma sum_Icc_ge_inv_pow2 {p k : ℕ} [Fact p.Prime] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    ∑ j ∈ Icc k (p - 1), ((j : ZMod p)⁻¹) ^ 2 =
      ∑ j ∈ Icc 1 (p - k), ((j : ZMod p)⁻¹) ^ 2 := by
  have hle : ∀ j ∈ Icc k (p - 1), j ≤ p := by
    intro j hj; simp only [mem_Icc] at hj; omega
  have hbij :
      ∑ j ∈ Icc k (p - 1), ((j : ZMod p)⁻¹) ^ 2 =
        ∑ i ∈ Icc 1 (p - k), (((p - i : ℕ) : ZMod p)⁻¹) ^ 2 := by
    refine sum_nbij (fun j => p - j) ?_ ?_ ?_ ?_
    · intro j hj; exact mem_Icc_p_sub_of_ge hk hj
    · intro a ha b hb heq
      exact (tsub_right_inj (hle a ha) (hle b hb)).mp heq
    · intro b hb
      have hbI : b ∈ Icc 1 (p - k) := by simpa using hb
      refine ⟨p - b, mem_Icc_ge_of_p_sub hk hbI, ?_⟩
      have hk' := mem_Icc.mp hk
      have hb' := mem_Icc.mp hbI
      exact Nat.sub_sub_self (by omega)
    · intro j hj
      have : p - (p - j) = j := Nat.sub_sub_self (hle j hj)
      simp [this]
  rw [hbij]
  refine sum_congr rfl fun i hi => ?_
  have hiI : i ∈ Icc 1 (p - 1) := by
    have := mem_Icc.mp hi
    have := mem_Icc.mp hk
    simp only [mem_Icc]; omega
  exact inv_p_sub_Fp_sq hiI

/-- `H_{p-k}^{(2)} = - H_{k-1}^{(2)}` in `F_p`. -/
lemma harmFp2_reflect_prefix {p k : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p)
    (hk : k ∈ Icc 1 (p - 1)) :
    ∑ j ∈ Icc 1 (p - k), ((j : ZMod p)⁻¹) ^ 2 =
      -∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2 := by
  have hfull := harmFp2_sum (p := p) hp
  have hsum0 : ∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2 +
      ∑ j ∈ Icc k (p - 1), ((j : ZMod p)⁻¹) ^ 2 = 0 := by
    rw [← sum_union (disjoint_Icc_split hk), ← Icc_split_at hk, hfull]
  rw [sum_Icc_ge_inv_pow2 hk] at hsum0
  exact (add_eq_zero_iff_eq_neg'.mp hsum0)

lemma harmFp_prefix_last {p n : ℕ} [Fact p.Prime] [NeZero p]
    (hn : 1 ≤ n) (hn' : n ≤ p - 1) :
    ∑ j ∈ Icc 1 n, (j : ZMod p)⁻¹ =
      ∑ j ∈ Icc 1 (n - 1), (j : ZMod p)⁻¹ + (n : ZMod p)⁻¹ := by
  rw [Icc_succ_split n hn, sum_insert (by simp [mem_Icc]; omega)]
  ac_rfl

lemma harmFp2_prefix_last {p n : ℕ} [Fact p.Prime] [NeZero p]
    (hn : 1 ≤ n) (hn' : n ≤ p - 1) :
    ∑ j ∈ Icc 1 n, ((j : ZMod p)⁻¹) ^ 2 =
      ∑ j ∈ Icc 1 (n - 1), ((j : ZMod p)⁻¹) ^ 2 + ((n : ZMod p)⁻¹) ^ 2 := by
  rw [Icc_succ_split n hn, sum_insert (by simp [mem_Icc]; omega)]
  ac_rfl

/-- `H_{p-k-1} = H_k` in `F_p`. -/
lemma harmFp_reflect_pred {p k : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p)
    (hk : k ∈ Icc 1 (p - 1)) :
    ∑ j ∈ Icc 1 (p - k - 1), (j : ZMod p)⁻¹ =
      ∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹ := by
  have hpk : p - k ∈ Icc 1 (p - 1) := mem_Icc_p_sub hk
  have hpk1 : 1 ≤ p - k := (mem_Icc.mp hpk).1
  have hpk2 : p - k ≤ p - 1 := (mem_Icc.mp hpk).2
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
  have hrefl := harmFp_reflect_prefix (p := p) hp hk
  have hsplit := harmFp_prefix_last (p := p) hpk1 hpk2
  have hksplit := harmFp_prefix_last (p := p) hk1 hk2
  have hinv := inv_p_sub_Fp hk
  -- H_{p-k} = H_{p-k-1} + (p-k)^{-1} = H_{k-1}
  -- (p-k)^{-1} = -k^{-1}
  -- H_k = H_{k-1} + k^{-1}
  calc
    ∑ j ∈ Icc 1 (p - k - 1), (j : ZMod p)⁻¹
        = ∑ j ∈ Icc 1 (p - k), (j : ZMod p)⁻¹ - ((p - k : ℕ) : ZMod p)⁻¹ := by
          rw [hsplit]; ring
    _ = ∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹ - ((p - k : ℕ) : ZMod p)⁻¹ := by
          rw [hrefl]
    _ = ∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹ - (-((k : ZMod p)⁻¹)) := by
          rw [hinv]
    _ = ∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹ + (k : ZMod p)⁻¹ := by
          ring
    _ = ∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹ := by
          rw [hksplit]

/-- `H_{p-k-1}^{(2)} = -H_k^{(2)}` in `F_p`. -/
lemma harmFp2_reflect_pred {p k : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p)
    (hk : k ∈ Icc 1 (p - 1)) :
    ∑ j ∈ Icc 1 (p - k - 1), ((j : ZMod p)⁻¹) ^ 2 =
      -∑ j ∈ Icc 1 k, ((j : ZMod p)⁻¹) ^ 2 := by
  have hpk : p - k ∈ Icc 1 (p - 1) := mem_Icc_p_sub hk
  have hpk1 : 1 ≤ p - k := (mem_Icc.mp hpk).1
  have hpk2 : p - k ≤ p - 1 := (mem_Icc.mp hpk).2
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
  have hrefl := harmFp2_reflect_prefix (p := p) hp hk
  have hsplit := harmFp2_prefix_last (p := p) hpk1 hpk2
  have hksplit := harmFp2_prefix_last (p := p) hk1 hk2
  have hinv := inv_p_sub_Fp_sq hk
  calc
    ∑ j ∈ Icc 1 (p - k - 1), ((j : ZMod p)⁻¹) ^ 2
        = ∑ j ∈ Icc 1 (p - k), ((j : ZMod p)⁻¹) ^ 2 -
            (((p - k : ℕ) : ZMod p)⁻¹) ^ 2 := by
          rw [hsplit]; ring
    _ = -∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2 -
            (((p - k : ℕ) : ZMod p)⁻¹) ^ 2 := by
          rw [hrefl]
    _ = -∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2 -
            ((k : ZMod p)⁻¹) ^ 2 := by
          rw [hinv]
    _ = -∑ j ∈ Icc 1 k, ((j : ZMod p)⁻¹) ^ 2 := by
          rw [hksplit]; ring

lemma two_ne_zero_zmod {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  exact Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 2) (by omega) hdvd

/-- `∑ H_{k-1} / k³ = 0` in `F_p`. -/
lemma sum_harm_prefix_div_k3 {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
      (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) * ((k : ZMod p)⁻¹) ^ 3 = 0 := by
  let f : ℕ → ZMod p := fun k =>
    (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) * ((k : ZMod p)⁻¹) ^ 3
  have hpair : ∀ k ∈ Icc 1 (p - 1), f k + f (p - k) = -(((k : ZMod p)⁻¹) ^ 4) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
    have hpred := harmFp_reflect_pred (p := p) hp hk
    have hinv3 := inv_p_sub_Fp_cube hk
    have hksplit := harmFp_prefix_last (p := p) hk1 hk2
    unfold f
    have : (∑ j ∈ Icc 1 (p - k - 1), (j : ZMod p)⁻¹) *
        (((p - k : ℕ) : ZMod p)⁻¹) ^ 3 =
        (∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (-(((k : ZMod p)⁻¹) ^ 3)) := by
      rw [hpred, hinv3]
    rw [this]
    have hdiff :
        ∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹ - ∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹ =
          -((k : ZMod p)⁻¹) := by
      rw [hksplit]; ring
    calc
      (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) * ((k : ZMod p)⁻¹) ^ 3 +
          (∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (-(((k : ZMod p)⁻¹) ^ 3)) =
        (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹ -
          ∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * ((k : ZMod p)⁻¹) ^ 3 := by
        ring
      _ = (-((k : ZMod p)⁻¹)) * ((k : ZMod p)⁻¹) ^ 3 := by
        rw [hdiff]
      _ = -(((k : ZMod p)⁻¹) ^ 4) := by
        ring
  have hsum := two_mul_sum_reflect (p := p) f
  have hsum' : ∑ k ∈ Icc 1 (p - 1), (f k + f (p - k)) =
      -∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4 := by
    rw [sum_congr rfl hpair, sum_neg_distrib]
  rw [hsum, two_nsmul] at hsum'
  -- 2 * ∑ f = - H4 = 0
  have hH4 := harmFp4_sum (p := p) hp
  rw [hH4, neg_zero] at hsum'
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have : (2 : ZMod p) * ∑ k ∈ Icc 1 (p - 1), f k = 0 := by
    rw [two_mul]
    exact hsum'
  exact (mul_eq_zero.mp this).resolve_left h2

/-- `∑ H_{k-1}^{(2)} / k² = 0` in `F_p`. -/
lemma sum_harm2_prefix_div_k2 {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
      (∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  let f : ℕ → ZMod p := fun k =>
    (∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2
  have hpair : ∀ k ∈ Icc 1 (p - 1), f k + f (p - k) = -(((k : ZMod p)⁻¹) ^ 4) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
    have hpred := harmFp2_reflect_pred (p := p) hp hk
    have hinv2 := inv_p_sub_Fp_sq hk
    have hksplit := harmFp2_prefix_last (p := p) hk1 hk2
    unfold f
    have : (∑ j ∈ Icc 1 (p - k - 1), ((j : ZMod p)⁻¹) ^ 2) *
        (((p - k : ℕ) : ZMod p)⁻¹) ^ 2 =
        (-∑ j ∈ Icc 1 k, ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 := by
      rw [hpred, hinv2]
    rw [this]
    have hdiff :
        ∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2 -
          ∑ j ∈ Icc 1 k, ((j : ZMod p)⁻¹) ^ 2 =
          -(((k : ZMod p)⁻¹) ^ 2) := by
      rw [hksplit]; ring
    calc
      (∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 +
          (-∑ j ∈ Icc 1 k, ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 =
        (∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2 -
          ∑ j ∈ Icc 1 k, ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 := by
        ring
      _ = (-(((k : ZMod p)⁻¹) ^ 2)) * ((k : ZMod p)⁻¹) ^ 2 := by
        rw [hdiff]
      _ = -(((k : ZMod p)⁻¹) ^ 4) := by
        ring
  have hsum := two_mul_sum_reflect (p := p) f
  have hsum' : ∑ k ∈ Icc 1 (p - 1), (f k + f (p - k)) =
      -∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4 := by
    rw [sum_congr rfl hpair, sum_neg_distrib]
  rw [hsum, two_nsmul] at hsum'
  have hH4 := harmFp4_sum (p := p) hp
  rw [hH4, neg_zero] at hsum'
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have : (2 : ZMod p) * ∑ k ∈ Icc 1 (p - 1), f k = 0 := by
    rw [two_mul]
    exact hsum'
  exact (mul_eq_zero.mp this).resolve_left h2

/-- `∑ H_k / k³ = 0` in `F_p`. -/
def eSymmInv (p r m : ℕ) [NeZero (p ^ r)] : ZMod (p ^ r) :=
  ∑ t ∈ (Icc 1 (p - 1)).powersetCard m, ∏ i ∈ t, (i : ZMod (p ^ r))⁻¹

lemma eSymmInv_zero (p r : ℕ) [NeZero (p ^ r)] : eSymmInv p r 0 = 1 := by
  simp [eSymmInv, powersetCard_zero, prod_empty]

lemma eSymmInv_one (p r : ℕ) [NeZero (p ^ r)] :
    eSymmInv p r 1 = harmZ p r 1 (p - 1) := by
  simp only [eSymmInv, harmZ, powersetCard_one, sum_map, Function.Embedding.coeFn_mk,
    prod_singleton, pow_one]

lemma sum_powerset_by_card {α β : Type*} [AddCommMonoid β] [DecidableEq α]
    (s : Finset α) (f : Finset α → β) :
    ∑ t ∈ s.powerset, f t =
      ∑ n ∈ range (s.card + 1), ∑ t ∈ s.powersetCard n, f t := by
  rw [powerset_card_disjiUnion, sum_disjiUnion]

lemma two_p_pow_eq_zero {p r m : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hm : r ≤ m) : ((2 : ZMod (p ^ r)) * p) ^ m = 0 := by
  rw [mul_pow, nat_cast_p_pow_eq_zero_of_le hm, mul_zero]

lemma eSymmInv_eq_zero_of_card_lt {p r m : ℕ} [NeZero (p ^ r)]
    (hm : (Icc 1 (p - 1)).card < m) : eSymmInv p r m = 0 := by
  unfold eSymmInv
  have : (Icc 1 (p - 1)).powersetCard m = ∅ :=
    powersetCard_eq_empty.mpr hm
  simp [this]

lemma prod_const_mul_inv {p r : ℕ} [NeZero (p ^ r)] (t : Finset ℕ)
    (c : ZMod (p ^ r)) :
    ∏ i ∈ t, c * (i : ZMod (p ^ r))⁻¹ =
      c ^ t.card * ∏ i ∈ t, (i : ZMod (p ^ r))⁻¹ := by
  rw [prod_mul_distrib, prod_const]

lemma sum_powersetCard_const_mul {p r m : ℕ} [NeZero (p ^ r)] :
    ∑ t ∈ (Icc 1 (p - 1)).powersetCard m,
        ∏ i ∈ t, ((2 : ZMod (p ^ r)) * p) * (i : ZMod (p ^ r))⁻¹ =
      ((2 : ZMod (p ^ r)) * p) ^ m * eSymmInv p r m := by
  unfold eSymmInv
  have h1 : ∑ t ∈ (Icc 1 (p - 1)).powersetCard m,
      ∏ i ∈ t, ((2 : ZMod (p ^ r)) * p) * (i : ZMod (p ^ r))⁻¹ =
    ∑ t ∈ (Icc 1 (p - 1)).powersetCard m,
      ((2 : ZMod (p ^ r)) * p) ^ t.card * ∏ i ∈ t, (i : ZMod (p ^ r))⁻¹ :=
    sum_congr rfl fun t _ => prod_const_mul_inv t _
  rw [h1]
  have h2 : ∑ t ∈ (Icc 1 (p - 1)).powersetCard m,
      ((2 : ZMod (p ^ r)) * p) ^ t.card * ∏ i ∈ t, (i : ZMod (p ^ r))⁻¹ =
    ∑ t ∈ (Icc 1 (p - 1)).powersetCard m,
      ((2 : ZMod (p ^ r)) * p) ^ m * ∏ i ∈ t, (i : ZMod (p ^ r))⁻¹ :=
    sum_congr rfl fun t ht => by
      have hc : t.card = m := (mem_powersetCard.mp ht).2
      rw [hc]
  rw [h2, ← mul_sum]

lemma betaZ_eq_sum_esymm (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)] :
    betaZ p r =
      ∑ m ∈ range (r + 1),
        ((2 : ZMod (p ^ r)) * p) ^ m * eSymmInv p r m := by
  unfold betaZ
  rw [prod_one_add]
  rw [sum_powerset_by_card]
  rw [sum_congr rfl fun m _ => sum_powersetCard_const_mul]
  -- compare `range (card+1)` with `range (r+1)`
  let N := (Icc 1 (p - 1)).card + 1
  change ∑ m ∈ range N, ((2 : ZMod (p ^ r)) * p) ^ m * eSymmInv p r m = _
  rcases le_total N (r + 1) with hle | hge
  · -- N ≤ r+1: extra large-m terms have empty powersetCard
    have hsub : range N ⊆ range (r + 1) := by
      intro x hx; simp only [mem_range] at hx ⊢; omega
    rw [sum_subset hsub]
    intro m hm hmN
    have : (Icc 1 (p - 1)).card < m := by
      simp only [mem_range, N] at hm hmN; omega
    rw [eSymmInv_eq_zero_of_card_lt this, mul_zero]
  · -- r+1 ≤ N: extra large-m terms have (2p)^m = 0
    have hsub : range (r + 1) ⊆ range N := by
      intro x hx; simp only [mem_range] at hx ⊢; omega
    rw [← sum_subset hsub]
    intro m hm hm'
    have : r ≤ m := by
      simp only [mem_range] at hm hm'; omega
    rw [two_p_pow_eq_zero this, zero_mul]

lemma powersetCard_two_insert {α : Type*} [DecidableEq α] {x : α} {s : Finset α}
    (hx : x ∉ s) :
    powersetCard 2 (insert x s) =
      powersetCard 2 s ∪ (s.image fun y => ({x, y} : Finset α)) := by
  rw [show 2 = Nat.succ 1 from rfl, powersetCard_succ_insert hx]
  congr 1
  ext t
  simp only [mem_image, mem_powersetCard]
  constructor
  · rintro ⟨u, ⟨hu_sub, hu_card⟩, rfl⟩
    have : u.card = 1 := hu_card
    obtain ⟨y, hy, rfl⟩ := card_eq_one.mp this
    refine ⟨y, mem_of_subset hu_sub (mem_singleton_self y), ?_⟩
    simp [pair_comm]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨{y}, ⟨singleton_subset_iff.mpr hy, card_singleton y⟩, ?_⟩
    simp

lemma sum_sq_eq_sum_sq_add_two_esymm {α : Type*} [DecidableEq α]
    {R : Type*} [CommRing R] (s : Finset α) (a : α → R) :
    (∑ i ∈ s, a i) ^ 2 =
      ∑ i ∈ s, a i ^ 2 + 2 * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, a i := by
  induction s using Finset.induction with
  | empty =>
    have : powersetCard 2 (∅ : Finset α) = ∅ :=
      powersetCard_eq_empty.mpr (by simp)
    simp [this]
  | insert x s hx ih =>
    rw [sum_insert hx, sum_insert hx, add_sq]
    have hpc := powersetCard_two_insert (x := x) (s := s) hx
    have hdisj : Disjoint (powersetCard 2 s)
        (s.image fun y => ({x, y} : Finset α)) := by
      refine disjoint_left.mpr ?_
      intro t ht2 htimg
      obtain ⟨y, hy, rfl⟩ := mem_image.mp htimg
      have hx_in : x ∈ ({x, y} : Finset α) := mem_insert_self _ _
      have : x ∈ s := (mem_powersetCard.mp ht2).1 hx_in
      exact hx this
    rw [hpc, sum_union hdisj, mul_add]
    have himg : ∑ t ∈ s.image (fun y => ({x, y} : Finset α)), ∏ i ∈ t, a i =
        ∑ y ∈ s, a x * a y := by
      rw [sum_image]
      · refine sum_congr rfl fun y hy => ?_
        have hxy : x ≠ y := fun h => hx (h ▸ hy)
        rw [prod_insert (by simp [hxy]), prod_singleton]
      · intro y hy z hz heq
        change ({x, y} : Finset α) = {x, z} at heq
        have yin : y ∈ ({x, y} : Finset α) := by simp
        rw [heq] at yin
        simp only [mem_insert, mem_singleton] at yin
        rcases yin with h | h
        · exact False.elim (hx (h ▸ (by simpa using hy)))
        · exact h
    rw [himg, ← mul_sum]
    rw [ih]
    ring

/-- `e₂ = (H² - H2)/2`. -/
lemma eSymmInv_two {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] :
    (2 : ZMod (p ^ r)) * eSymmInv p r 2 =
      harmZ p r 1 (p - 1) ^ 2 - harmZ p r 2 (p - 1) := by
  have h := sum_sq_eq_sum_sq_add_two_esymm (Icc 1 (p - 1))
    (fun k : ℕ => (k : ZMod (p ^ r))⁻¹)
  simp only [harmZ, eSymmInv, pow_one]
  rw [h]
  ring

lemma sum_off_diag_sq {α : Type*} [DecidableEq α] {R : Type*} [CommRing R]
    (s : Finset α) (a : α → R) :
    ∑ i ∈ s, ∑ j ∈ s.erase i, a i ^ 2 * a j =
      (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, a j) - ∑ i ∈ s, a i ^ 3 := by
  have hfull : ∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * a j =
      (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, a j) := by
    have : ∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * a j =
        ∑ i ∈ s, a i ^ 2 * ∑ j ∈ s, a j :=
      sum_congr rfl fun i _ => (mul_sum _ _ _).symm
    rw [this, ← sum_mul]
  have hdiag : ∑ i ∈ s, a i ^ 2 * a i = ∑ i ∈ s, a i ^ 3 :=
    sum_congr rfl fun i _ => by ring
  have hsplit : ∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * a j =
      ∑ i ∈ s, a i ^ 2 * a i + ∑ i ∈ s, ∑ j ∈ s.erase i, a i ^ 2 * a j := by
    refine Eq.trans (sum_congr rfl fun i hi => ?_) sum_add_distrib
    rw [← sum_erase_add (s := s) (a := i) (h := hi)]
    ring
  rw [hfull] at hsplit
  rw [hsplit, hdiag]
  ring

lemma powersetCard_three_insert {α : Type*} [DecidableEq α] {x : α} {s : Finset α}
    (hx : x ∉ s) :
    powersetCard 3 (insert x s) =
      powersetCard 3 s ∪ (powersetCard 2 s).image (insert x) := by
  rw [show 3 = Nat.succ 2 from rfl, powersetCard_succ_insert hx]

lemma sum_cube_eq_sum_cube_add {α : Type*} [DecidableEq α]
    {R : Type*} [CommRing R] (s : Finset α) (a : α → R) :
    (∑ i ∈ s, a i) ^ 3 =
      ∑ i ∈ s, a i ^ 3
        + 3 * ∑ i ∈ s, ∑ j ∈ s.erase i, a i ^ 2 * a j
        + 6 * ∑ t ∈ s.powersetCard 3, ∏ i ∈ t, a i := by
  induction s using Finset.induction with
  | empty =>
    have h3 : powersetCard 3 (∅ : Finset α) = ∅ :=
      powersetCard_eq_empty.mpr (by simp)
    simp [h3]
  | insert x s hx ih =>
    have hcube :
        (a x + ∑ i ∈ s, a i) ^ 3 =
          a x ^ 3 + 3 * a x ^ 2 * ∑ i ∈ s, a i
            + 3 * a x * (∑ i ∈ s, a i) ^ 2 + (∑ i ∈ s, a i) ^ 3 := by
      ring
    have hpc := powersetCard_three_insert (x := x) (s := s) hx
    have hdisj : Disjoint (powersetCard 3 s)
        ((powersetCard 2 s).image (insert x)) := by
      refine disjoint_left.mpr ?_
      intro t ht3 htimg
      obtain ⟨u, hu, rfl⟩ := mem_image.mp htimg
      have hx_in : x ∈ insert x u := mem_insert_self _ _
      have : x ∈ s := (mem_powersetCard.mp ht3).1 hx_in
      exact hx this
    have hprod : ∑ t ∈ (powersetCard 2 s).image (insert x), ∏ i ∈ t, a i =
        a x * ∑ t ∈ powersetCard 2 s, ∏ i ∈ t, a i := by
      rw [sum_image]
      · refine Eq.trans (sum_congr rfl fun t ht => ?_) (mul_sum _ _ _).symm
        have hx_not : x ∉ t := fun hxt =>
          hx ((mem_powersetCard.mp ht).1 hxt)
        rw [prod_insert hx_not]
      · intro t ht u hu heq
        have ht' : t = (insert x t).erase x := by
          rw [erase_insert]
          intro hxt; exact hx ((mem_powersetCard.mp ht).1 hxt)
        have hu' : u = (insert x u).erase x := by
          rw [erase_insert]
          intro hxu; exact hx ((mem_powersetCard.mp hu).1 hxu)
        calc
          t = (insert x t).erase x := ht'
          _ = (insert x u).erase x := by rw [heq]
          _ = u := hu'.symm
    have hoff_insert :
        ∑ i ∈ insert x s, ∑ j ∈ (insert x s).erase i, a i ^ 2 * a j =
          ∑ j ∈ s, a x ^ 2 * a j
            + ∑ i ∈ s, a i ^ 2 * a x
            + ∑ i ∈ s, ∑ j ∈ s.erase i, a i ^ 2 * a j := by
      rw [sum_insert hx, erase_insert hx]
      have herase_i : ∀ i ∈ s, (insert x s).erase i = insert x (s.erase i) := by
        intro i hi
        refine erase_insert_of_ne ?_
        intro h
        exact hx (h ▸ hi)
      have hrest :
          ∑ i ∈ s, ∑ j ∈ (insert x s).erase i, a i ^ 2 * a j =
            ∑ i ∈ s, a i ^ 2 * a x
              + ∑ i ∈ s, ∑ j ∈ s.erase i, a i ^ 2 * a j := by
        refine Eq.trans (sum_congr rfl fun i hi => ?_) sum_add_distrib
        have hx' : x ∉ s.erase i := fun h => hx (mem_of_mem_erase h)
        rw [herase_i i hi, sum_insert hx']
      rw [hrest]
      ac_rfl
    have hpull1 : ∑ j ∈ s, a x ^ 2 * a j = a x ^ 2 * ∑ j ∈ s, a j :=
      (mul_sum s (fun j => a j) (a x ^ 2)).symm
    have hpull2 : ∑ i ∈ s, a i ^ 2 * a x = (∑ i ∈ s, a i ^ 2) * a x :=
      (sum_mul s (fun i => a i ^ 2) (a x)).symm
    have he2 := sum_sq_eq_sum_sq_add_two_esymm s a
    rw [sum_insert hx, hcube, ih]
    rw [sum_insert (f := fun i => a i ^ 3) hx]
    rw [hoff_insert, hpull1, hpull2, hpc, sum_union hdisj, hprod, he2]
    ring

lemma eSymmInv_three_mul_six {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] :
    (6 : ZMod (p ^ r)) * eSymmInv p r 3 =
      harmZ p r 1 (p - 1) ^ 3
        - 3 * harmZ p r 1 (p - 1) * harmZ p r 2 (p - 1)
        + 2 * harmZ p r 3 (p - 1) := by
  have h := sum_cube_eq_sum_cube_add (Icc 1 (p - 1))
    (fun k : ℕ => (k : ZMod (p ^ r))⁻¹)
  have hoff := sum_off_diag_sq (Icc 1 (p - 1))
    (fun k : ℕ => (k : ZMod (p ^ r))⁻¹)
  rw [hoff] at h
  simp only [harmZ, eSymmInv, pow_one]
  rw [h]
  ring

/-- `H` is divisible by `p²` in `ZMod (p^r)` for `r ≥ 2`. -/
lemma harmZ_one_dvd_p2 {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero (p ^ 2)]
    [NeZero p] (hr : 2 ≤ r) (hp : 7 ≤ p) :
    ∃ y : ZMod (p ^ r),
      harmZ p r 1 (p - 1) = (p : ZMod (p ^ r)) ^ 2 * y := by
  have hcast :
      ZMod.castHom (pow_dvd_pow p hr) (ZMod (p ^ 2)) (harmZ p r 1 (p - 1)) =
        harmZ p 2 1 (p - 1) :=
    castHom_harmZ hr (by
      have : 1 ≤ p := (Fact.out : p.Prime).one_le; omega)
  have h0 : harmZ p 2 1 (p - 1) = 0 := (harmZ_odd_mod_p2 (p := p) hp).1
  have : ZMod.castHom (pow_dvd_pow p hr) (ZMod (p ^ 2)) (harmZ p r 1 (p - 1)) = 0 := by
    rw [hcast, h0]
  obtain ⟨y, hy⟩ := eq_mul_pow_of_cast_eq_zero (pow_dvd_pow p hr) this
  refine ⟨y, ?_⟩
  rw [← Nat.cast_pow]
  exact hy

/-- `H3` is divisible by `p²` in `ZMod (p^r)` for `r ≥ 2`. -/
lemma harmZ_three_dvd_p2 {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero (p ^ 2)]
    [NeZero p] (hr : 2 ≤ r) (hp : 7 ≤ p) :
    ∃ y : ZMod (p ^ r),
      harmZ p r 3 (p - 1) = (p : ZMod (p ^ r)) ^ 2 * y := by
  have hcast :
      ZMod.castHom (pow_dvd_pow p hr) (ZMod (p ^ 2)) (harmZ p r 3 (p - 1)) =
        harmZ p 2 3 (p - 1) :=
    castHom_harmZ hr (by
      have : 1 ≤ p := (Fact.out : p.Prime).one_le; omega)
  have h0 : harmZ p 2 3 (p - 1) = 0 := (harmZ_odd_mod_p2 (p := p) hp).2
  have : ZMod.castHom (pow_dvd_pow p hr) (ZMod (p ^ 2)) (harmZ p r 3 (p - 1)) = 0 := by
    rw [hcast, h0]
  obtain ⟨y, hy⟩ := eq_mul_pow_of_cast_eq_zero (pow_dvd_pow p hr) this
  refine ⟨y, ?_⟩
  rw [← Nat.cast_pow]
  exact hy

/-- `H2` is divisible by `p` in `ZMod (p^r)`. -/
lemma harmZ_two_dvd_p {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero p]
    (hr : 1 ≤ r) (hp : 7 ≤ p) :
    ∃ y : ZMod (p ^ r),
      harmZ p r 2 (p - 1) = (p : ZMod (p ^ r)) * y := by
  have hcast :
      ZMod.castHom (dvd_prime_self_pow (by omega : 0 < r)) (ZMod p)
        (harmZ p r 2 (p - 1)) = 0 :=
    harmZ_even_mod_p (by omega) (by norm_num) (by omega)
  exact eq_mul_pow_of_cast_eq_zero (dvd_prime_self_pow (by omega : 0 < r)) hcast

lemma p_pow_mul_harm_sq_eq_zero {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero (p ^ 2)]
    [NeZero p] (hp : 7 ≤ p) :
    (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 1 (p - 1) ^ 2 = 0 := by
  obtain ⟨y, hy⟩ := harmZ_one_dvd_p2 (p := p) (r := 5) (by norm_num) hp
  rw [hy, mul_pow]
  have : (p : ZMod (p ^ 5)) ^ 2 * ((p : ZMod (p ^ 5)) ^ 2) ^ 2 * y ^ 2 = 0 := by
    have hp6 : (p : ZMod (p ^ 5)) ^ 6 = 0 :=
      nat_cast_p_pow_eq_zero_of_le (by norm_num : 5 ≤ 6)
    ring_nf
    simp [hp6]
  convert this using 1
  ring

lemma isUnit_six_zmod {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] (hp : 7 ≤ p) :
    IsUnit (6 : ZMod (p ^ r)) := by
  have h2 : IsUnit (2 : ZMod (p ^ r)) := isUnit_two_zmod (by omega)
  have h3 : IsUnit (3 : ZMod (p ^ r)) := isUnit_three_zmod (by omega)
  have h6 : (6 : ZMod (p ^ r)) = 2 * 3 := by norm_num
  rw [h6]
  exact h2.mul h3

lemma eSymmInv_three_mul_p3_eq_zero {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    [NeZero (p ^ 2)] [NeZero p] (hp : 7 ≤ p) :
    (p : ZMod (p ^ 5)) ^ 3 * eSymmInv p 5 3 = 0 := by
  have h6 := eSymmInv_three_mul_six (p := p) (r := 5)
  have hunit : IsUnit (6 : ZMod (p ^ 5)) := isUnit_six_zmod hp
  obtain ⟨y, hy⟩ := harmZ_one_dvd_p2 (p := p) (r := 5) (by norm_num) hp
  obtain ⟨z, hz⟩ := harmZ_two_dvd_p (p := p) (r := 5) (by norm_num) hp
  obtain ⟨w, hw⟩ := harmZ_three_dvd_p2 (p := p) (r := 5) (by norm_num) hp
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := nat_cast_p_pow_eq_zero p 5
  have hp6 : (p : ZMod (p ^ 5)) ^ 6 = 0 :=
    nat_cast_p_pow_eq_zero_of_le (by norm_num : 5 ≤ 6)
  have hRHS :
      (p : ZMod (p ^ 5)) ^ 3 *
        (harmZ p 5 1 (p - 1) ^ 3
          - 3 * harmZ p 5 1 (p - 1) * harmZ p 5 2 (p - 1)
          + 2 * harmZ p 5 3 (p - 1)) = 0 := by
    rw [hy, hz, hw]
    have hp9 : (p : ZMod (p ^ 5)) ^ 9 = 0 := by
      have : (p : ZMod (p ^ 5)) ^ 9 = (p : ZMod (p ^ 5)) ^ 5 * (p : ZMod (p ^ 5)) ^ 4 := by ring
      rw [this, hp5, zero_mul]
    ring_nf
    simp [hp5, hp6, hp9]
  have hmul :
      (6 : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 3 * eSymmInv p 5 3) = 0 := by
    have : (p : ZMod (p ^ 5)) ^ 3 * ((6 : ZMod (p ^ 5)) * eSymmInv p 5 3) = 0 := by
      rw [h6, hRHS]
    convert this using 1
    ring
  exact hunit.mul_right_inj.mp (hmul.trans (mul_zero _).symm)

lemma castHom_eSymmInv_prime {p r m : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero p]
    (hr : 0 < r) :
    ZMod.castHom (dvd_prime_self_pow hr) (ZMod p) (eSymmInv p r m) =
      ∑ t ∈ (Icc 1 (p - 1)).powersetCard m, ∏ i ∈ t, (i : ZMod p)⁻¹ := by
  unfold eSymmInv
  rw [map_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [map_prod]
  refine prod_congr rfl fun k hk => ?_
  have hkI : k ∈ Icc 1 (p - 1) := (mem_powersetCard.mp ht).1 hk
  exact castHom_inv (dvd_prime_self_pow hr) (isUnit_of_mem_Icc hkI)

lemma Icc_cast_injOn (p : ℕ) [Fact p.Prime] :
    Set.InjOn (fun k : ℕ => (k : ZMod p)) (Icc 1 (p - 1)) := by
  intro a ha b hb h
  have ha' := mem_Icc_lt_prime (p := p) ha
  have hb' := mem_Icc_lt_prime (p := p) hb
  have hab : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp h
  have ha_mod : a % p = a := Nat.mod_eq_of_lt ha'.2
  have hb_mod : b % p = b := Nat.mod_eq_of_lt hb'.2
  rwa [Nat.ModEq, ha_mod, hb_mod] at hab

open Polynomial

lemma eSymmInv_four_eq_zero_mod_p {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ t ∈ (Icc 1 (p - 1)).powersetCard 4, ∏ i ∈ t, (i : ZMod p)⁻¹ = 0 := by
  classical
  let nz : Finset (ZMod p) := (univ : Finset (ZMod p)).filter (fun x => x ≠ 0)
  have hIcc : (Icc 1 (p - 1)).image (fun k : ℕ => (k : ZMod p)) = nz :=
    Icc_image_eq_nonzero p
  have hinj := Icc_cast_injOn p
  have hinj_inv : Set.InjOn (fun k : ℕ => (k : ZMod p)⁻¹) (Icc 1 (p - 1)) := by
    intro a ha b hb h
    have ha0 : (a : ZMod p) ≠ 0 := by
      have := mem_Icc_lt_prime (p := p) ha
      exact (CharP.cast_eq_zero_iff (ZMod p) p a).not.mpr
        (Nat.not_dvd_of_pos_of_lt this.1 this.2)
    have hb0 : (b : ZMod p) ≠ 0 := by
      have := mem_Icc_lt_prime (p := p) hb
      exact (CharP.cast_eq_zero_iff (ZMod p) p b).not.mpr
        (Nat.not_dvd_of_pos_of_lt this.1 this.2)
    have := congrArg (fun z : ZMod p => z⁻¹) h
    simp only [inv_inv] at this
    exact hinj ha hb this
  have hIcc_inv : (Icc 1 (p - 1)).image (fun k : ℕ => (k : ZMod p)⁻¹) = nz := by
    ext x
    simp only [mem_image, nz, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk0 : (k : ZMod p) ≠ 0 := by
        have := mem_Icc_lt_prime (p := p) hk
        exact (CharP.cast_eq_zero_iff (ZMod p) p k).not.mpr
          (Nat.not_dvd_of_pos_of_lt this.1 this.2)
      exact inv_ne_zero hk0
    · intro hx
      -- x ≠ 0, so x⁻¹ ≠ 0, hence x⁻¹ is in the image of Icc under natCast
      have : x⁻¹ ∈ nz := by
        simp [nz, inv_ne_zero hx]
      rw [← hIcc] at this
      obtain ⟨k, hk, hkcast⟩ := mem_image.mp this
      refine ⟨k, hk, ?_⟩
      rw [hkcast, inv_inv]
  -- both mapped multisets equal nz.val
  have hmap_id :
      ((Icc 1 (p - 1)).val.map (fun k : ℕ => (k : ZMod p))) = nz.val := by
    rw [← image_val_of_injOn hinj, hIcc]
  have hmap_inv :
      ((Icc 1 (p - 1)).val.map (fun k : ℕ => (k : ZMod p)⁻¹)) = nz.val := by
    rw [← image_val_of_injOn hinj_inv, hIcc_inv]
  have hsum_inv :
      ∑ t ∈ (Icc 1 (p - 1)).powersetCard 4, ∏ i ∈ t, (i : ZMod p)⁻¹ =
        nz.val.esymm 4 := by
    have := Finset.esymm_map_val (fun k : ℕ => (k : ZMod p)⁻¹) (Icc 1 (p - 1)) 4
    rw [← this, hmap_inv]
  have hsum_id :
      ∑ t ∈ (Icc 1 (p - 1)).powersetCard 4, ∏ i ∈ t, (i : ZMod p) =
        nz.val.esymm 4 := by
    have := Finset.esymm_map_val (fun k : ℕ => (k : ZMod p)) (Icc 1 (p - 1)) 4
    rw [← this, hmap_id]
  rw [hsum_inv]
  -- e4(F_p^*) = e4(F_p) via adjoining 0
  have huniv : (univ : Finset (ZMod p)) = insert 0 nz := by
    ext x
    by_cases hx : x = 0
    · subst hx
      simp [nz]
    · simp [nz, hx]
  have h0nz : (0 : ZMod p) ∉ nz := by simp [nz]
  have hpc := powersetCard_succ_insert (s := nz) (x := (0 : ZMod p)) (n := 3) h0nz
  have h4 : (4 : ℕ) = Nat.succ 3 := rfl
  have hesymm_univ :
      (univ : Finset (ZMod p)).val.esymm 4 =
        nz.val.esymm 4 := by
    have h1 : (univ : Finset (ZMod p)).val.esymm 4 =
        ∑ t ∈ (univ : Finset (ZMod p)).powersetCard 4, ∏ x ∈ t, x := by
      simpa [Multiset.map_id'] using
        Finset.esymm_map_val (fun x : ZMod p => x) univ 4
    have h2 : nz.val.esymm 4 = ∑ t ∈ nz.powersetCard 4, ∏ x ∈ t, x := by
      simpa [Multiset.map_id'] using
        Finset.esymm_map_val (fun x : ZMod p => x) nz 4
    rw [h1]
    have hsplit : powersetCard 4 (univ : Finset (ZMod p)) =
        powersetCard 4 nz ∪ (powersetCard 3 nz).image (insert (0 : ZMod p)) := by
      rw [huniv, h4, hpc]
    have hdisj : Disjoint (powersetCard 4 nz)
        ((powersetCard 3 nz).image (insert (0 : ZMod p))) := by
      refine disjoint_left.mpr ?_
      intro t ht4 htimg
      obtain ⟨u, hu, rfl⟩ := mem_image.mp htimg
      have : (0 : ZMod p) ∈ insert 0 u := mem_insert_self _ _
      have : (0 : ZMod p) ∈ nz := (mem_powersetCard.mp ht4).1 this
      exact h0nz this
    have hprod0 : ∑ t ∈ (powersetCard 3 nz).image (insert (0 : ZMod p)),
        ∏ i ∈ t, i = 0 := by
      refine sum_eq_zero fun t ht => ?_
      obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
      exact prod_eq_zero (mem_insert_self _ _) rfl
    rw [hsplit, sum_union hdisj, hprod0, add_zero, ← h2]
  -- Vieta on X^p - X
  let P : (ZMod p)[X] := X ^ p - X
  have hdeg : P.natDegree = p := by
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    simpa [P] using (FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp1)
  have hroots : P.roots = (univ : Finset (ZMod p)).val := by
    simpa [P] using (FiniteField.roots_X_pow_card_sub_X (K := ZMod p))
  have hcard : Multiset.card P.roots = P.natDegree := by
    rw [hroots, hdeg]
    simp [ZMod.card]
  have hle : p - 4 ≤ P.natDegree := by rw [hdeg]; omega
  have hcoeff := Polynomial.coeff_eq_esymm_roots_of_card (R := ZMod p) hcard hle
  have hleft : P.coeff (p - 4) = 0 := by
    have hne1 : p - 4 ≠ 1 := by omega
    have hnep : p - 4 ≠ p := by omega
    unfold P
    rw [coeff_sub, coeff_X_pow, coeff_X, if_neg hnep]
    simp [show (1 : ℕ) ≠ p - 4 by omega]
  have hlead : P.leadingCoeff = 1 := by
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hlt : (X : (ZMod p)[X]).degree < (X ^ p : (ZMod p)[X]).degree := by
      rw [degree_X_pow, degree_X]
      exact_mod_cast hp1
    simpa [P] using (leadingCoeff_sub_of_degree_lt hlt).trans (leadingCoeff_X_pow p)
  have hidx : P.natDegree - (p - 4) = 4 := by rw [hdeg]; omega
  have hroot0 : P.roots.esymm 4 = 0 := by
    rw [hidx] at hcoeff
    rw [hleft, hlead, one_mul] at hcoeff
    have hsign : (-1 : ZMod p) ^ 4 = 1 := by norm_num
    rw [hsign, one_mul] at hcoeff
    exact hcoeff.symm
  rw [← hesymm_univ, ← hroots, hroot0]

lemma eSymmInv_four_mul_p4_eq_zero {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    [NeZero p] (hp : 7 ≤ p) :
    (p : ZMod (p ^ 5)) ^ 4 * eSymmInv p 5 4 = 0 := by
  have hcast :
      ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
        (eSymmInv p 5 4) = 0 := by
    rw [castHom_eSymmInv_prime (by norm_num : 0 < 5)]
    exact eSymmInv_four_eq_zero_mod_p hp
  have := pow_mul_of_cast_mod_p (p := p) (r := 5) (by norm_num) hcast
  simpa using this

lemma isUnit_two_p5 {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] (hp : 7 ≤ p) :
    IsUnit (2 : ZMod (p ^ 5)) :=
  isUnit_two_zmod (by omega)

lemma betaZ_eq_one_add_two_p_H_sub {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    [NeZero (p ^ 2)] [NeZero p] (hp : 7 ≤ p) :
    betaZ p 5 =
      1 + (2 : ZMod (p ^ 5)) * p * harmZ p 5 1 (p - 1)
        - (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 2 (p - 1) := by
  rw [betaZ_eq_sum_esymm]
  have hsum :
      ∑ m ∈ range 6, ((2 : ZMod (p ^ 5)) * p) ^ m * eSymmInv p 5 m =
        eSymmInv p 5 0
          + ((2 : ZMod (p ^ 5)) * p) * eSymmInv p 5 1
          + ((2 : ZMod (p ^ 5)) * p) ^ 2 * eSymmInv p 5 2
          + ((2 : ZMod (p ^ 5)) * p) ^ 3 * eSymmInv p 5 3
          + ((2 : ZMod (p ^ 5)) * p) ^ 4 * eSymmInv p 5 4
          + ((2 : ZMod (p ^ 5)) * p) ^ 5 * eSymmInv p 5 5 := by
    simp [sum_range_succ]
  rw [hsum, eSymmInv_zero, eSymmInv_one]
  have hp5pow : ((2 : ZMod (p ^ 5)) * p) ^ 5 = 0 :=
    two_p_pow_eq_zero (by norm_num : 5 ≤ 5)
  rw [hp5pow, zero_mul, add_zero]
  have h3 : ((2 : ZMod (p ^ 5)) * p) ^ 3 * eSymmInv p 5 3 = 0 := by
    have : ((2 : ZMod (p ^ 5)) * p) ^ 3 =
        (8 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 := by ring
    rw [this, mul_assoc, eSymmInv_three_mul_p3_eq_zero hp, mul_zero]
  have h4 : ((2 : ZMod (p ^ 5)) * p) ^ 4 * eSymmInv p 5 4 = 0 := by
    have : ((2 : ZMod (p ^ 5)) * p) ^ 4 =
        (16 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 4 := by ring
    rw [this, mul_assoc, eSymmInv_four_mul_p4_eq_zero hp, mul_zero]
  rw [h3, h4, add_zero, add_zero]
  have he2 := eSymmInv_two (p := p) (r := 5)
  have h2 :
      ((2 : ZMod (p ^ 5)) * p) ^ 2 * eSymmInv p 5 2 =
        (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 *
          (harmZ p 5 1 (p - 1) ^ 2 - harmZ p 5 2 (p - 1)) := by
    have hpow : ((2 : ZMod (p ^ 5)) * p) ^ 2 =
        (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * 2 := by ring
    rw [hpow, mul_assoc, he2]
  rw [h2]
  have hHsq : (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 1 (p - 1) ^ 2 = 0 :=
    p_pow_mul_harm_sq_eq_zero hp
  have :
      (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 *
        (harmZ p 5 1 (p - 1) ^ 2 - harmZ p 5 2 (p - 1)) =
      -((2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 2 (p - 1)) := by
    rw [mul_sub]
    have hzero : (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 *
        harmZ p 5 1 (p - 1) ^ 2 = 0 := by
      calc
        (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 1 (p - 1) ^ 2
            = (2 : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 1 (p - 1) ^ 2) := by
          ring
        _ = (2 : ZMod (p ^ 5)) * 0 := by rw [hHsq]
        _ = 0 := mul_zero _
    rw [hzero, zero_sub]
  rw [this]
  ring

/-- `β - 1 ≡ -3 p² H2` in `ZMod (p^5)`. -/
lemma betaZ_sub_one {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero (p ^ 4)]
    [NeZero (p ^ 2)] [NeZero p] (hp : 7 ≤ p) :
    betaZ p 5 - 1 =
      -((3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 2 (p - 1)) := by
  rw [betaZ_eq_one_add_two_p_H_sub hp]
  have hW := harmZ_wolstenholme_p4 (p := p) hp
  have hcastH :
      ZMod.castHom (pow_dvd_pow p (by norm_num : 4 ≤ 5)) (ZMod (p ^ 4))
        (harmZ p 5 1 (p - 1)) = harmZ p 4 1 (p - 1) :=
    castHom_harmZ (by norm_num : 4 ≤ 5) (by
      have : 1 ≤ p := (Fact.out : p.Prime).one_le; omega)
  have hcastH2 :
      ZMod.castHom (pow_dvd_pow p (by norm_num : 4 ≤ 5)) (ZMod (p ^ 4))
        (harmZ p 5 2 (p - 1)) = harmZ p 4 2 (p - 1) :=
    castHom_harmZ (by norm_num : 4 ≤ 5) (by
      have : 1 ≤ p := (Fact.out : p.Prime).one_le; omega)
  have hcast :
      ZMod.castHom (pow_dvd_pow p (by norm_num : 4 ≤ 5)) (ZMod (p ^ 4))
        ((2 : ZMod (p ^ 5)) * harmZ p 5 1 (p - 1)
          + (p : ZMod (p ^ 5)) * harmZ p 5 2 (p - 1)) = 0 := by
    simp only [map_add, map_mul, map_ofNat, map_natCast, hcastH, hcastH2]
    linear_combination hW
  obtain ⟨γ, hγ⟩ :=
    eq_mul_pow_of_cast_eq_zero (pow_dvd_pow p (by norm_num : 4 ≤ 5)) hcast
  have hlift :
      (2 : ZMod (p ^ 5)) * p * harmZ p 5 1 (p - 1)
        + (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 2 (p - 1) = 0 := by
    have hmul' :
        (p : ZMod (p ^ 5)) *
            ((2 : ZMod (p ^ 5)) * harmZ p 5 1 (p - 1)
              + (p : ZMod (p ^ 5)) * harmZ p 5 2 (p - 1)) =
          (p : ZMod (p ^ 5)) * ((p ^ 4 : ℕ) : ZMod (p ^ 5)) * γ := by
      rw [hγ]; ring
    have hrhs : (p : ZMod (p ^ 5)) * ((p ^ 4 : ℕ) : ZMod (p ^ 5)) * γ = 0 := by
      rw [← Nat.cast_mul]
      have : (p : ℕ) * p ^ 4 = p ^ 5 := by ring
      rw [this, CharP.cast_eq_zero, zero_mul]
    have hrew :
        (p : ZMod (p ^ 5)) *
            ((2 : ZMod (p ^ 5)) * harmZ p 5 1 (p - 1)
              + (p : ZMod (p ^ 5)) * harmZ p 5 2 (p - 1)) =
          (2 : ZMod (p ^ 5)) * p * harmZ p 5 1 (p - 1)
            + (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 2 (p - 1) := by
      ring
    rw [hrew] at hmul'
    rw [hmul', hrhs]
  have :
      1 + (2 : ZMod (p ^ 5)) * p * harmZ p 5 1 (p - 1)
        - (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 2 (p - 1) - 1 =
      -((3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * harmZ p 5 2 (p - 1)) := by
    linear_combination hlift
  exact this

lemma den_one_add_two_p_div {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (((1 : ℚ) + 2 * (p : ℚ) / k).den : ZMod (p ^ r)) := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
    exact_mod_cast this
  have hform : (1 : ℚ) + 2 * (p : ℚ) / k = ((k + 2 * p : ℤ) : ℚ) / (k : ℤ) := by
    field_simp [hk0]
    push_cast
    ring
  have hdvd : ((1 : ℚ) + 2 * (p : ℚ) / k).den ∣ k := by
    rw [hform, ← Rat.divInt_eq_div]
    have h := Rat.den_dvd (k + 2 * p : ℤ) (k : ℤ)
    exact_mod_cast h
  exact isUnit_natCast_of_dvd hdvd (isUnit_of_mem_Icc (p := p) (r := r) hk)

lemma ratZMod_one_add_two_p_div {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ratZMod (p ^ r) (1 + 2 * (p : ℚ) / k) =
      1 + (2 : ZMod (p ^ r)) * p * (k : ZMod (p ^ r))⁻¹ := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
    exact_mod_cast this
  have hk0n : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
  have hunit_k : IsUnit (k : ZMod (p ^ r)) := isUnit_of_mem_Icc hk
  have hform : (1 : ℚ) + 2 * (p : ℚ) / k = ((k + 2 * p : ℕ) : ℚ) / k := by
    have : (k : ℚ) + 2 * p = (k + 2 * p : ℕ) := by push_cast; ring
    field_simp [hk0]
    exact this
  rw [hform]
  have hcast : ((k + 2 * p : ℕ) : ℚ) = ((k + 2 * p : ℤ) : ℚ) := by simp
  rw [hcast]
  have hdiv := ratZMod_eq_div (q := p ^ r) (n := (k + 2 * p : ℤ)) (d := k) hk0n hunit_k
  rw [hdiv]
  push_cast
  have : (k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit_k
  calc
    ((k : ZMod (p ^ r)) + 2 * p) * (k : ZMod (p ^ r))⁻¹
        = (k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹
          + (2 : ZMod (p ^ r)) * p * (k : ZMod (p ^ r))⁻¹ := by ring
    _ = 1 + (2 : ZMod (p ^ r)) * p * (k : ZMod (p ^ r))⁻¹ := by rw [this]

lemma ratZMod_betaRat {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] (hn : 1 ≤ p) :
    ratZMod (p ^ r) (betaRat p) = betaZ p r := by
  have hf : ∀ k ∈ Icc 1 (p - 1),
      IsUnit (((1 : ℚ) + 2 * (p : ℚ) / k).den : ZMod (p ^ r)) :=
    fun k hk => den_one_add_two_p_div hk
  rw [betaRat_eq_prod p hn, betaZ, ratZMod_prod _ _ hf]
  refine prod_congr rfl fun k hk => ratZMod_one_add_two_p_div hk

lemma S1_cast_eq_three_betaZ {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hp : 7 ≤ p) :
    (S1 p : ZMod (p ^ r)) = (3 : ZMod (p ^ r)) * betaZ p r := by
  have hn : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hS1 : (S1 p : ℚ) = (3 * p).choose p := by
    exact_mod_cast S1_eq_choose p hn
  have hbeta : ((3 * p).choose p : ℚ) = 3 * betaRat p := by
    unfold betaRat
    field_simp
  have h3 : IsUnit ((3 : ℚ).den : ZMod (p ^ r)) := by simp
  have hbden : IsUnit ((betaRat p).den : ZMod (p ^ r)) := by
    have hf : ∀ k ∈ Icc 1 (p - 1),
        IsUnit (((1 : ℚ) + 2 * (p : ℚ) / k).den : ZMod (p ^ r)) :=
      fun k hk => den_one_add_two_p_div hk
    rw [betaRat_eq_prod p hn]
    exact den_isUnit_prod _ _ hf
  have : (S1 p : ZMod (p ^ r)) = ratZMod (p ^ r) (S1 p : ℚ) := by
    rw [ratZMod_nat]
  have h3q : ratZMod (p ^ r) (3 : ℚ) = 3 := by
    have : (3 : ℚ) = ((3 : ℤ) : ℚ) := by norm_cast
    rw [this, ratZMod_int]
    norm_cast
  rw [this, hS1, hbeta, ratZMod_mul h3 hbden, h3q, ratZMod_betaRat hn]

/-- Square of `β-1` vanishes in `ZMod (p^5)`. -/
lemma betaZ_sub_one_sq {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero (p ^ 4)]
    [NeZero (p ^ 2)] [NeZero p] (hp : 7 ≤ p) :
    (betaZ p 5 - 1) ^ 2 = 0 := by
  rw [betaZ_sub_one hp]
  obtain ⟨z, hz⟩ := harmZ_two_dvd_p (p := p) (r := 5) (by norm_num) hp
  rw [hz]
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := nat_cast_p_pow_eq_zero p 5
  have hp6 : (p : ZMod (p ^ 5)) ^ 6 = 0 :=
    nat_cast_p_pow_eq_zero_of_le (by norm_num : 5 ≤ 6)
  ring_nf
  simp [hp5, hp6]

lemma pow_one_add_of_sq_eq_zero {q : ℕ} [NeZero q] {x : ZMod q} (hx : x ^ 2 = 0)
    (n : ℕ) : (1 + x) ^ n = 1 + n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have hx2 : x ^ 2 = 0 := hx
    calc
      (1 + (n : ZMod q) * x) * (1 + x)
          = 1 + (n : ZMod q) * x + x + (n : ZMod q) * x * x := by ring
      _ = 1 + (n : ZMod q) * x + x + (n : ZMod q) * x ^ 2 := by
          ring
      _ = 1 + (n : ZMod q) * x + x := by rw [hx2, mul_zero, add_zero]
      _ = 1 + ((n : ZMod q) + 1) * x := by ring
      _ = 1 + ((n + 1 : ℕ) : ZMod q) * x := by
          simp [Nat.cast_succ]

lemma den_div_of_int_div_nat {a : ℤ} {d : ℕ} (hd : d ≠ 0) :
    ((a : ℚ) / d).den ∣ d := by
  have h := Rat.den_dvd a (d : ℤ)
  have heq : (a : ℚ) / (d : ℕ) = Rat.divInt a (d : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
  rw [heq]
  exact_mod_cast h

lemma den_inv_sq_unit {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (((1 : ℚ) / (k : ℚ) ^ 2).den : ZMod (p ^ r)) := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
    exact_mod_cast this
  have : (1 : ℚ) / (k : ℚ) ^ 2 = (1 : ℤ) / (k ^ 2 : ℕ) := by
    push_cast; field_simp [hk0]
  rw [this]
  have hdvd := den_div_of_int_div_nat (a := 1) (d := k ^ 2) (pow_ne_zero 2 (mem_Icc_lt_prime (p := p) hk).1.ne')
  have hunit : IsUnit ((k ^ 2 : ℕ) : ZMod (p ^ r)) := by
    rw [Nat.cast_pow]
    exact (isUnit_of_mem_Icc (p := p) (r := r) hk).pow 2
  exact isUnit_natCast_of_dvd hdvd hunit

lemma den_frac_pm_unit {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit ((((1 : ℚ) - (p : ℚ) / k) / (1 + (p : ℚ) / k)).den : ZMod (p ^ r)) := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
    exact_mod_cast this
  have hkp0 : k + p ≠ 0 := by
    have : 0 < k + p := by
      have := (mem_Icc_lt_prime (p := p) hk).1
      omega
    exact this.ne'
  have hform : ((1 : ℚ) - (p : ℚ) / k) / (1 + (p : ℚ) / k) =
      (((k : ℤ) - (p : ℤ)) : ℚ) / (k + p : ℕ) := by
    have hkpn : ((k : ℚ) + (p : ℚ)) = ((k + p : ℕ) : ℚ) := by push_cast; rfl
    field_simp [hk0]
    rw [hkpn]
    push_cast
    ring
  rw [hform]
  have hdvd : ((((k : ℤ) - (p : ℤ)) : ℚ) / (k + p : ℕ)).den ∣ k + p := by
    convert den_div_of_int_div_nat (a := (k : ℤ) - (p : ℤ)) (d := k + p) hkp0 using 4
    simp
  have hunit : IsUnit ((k + p : ℕ) : ZMod (p ^ r)) := by
    have hklt := mem_Icc_lt_prime (p := p) hk
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right r ?_
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro hdvd'
      have : p ∣ k := (Nat.dvd_add_iff_left (dvd_refl p)).mpr hdvd'
      exact Nat.not_dvd_of_pos_of_lt hklt.1 hklt.2 this)).symm
  exact isUnit_natCast_of_dvd hdvd hunit

lemma den_quad_unit {p r i : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hi : i ∈ Icc 1 (p - 1)) :
    IsUnit (((1 : ℚ) - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2).den : ZMod (p ^ r)) := by
  have hi0 : (i : ℚ) ≠ 0 := by
    have : i ≠ 0 := (mem_Icc_lt_prime (p := p) hi).1.ne'
    exact_mod_cast this
  have hform : (1 : ℚ) - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2 =
      ((i : ℤ) ^ 2 - 3 * p * i + 2 * p ^ 2 : ℤ) / (i ^ 2 : ℕ) := by
    field_simp [hi0]
    push_cast
    ring
  rw [hform]
  have hdvd := den_div_of_int_div_nat
    (a := (i : ℤ) ^ 2 - 3 * p * i + 2 * p ^ 2) (d := i ^ 2)
    (pow_ne_zero 2 (mem_Icc_lt_prime (p := p) hi).1.ne')
  have hunit : IsUnit ((i ^ 2 : ℕ) : ZMod (p ^ r)) := by
    rw [Nat.cast_pow]
    exact (isUnit_of_mem_Icc (p := p) (r := r) hi).pow 2
  exact isUnit_natCast_of_dvd hdvd hunit

lemma den_Wrat_term_unit {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (((1 : ℚ) / (k : ℚ) ^ 2 *
        ((1 - (p : ℚ) / k) / (1 + (p : ℚ) / k)) *
        ∏ i ∈ Icc 1 (k - 1),
          (1 - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2)).den : ZMod (p ^ r)) := by
  have h1 := den_inv_sq_unit (p := p) (r := r) hk
  have h2 := den_frac_pm_unit (p := p) (r := r) hk
  have h3 : IsUnit (((∏ i ∈ Icc 1 (k - 1),
        (1 - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2)).den : ZMod (p ^ r))) := by
    refine den_isUnit_prod _ _ ?_
    intro i hi
    have hik : i ∈ Icc 1 (p - 1) := by
      have hi' := mem_Icc.mp hi
      have hk' := mem_Icc.mp hk
      exact mem_Icc.mpr ⟨hi'.1, by omega⟩
    exact den_quad_unit hik
  exact den_isUnit_of_mul (den_isUnit_of_mul h1 h2) h3

lemma den_Wrat_unit {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] :
    IsUnit ((Wrat p).den : ZMod (p ^ r)) := by
  unfold Wrat
  refine den_isUnit_sum _ _ ?_
  intro k hk
  exact den_Wrat_term_unit hk

lemma S2_cast_eq_S1_mul {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hp : 7 ≤ p) :
    (S2 p : ZMod (p ^ r)) =
      (S1 p : ZMod (p ^ r)) *
        (1 - (2 : ZMod (p ^ r)) * (p : ZMod (p ^ r)) ^ 2 * ratZMod (p ^ r) (Wrat p)) := by
  have hn : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hQ := S2_eq_S1_mul_W p hn
  have hS1u : IsUnit (((S1 p : ℚ).den : ZMod (p ^ r))) := by simp
  have hWu : IsUnit ((Wrat p).den : ZMod (p ^ r)) := den_Wrat_unit
  have h2u : IsUnit (((2 : ℚ).den : ZMod (p ^ r))) := by simp
  have hpu : IsUnit ((((p : ℚ) ^ 2).den : ZMod (p ^ r))) := by
    have : (p : ℚ) ^ 2 = ((p ^ 2 : ℕ) : ℚ) := by push_cast; rfl
    rw [this]
    simp
  have h1u : IsUnit (((1 : ℚ).den : ZMod (p ^ r))) := by simp
  have hrhs_u : IsUnit (((1 - 2 * (p : ℚ) ^ 2 * Wrat p).den : ZMod (p ^ r))) :=
    den_isUnit_of_sub h1u (den_isUnit_of_mul (den_isUnit_of_mul h2u hpu) hWu)
  have : (S2 p : ZMod (p ^ r)) = ratZMod (p ^ r) (S2 p : ℚ) := by
    rw [ratZMod_nat]
  rw [this, hQ, ratZMod_mul hS1u hrhs_u, ratZMod_nat, ratZMod_sub h1u
      (den_isUnit_of_mul (den_isUnit_of_mul h2u hpu) hWu), ratZMod_one,
      ratZMod_mul (den_isUnit_of_mul h2u hpu) hWu]
  have h2q : ratZMod (p ^ r) (2 : ℚ) = 2 := by
    have : (2 : ℚ) = ((2 : ℤ) : ℚ) := by norm_cast
    rw [this, ratZMod_int]; norm_cast
  have hpq : ratZMod (p ^ r) ((p : ℚ) ^ 2) = (p : ZMod (p ^ r)) ^ 2 := by
    have : (p : ℚ) ^ 2 = ((p ^ 2 : ℕ) : ℚ) := by push_cast; rfl
    rw [this, ratZMod_nat, Nat.cast_pow]
  rw [ratZMod_mul h2u hpu, h2q, hpq]

lemma sum_binom_neg_one (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ range (n + 1), ((-1 : ℚ) ^ k * n.choose k) = 0 := by
  have h := Int.alternating_sum_range_choose_of_ne hn
  have : ∑ k ∈ range (n + 1), ((-1 : ℚ) ^ k * n.choose k) =
      ∑ k ∈ range (n + 1), (((-1 : ℤ) ^ k * n.choose k : ℤ) : ℚ) := by
    refine sum_congr rfl fun k _ => ?_
    simp
  rw [this, ← Int.cast_sum, h]
  simp

lemma neg_one_pow_pred {k : ℕ} (hk : 1 ≤ k) :
    ((-1 : ℚ) ^ (k - 1)) = -((-1 : ℚ) ^ k) := by
  have : ((-1 : ℚ) ^ k) = ((-1 : ℚ) ^ ((k - 1) + 1)) := by
    congr 1; omega
  rw [this, pow_succ]
  ring

lemma sum_alternating_choose (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k) = 1 := by
  have htot := sum_binom_neg_one n hn
  have hr : range (n + 1) = insert 0 (Icc 1 n) := by
    ext x; simp [mem_range, mem_insert, mem_Icc]; omega
  rw [hr, sum_insert (by simp [mem_Icc])] at htot
  have hneg : ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ k * n.choose k) = -1 := by
    simp only [pow_zero, one_mul] at htot
    change (n.choose 0 : ℚ) + _ = 0 at htot
    simp only [choose_zero_right, Nat.cast_one] at htot
    linarith
  have hsgn : ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k) =
      -∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ k * n.choose k) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    rw [neg_one_pow_pred hk1]
    ring
  rw [hsgn, hneg, neg_neg]

lemma choose_mul_pred (n k : ℕ) (hk : 1 ≤ k) :
    k * (n + 1).choose k = (n + 1) * n.choose (k - 1) := by
  have hk0 : k = (k - 1) + 1 := by omega
  have h := Nat.add_one_mul_choose_eq n (k - 1)
  rw [← hk0] at h
  linarith

lemma choose_pred_div_eq (n k : ℕ) (hk : 1 ≤ k) :
    ((n.choose (k - 1) : ℚ) / k) = ((n + 1).choose k : ℚ) / (n + 1) := by
  have hmul := choose_mul_pred n k hk
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hn0 : (n + 1 : ℚ) ≠ 0 := by
    have : (n + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero n
    exact_mod_cast this
  have hmulQ : (k : ℚ) * (n + 1).choose k = (n + 1 : ℚ) * n.choose (k - 1) := by
    exact_mod_cast hmul
  calc
    (n.choose (k - 1) : ℚ) / k
        = ((n + 1 : ℚ) * n.choose (k - 1)) / ((n + 1 : ℚ) * k) := by
          field_simp [hk0, hn0]
    _ = ((k : ℚ) * (n + 1).choose k) / ((n + 1 : ℚ) * k) := by
          rw [hmulQ]
    _ = ((n + 1).choose k : ℚ) / (n + 1) := by
          field_simp [hk0, hn0]

lemma pascal_choose (n k : ℕ) (hk : 1 ≤ k) :
    (n + 1).choose k = n.choose (k - 1) + n.choose k := by
  have hk0 : (k - 1) + 1 = k := by omega
  simpa [hk0, add_comm] using Nat.choose_succ_succ n (k - 1)

lemma pascal_div (n k : ℕ) (hk : 1 ≤ k) :
    ((n + 1).choose k : ℚ) / k - (n.choose k : ℚ) / k =
      (n.choose (k - 1) : ℚ) / k := by
  have hch := pascal_choose n k hk
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hchQ : ((n + 1).choose k : ℚ) = (n.choose (k - 1) : ℚ) + n.choose k := by
    exact_mod_cast hch
  field_simp [hk0]
  linarith [hchQ]

lemma Icc_succ_eq (n : ℕ) : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
  ext x; simp [mem_Icc, mem_insert]; omega

/-- Generalized harmonic numbers of weight 2. -/
def harmonic₂ (n : ℕ) : ℚ := ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2

lemma harmonic₂_zero : harmonic₂ 0 = 0 := by
  simp [harmonic₂, Icc_eq_empty_of_lt]

lemma harmonic₂_succ (n : ℕ) :
    harmonic₂ (n + 1) = harmonic₂ n + (1 : ℚ) / ((n + 1 : ℕ) : ℚ) ^ 2 := by
  have hsplit := Icc_succ_eq n
  unfold harmonic₂
  rw [hsplit, sum_insert (by simp [mem_Icc])]
  ring

lemma harmonic_succ_div (n : ℕ) :
    harmonic (n + 1) = harmonic n + (1 : ℚ) / (n + 1) := by
  rw [harmonic_succ]
  have : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by simp
  rw [this, inv_eq_one_div]

/-- `∑_{k=1}^n (-1)^{k-1} C(n,k) / k = H_n`. -/
lemma sum_alternating_choose_div (n : ℕ) :
    ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / k) = harmonic n := by
  induction n with
  | zero =>
    simp [harmonic_zero, Icc_eq_empty_of_lt]
  | succ n ih =>
    have hsplit := Icc_succ_eq n
    have hmid :
        ∑ k ∈ Icc 1 n,
          ((-1 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ) / k -
            (-1 : ℚ) ^ (k - 1) * n.choose k / k) =
        ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose (k - 1) / k) := by
      refine sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have :
          ((-1 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ) / k -
            (-1 : ℚ) ^ (k - 1) * n.choose k / k) =
          (-1 : ℚ) ^ (k - 1) *
            (((n + 1).choose k : ℚ) / k - n.choose k / k) := by
        ring
      rw [this, pascal_div n k hk1]
      ring
    have hid :
        ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose (k - 1) / k) =
          ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (n + 1)) := by
      refine sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have h := choose_pred_div_eq n k hk1
      have :
          ((-1 : ℚ) ^ (k - 1) * n.choose (k - 1) / k) =
            ((-1 : ℚ) ^ (k - 1)) * (n.choose (k - 1) / k) := by
        ring
      rw [this, h]
      ring
    have hbin :
        ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k) = 1 :=
      sum_alternating_choose (n + 1) (Nat.succ_ne_zero n)
    have h1 :
        ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) =
          ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) +
            ((-1 : ℚ) ^ n / (n + 1)) := by
      rw [hsplit, sum_insert (by simp [mem_Icc])]
      simp [add_comm]
    have h2 :
        ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) -
            ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / k) =
          ∑ k ∈ Icc 1 n,
            ((-1 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ) / k -
              (-1 : ℚ) ^ (k - 1) * n.choose k / k) := by
      rw [← sum_sub_distrib]
    have hn0 : (n + 1 : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero n)
    have h3 :
        ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (n + 1)) +
            ((-1 : ℚ) ^ n / (n + 1)) =
          (1 : ℚ) / (n + 1) := by
      have hsum :
          ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k) =
            ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k) +
              ((-1 : ℚ) ^ n) := by
        rw [hsplit, sum_insert (by simp [mem_Icc])]
        simp [add_comm]
      have hpull :
          ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (n + 1)) =
            (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k)) *
              (n + 1 : ℚ)⁻¹ := by
        simp only [div_eq_mul_inv]
        rw [← sum_mul]
      rw [hpull]
      have hcomb :
          (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k)) *
              (n + 1 : ℚ)⁻¹ + ((-1 : ℚ) ^ n / (n + 1)) =
            (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k) +
              (-1 : ℚ) ^ n) / (n + 1) := by
        simp [div_eq_mul_inv]
        ring
      rw [hcomb, ← hsum, hbin]
    have hdiff :
        ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) -
          ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / k) =
          (1 : ℚ) / (n + 1) := by
      rw [h1]
      have :
          ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) +
              ((-1 : ℚ) ^ n / (n + 1)) -
            ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / k) =
          (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) -
            ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / k)) +
          ((-1 : ℚ) ^ n / (n + 1)) := by
        ring
      rw [this, h2, hmid, hid, h3]
    rw [harmonic_succ_div]
    linarith [hdiff, ih]

lemma sum_alternating_choose_div_sq_succ (n : ℕ) :
    ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2) =
      ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
        harmonic (n + 1) / (n + 1) := by
  have hsplit := Icc_succ_eq n
  have hn0 : (n + 1 : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hk_ne : ∀ k ∈ Icc 1 n, (k : ℚ) ≠ 0 := by
    intro k hk; exact_mod_cast (show k ≠ 0 by have := (mem_Icc.mp hk).1; omega)
  have hI1 := sum_alternating_choose_div (n + 1)
  -- split the (n+1) term
  have hL :
      ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2) =
        ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2) +
          ((-1 : ℚ) ^ n / (n + 1 : ℚ) ^ 2) := by
    rw [hsplit, sum_insert (by simp [mem_Icc])]
    simp [add_comm, pow_two]
  -- Pascal difference of summands
  have hdiff :
      ∑ k ∈ Icc 1 n,
          ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2 -
            (-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) =
        ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose (k - 1) / (k : ℚ) ^ 2) := by
    refine sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk0 := hk_ne k hk
    have hchQ : ((n + 1).choose k : ℚ) =
        (n.choose (k - 1) : ℚ) + n.choose k := by
      exact_mod_cast pascal_choose n k hk1
    field_simp [hk0, pow_two]
    linarith [hchQ]
  -- rewrite C(n, k-1)/k² via C(n+1,k)/((n+1)k)
  have hid :
      ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose (k - 1) / (k : ℚ) ^ 2) =
        ∑ k ∈ Icc 1 n,
          ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / ((n + 1 : ℚ) * k)) := by
    refine sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk0 := hk_ne k hk
    have h := choose_pred_div_eq n k hk1
    have hassoc :
        ((-1 : ℚ) ^ (k - 1) * n.choose (k - 1) / (k : ℚ) ^ 2) =
          ((-1 : ℚ) ^ (k - 1)) * ((n.choose (k - 1) : ℚ) / (k : ℚ) ^ 2) := by
      ring
    have hdiv : (n.choose (k - 1) : ℚ) / (k : ℚ) ^ 2 =
        ((n.choose (k - 1) : ℚ) / k) / k := by
      field_simp [hk0, pow_two]
    rw [hassoc, hdiv, h]
    field_simp [hk0, hn0, pow_two]
  have hpull :
      ∑ k ∈ Icc 1 n,
          ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / ((n + 1 : ℚ) * k)) =
        (1 / (n + 1 : ℚ)) *
          ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) := by
    have :
        ∑ k ∈ Icc 1 n,
            ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / ((n + 1 : ℚ) * k)) =
          ∑ k ∈ Icc 1 n,
            ((1 / (n + 1 : ℚ)) *
              ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k)) := by
      refine sum_congr rfl fun k hk => ?_
      have hk0 := hk_ne k hk
      field_simp [hn0, hk0]
    rw [this, ← mul_sum]
  have hI1split :
      ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) =
        ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) +
          ((-1 : ℚ) ^ n / (n + 1)) := by
    rw [hsplit, sum_insert (by simp [mem_Icc])]
    simp [add_comm]
  -- assemble
  have hsub :
      ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2) -
        ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) =
      ∑ k ∈ Icc 1 n,
          ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2 -
            (-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) := by
    rw [← sum_sub_distrib]
  calc
    ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2)
        = ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2) +
            ((-1 : ℚ) ^ n / (n + 1 : ℚ) ^ 2) := hL
    _ = (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
            (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2) -
              ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2))) +
          ((-1 : ℚ) ^ n / (n + 1 : ℚ) ^ 2) := by
        ring
    _ = ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
          (∑ k ∈ Icc 1 n,
              ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / (k : ℚ) ^ 2 -
                (-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
            ((-1 : ℚ) ^ n / (n + 1 : ℚ) ^ 2)) := by
        rw [hsub]; ring
    _ = ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
          (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose (k - 1) / (k : ℚ) ^ 2) +
            ((-1 : ℚ) ^ n / (n + 1 : ℚ) ^ 2)) := by
        rw [hdiff]
    _ = ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
          ((1 / (n + 1 : ℚ)) *
            ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) +
            ((-1 : ℚ) ^ n / (n + 1 : ℚ) ^ 2)) := by
        rw [hid, hpull]
    _ = ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
          ((1 / (n + 1 : ℚ)) *
            (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k) +
              ((-1 : ℚ) ^ n / (n + 1)))) := by
        have : ((-1 : ℚ) ^ n / (n + 1 : ℚ) ^ 2) =
            (1 / (n + 1 : ℚ)) * ((-1 : ℚ) ^ n / (n + 1)) := by
          field_simp [hn0]
        rw [this]
        ring
    _ = ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
          ((1 / (n + 1 : ℚ)) *
            ∑ k ∈ Icc 1 (n + 1), ((-1 : ℚ) ^ (k - 1) * (n + 1).choose k / k)) := by
        rw [hI1split]
    _ = ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) +
          harmonic (n + 1) / (n + 1) := by
        rw [hI1]
        ring

/-- `∑_{k=1}^n (-1)^{k-1} C(n,k) / k² = (H_n² + H_n^{(2)}) / 2`. -/
lemma sum_alternating_choose_div_sq (n : ℕ) :
    ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) =
      (harmonic n ^ 2 + harmonic₂ n) / 2 := by
  induction n with
  | zero =>
    simp [harmonic_zero, harmonic₂_zero, Icc_eq_empty_of_lt]
  | succ n ih =>
    rw [sum_alternating_choose_div_sq_succ, ih, harmonic_succ_div, harmonic₂_succ]
    have hn0 : (n + 1 : ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hcast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by simp
    rw [hcast]
    field_simp [hn0]
    ring

lemma harmonic_eq_sum (n : ℕ) :
    harmonic n = ∑ k ∈ Icc 1 n, (1 : ℚ) / k := by
  induction n with
  | zero => simp [harmonic_zero, Icc_eq_empty_of_lt]
  | succ n ih =>
    rw [harmonic_succ_div, ih, Icc_succ_eq, sum_insert (by simp [mem_Icc])]
    have : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by simp
    rw [this]
    ring

lemma den_inv_nat_unit {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (((1 : ℚ) / k).den : ZMod (p ^ r)) := by
  have hk0 : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
  have : (1 : ℚ) / k = ((1 : ℤ) : ℚ) / (k : ℕ) := by simp
  rw [this]
  have hdvd := den_div_of_int_div_nat (a := 1) (d := k) hk0
  exact isUnit_natCast_of_dvd hdvd (isUnit_of_mem_Icc (p := p) (r := r) hk)

lemma den_harmonic_prefix_unit {p r n : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hn : n ≤ p - 1) :
    IsUnit ((harmonic n).den : ZMod (p ^ r)) := by
  rw [harmonic_eq_sum]
  refine den_isUnit_sum _ _ ?_
  intro k hk
  have : k ∈ Icc 1 (p - 1) := by
    simp only [mem_Icc] at hk ⊢
    omega
  exact den_inv_nat_unit this

lemma ratZMod_harmonic {p r n : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hn : n ≤ p - 1) :
    ratZMod (p ^ r) (harmonic n) = harmZ p r 1 n := by
  rw [harmonic_eq_sum, harmZ]
  refine (ratZMod_sum (s := Icc 1 n) (f := fun k => (1 : ℚ) / k) ?_).trans ?_
  · intro k hk
    have : k ∈ Icc 1 (p - 1) := by
      simp only [mem_Icc] at hk ⊢; omega
    exact den_inv_nat_unit this
  · refine sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by
      have := (mem_Icc.mp hk).1; omega
    have hmem : k ∈ Icc 1 (p - 1) := by
      simp only [mem_Icc] at hk ⊢; omega
    have hunit := isUnit_of_mem_Icc (p := p) (r := r) hmem
    have : (1 : ℚ) / k = ((1 : ℤ) : ℚ) / (k : ℕ) := by simp
    rw [this, ratZMod_eq_div (n := 1) (d := k) hk0 hunit]
    simp [pow_one]

lemma den_harmonic₂_prefix_unit {p r n : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hn : n ≤ p - 1) :
    IsUnit ((harmonic₂ n).den : ZMod (p ^ r)) := by
  unfold harmonic₂
  refine den_isUnit_sum _ _ ?_
  intro k hk
  have hmem : k ∈ Icc 1 (p - 1) := by
    simp only [mem_Icc] at hk ⊢; omega
  exact den_inv_sq_unit hmem

lemma ratZMod_harmonic₂ {p r n : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hn : n ≤ p - 1) :
    ratZMod (p ^ r) (harmonic₂ n) = harmZ p r 2 n := by
  unfold harmonic₂ harmZ
  refine (ratZMod_sum (s := Icc 1 n) (f := fun k => (1 : ℚ) / (k : ℚ) ^ 2) ?_).trans ?_
  · intro k hk
    have hmem : k ∈ Icc 1 (p - 1) := by
      simp only [mem_Icc] at hk ⊢; omega
    exact den_inv_sq_unit hmem
  · refine sum_congr rfl fun k hk => ?_
    have hk0n : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    have hmem : k ∈ Icc 1 (p - 1) := by
      simp only [mem_Icc] at hk ⊢; omega
    have hunit := isUnit_of_mem_Icc (p := p) (r := r) hmem
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk0n
    have : (1 : ℚ) / (k : ℚ) ^ 2 = ((1 : ℤ) : ℚ) / (k ^ 2 : ℕ) := by
      push_cast; field_simp [hk0]
    rw [this]
    have hunit2 : IsUnit ((k ^ 2 : ℕ) : ZMod (p ^ r)) := by
      rw [Nat.cast_pow]; exact hunit.pow 2
    have hk20 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk0n
    rw [ratZMod_eq_div (n := 1) (d := k ^ 2) hk20 hunit2]
    have hpow : ((k ^ 2 : ℕ) : ZMod (p ^ r)) = (k : ZMod (p ^ r)) ^ 2 := by
      rw [Nat.cast_pow]
    rw [hpow]
    simp only [Int.cast_one, one_mul]
    refine ZMod.inv_eq_of_mul_eq_one (p ^ r) ((k : ZMod (p ^ r)) ^ 2)
        (((k : ZMod (p ^ r))⁻¹) ^ 2) ?_
    have hk1 : (k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hunit
    rw [pow_two, pow_two]
    calc
      (k : ZMod (p ^ r)) * k * ((k : ZMod (p ^ r))⁻¹ * (k : ZMod (p ^ r))⁻¹) =
          ((k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
            ((k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by ring
      _ = 1 * 1 := by rw [hk1]
      _ = 1 := by ring

lemma choose_p_div_eq {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k ≤ p) :
    ((p.choose k : ℚ) / k) = (p : ℚ) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2 := by
  have hmul : k * p.choose k = p * (p - 1).choose (k - 1) := by
    have hk0 : k = (k - 1) + 1 := by omega
    have hp0 : p = (p - 1) + 1 := by
      have : 1 ≤ p := hp.one_le
      omega
    have h := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
    rw [← hp0, ← hk0] at h
    linarith
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hmulQ : (k : ℚ) * p.choose k = (p : ℚ) * (p - 1).choose (k - 1) := by
    exact_mod_cast hmul
  field_simp [hk0, pow_two]
  linarith [hmulQ]

lemma choose_pred_eq_prod_shift {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) (hkp : k ≤ p) :
    ((p - 1).choose (k - 1) : ℚ) =
      (-1 : ℚ) ^ (k - 1) * ∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i) := by
  by_cases h1 : k = 1
  · subst h1; simp [Icc_eq_empty_of_lt]
  have hk1 : k - 1 ≤ p - 1 := by omega
  have hk1p : 1 ≤ k - 1 := by omega
  -- `choose_pred_eq_prod` gives C((p)-1, (k-1)) wait: C(n-1, t) with n=p, t=k-1
  simpa using choose_pred_eq_prod p (k - 1) hp hk1

lemma sum_alt_choose_pred_div_sq (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
        ((-1 : ℚ) ^ (k - 1) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2) =
      harmonic (p - 1) / p := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hI := sum_alternating_choose_div p
  -- split off the k = p term
  have hsplit : Icc 1 p = insert p (Icc 1 (p - 1)) := by
    ext x; simp [mem_Icc, mem_insert]; omega
  have hL :
      ∑ k ∈ Icc 1 p, ((-1 : ℚ) ^ (k - 1) * p.choose k / k) =
        ∑ k ∈ Icc 1 (p - 1), ((-1 : ℚ) ^ (k - 1) * p.choose k / k) +
          ((-1 : ℚ) ^ (p - 1) / p) := by
    have hp1 : 1 ≤ p := hp.one_le
    rw [hsplit, sum_insert (by simp [mem_Icc]; omega)]
    simp [add_comm]
  have hsign : ((-1 : ℚ) ^ (p - 1)) = 1 := by
    obtain ⟨m, hm⟩ := hodd
    have : p - 1 = 2 * m := by omega
    rw [this, pow_mul, neg_one_sq, one_pow]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  -- rewrite each inner term via C(p,k)/k = p C(p-1,k-1)/k²
  have hterms :
      ∑ k ∈ Icc 1 (p - 1), ((-1 : ℚ) ^ (k - 1) * p.choose k / k) =
        (p : ℚ) * ∑ k ∈ Icc 1 (p - 1),
          ((-1 : ℚ) ^ (k - 1) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2) := by
    have :
        ∑ k ∈ Icc 1 (p - 1), ((-1 : ℚ) ^ (k - 1) * p.choose k / k) =
          ∑ k ∈ Icc 1 (p - 1),
            ((-1 : ℚ) ^ (k - 1) *
              ((p : ℚ) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2)) := by
      refine sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have hk2 : k ≤ p := by have := (mem_Icc.mp hk).2; omega
      have h := choose_p_div_eq hp hk1 hk2
      have : (p.choose k : ℚ) / k =
          (p : ℚ) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2 := h
      -- associate
      have hassoc :
          ((-1 : ℚ) ^ (k - 1) * p.choose k / k) =
            ((-1 : ℚ) ^ (k - 1)) * (p.choose k / k) := by ring
      rw [hassoc, this]
    rw [this]
    have hfactor :
        ∑ k ∈ Icc 1 (p - 1),
            ((-1 : ℚ) ^ (k - 1) *
              ((p : ℚ) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2)) =
          (p : ℚ) * ∑ k ∈ Icc 1 (p - 1),
            ((-1 : ℚ) ^ (k - 1) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2) := by
      have :
          ∑ k ∈ Icc 1 (p - 1),
              ((-1 : ℚ) ^ (k - 1) *
                ((p : ℚ) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2)) =
            ∑ k ∈ Icc 1 (p - 1),
              ((p : ℚ) * ((-1 : ℚ) ^ (k - 1) *
                (p - 1).choose (k - 1) / (k : ℚ) ^ 2)) := by
        refine sum_congr rfl fun k _ => by ring
      rw [this, ← mul_sum]
    exact hfactor
  -- H_p = H_{p-1} + 1/p
  have hHp : harmonic p = harmonic (p - 1) + (1 : ℚ) / p := by
    have : p = (p - 1) + 1 := by omega
    rw [this, harmonic_succ_div]
    congr 2
    simp
  -- conclude
  have hI' : ∑ k ∈ Icc 1 p, ((-1 : ℚ) ^ (k - 1) * p.choose k / k) = harmonic p := hI
  rw [hL, hsign, hterms, hHp] at hI'
  have :
      (p : ℚ) * ∑ k ∈ Icc 1 (p - 1),
          ((-1 : ℚ) ^ (k - 1) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2) +
        (1 : ℚ) / p =
      harmonic (p - 1) + (1 : ℚ) / p := by
    simpa using hI'
  have heq := add_right_cancel this
  have := congrArg (fun t : ℚ => t / p) heq
  simp only at this
  have hcancel :
      ((p : ℚ) * ∑ k ∈ Icc 1 (p - 1),
          ((-1 : ℚ) ^ (k - 1) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2)) / p =
        ∑ k ∈ Icc 1 (p - 1),
          ((-1 : ℚ) ^ (k - 1) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2) := by
    field_simp [hpQ]
  rw [hcancel] at this
  exact this

lemma sum_prod_one_sub_p_div_k2 (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
        ((∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) / (k : ℚ) ^ 2) =
      harmonic (p - 1) / p := by
  have h := sum_alt_choose_pred_div_sq p hp hp3
  have :
      ∑ k ∈ Icc 1 (p - 1),
          ((-1 : ℚ) ^ (k - 1) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2) =
        ∑ k ∈ Icc 1 (p - 1),
          ((∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) / (k : ℚ) ^ 2) := by
    refine sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk2 : k ≤ p := by have := (mem_Icc.mp hk).2; omega
    have hp1 : 1 ≤ p := hp.one_le
    have hch := choose_pred_eq_prod_shift (p := p) (k := k) hp1 hk1 hk2
    have hassoc :
        ((-1 : ℚ) ^ (k - 1) * (p - 1).choose (k - 1) / (k : ℚ) ^ 2) =
          ((-1 : ℚ) ^ (k - 1)) * ((p - 1).choose (k - 1) : ℚ) / (k : ℚ) ^ 2 := by
      ring
    rw [hassoc, hch]
    have hsq : ((-1 : ℚ) ^ (k - 1)) * ((-1 : ℚ) ^ (k - 1)) = 1 := by
      rw [← pow_add]
      have : (k - 1) + (k - 1) = 2 * (k - 1) := by ring
      rw [this, pow_mul, neg_one_sq, one_pow]
    -- ((-1)^{k-1}) * ((-1)^{k-1} * prod) / k² = prod / k²
    ring_nf
    simp [hsq]
  rw [← this, h]

lemma neZero_p {p : ℕ} [Fact p.Prime] : NeZero p :=
  ⟨(Fact.out : p.Prime).ne_zero⟩

/-- `k⁻¹ = k^{p-2}` in `F_p`. -/
lemma choose_prime_pred {p i : ℕ} [Fact p.Prime] [NeZero p]
    (hi : i ≤ p - 1) :
    ((p - 1).choose i : ZMod p) = (-1 : ZMod p) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi' : i ≤ p - 1 := by omega
    have hne : (i + 1 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((i + 1 : ℕ) : ZMod p) = 0 := by
        simpa [Nat.cast_succ] using h
      have hdvd : p ∣ (i + 1) := (CharP.cast_eq_zero_iff (ZMod p) p (i + 1)).mp h'
      exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos i) (by omega) hdvd
    have hmulN := Nat.choose_succ_right_eq (p - 1) i
    have hcast :
        ((p - 1).choose (i + 1) : ZMod p) * (i + 1 : ZMod p) =
          ((p - 1).choose i : ZMod p) * (((p - 1) - i : ℕ) : ZMod p) := by
      have := congrArg (fun n : ℕ => (n : ZMod p)) hmulN
      push_cast at this
      exact this
    have hsub : (((p - 1) - i : ℕ) : ZMod p) = (-1 : ZMod p) - (i : ZMod p) := by
      have hle' : i ≤ p - 1 := hi'
      have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
      rw [Nat.cast_sub hle', Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one,
        CharP.cast_eq_zero]
      ring
    have ih' := ih hi'
    have : ((p - 1).choose (i + 1) : ZMod p) * (i + 1 : ZMod p) =
        ((-1 : ZMod p) ^ i) * (-(i + 1 : ZMod p)) := by
      rw [hcast, hsub, ih']
      ring
    apply (mul_left_inj' hne).mp
    rw [this, pow_succ]
    ring

lemma choose_den_unit (n k : ℕ) {q : ℕ} [NeZero q] :
    IsUnit (((n.choose k : ℚ).den : ZMod q)) := by simp

lemma ratZMod_choose {q n k : ℕ} [NeZero q] :
    ratZMod q (n.choose k : ℚ) = (n.choose k : ZMod q) :=
  ratZMod_nat _ _

section GeomChoose
variable {p : ℕ} [Fact p.Prime] [NeZero p]
lemma one_add_X_pow_char :
    ((1 + X : (ZMod p)[X]) ^ p) = 1 + X ^ p := by
  rw [add_pow_char, one_pow]

/-- `∑_{j=0}^{p-1} C(j,b) (1+X)^j`. -/
noncomputable def geomChoosePoly (b : ℕ) : (ZMod p)[X] :=
  ∑ j ∈ range p, C (j.choose b : ZMod p) * (1 + X) ^ j

lemma geomChoosePoly_zero :
    geomChoosePoly (p := p) 0 = X ^ (p - 1) := by
  have hsum : geomChoosePoly (p := p) 0 = ∑ j ∈ range p, (1 + X : (ZMod p)[X]) ^ j := by
    unfold geomChoosePoly
    refine sum_congr rfl fun j _ => ?_
    simp [choose_zero_right]
  have hgeom : (∑ j ∈ range p, (1 + X : (ZMod p)[X]) ^ j) * X = X ^ p := by
    have h := geom_sum_mul (1 + X : (ZMod p)[X]) p
    have hX : (1 + X : (ZMod p)[X]) - 1 = X := by ring
    have hpow : (1 + X : (ZMod p)[X]) ^ p - 1 = X ^ p := by
      rw [one_add_X_pow_char]; ring
    rwa [hX, hpow] at h
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hrhs : (X : (ZMod p)[X]) ^ p = X * X ^ (p - 1) := by
    have hpe : (X : (ZMod p)[X]) ^ p = X ^ ((p - 1) + 1) := by
      congr 1
      exact (Nat.sub_add_cancel hp1).symm
    rw [hpe, pow_succ]
    ring
  have hcancel : X * ((∑ j ∈ range p, (1 + X : (ZMod p)[X]) ^ j) - X ^ (p - 1)) = 0 := by
    calc
      X * ((∑ j ∈ range p, (1 + X : (ZMod p)[X]) ^ j) - X ^ (p - 1)) =
          (∑ j ∈ range p, (1 + X : (ZMod p)[X]) ^ j) * X - X * X ^ (p - 1) := by ring
      _ = X ^ p - X * X ^ (p - 1) := by rw [hgeom]
      _ = X * X ^ (p - 1) - X * X ^ (p - 1) := by rw [hrhs]
      _ = 0 := by ring
  have hXne : (X : (ZMod p)[X]) ≠ 0 := X_ne_zero
  have hdiff : (∑ j ∈ range p, (1 + X : (ZMod p)[X]) ^ j) - X ^ (p - 1) = 0 :=
    (mul_eq_zero.mp hcancel).resolve_left hXne
  rw [hsum, ← sub_eq_zero]
  exact hdiff

lemma choose_prime_mid {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    (p.choose k : ZMod p) = 0 := by
  have hdvd : p ∣ p.choose k :=
    (Fact.out : p.Prime).dvd_choose_self hk0.ne' hkp
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hdvd

lemma range_p_succ :
    range p = insert (p - 1) (range (p - 1)) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have h : range p = range ((p - 1) + 1) := by
    congr 1
    exact (Nat.sub_add_cancel hp1).symm
  rw [h, range_add_one]

lemma sum_range_p_succ (f : ℕ → (ZMod p)[X]) :
    ∑ i ∈ range p, f i = ∑ i ∈ range (p - 1), f i + f (p - 1) := by
  rw [range_p_succ, sum_insert (by simp [mem_range]), add_comm]

lemma geomChoosePoly_drop_zero {b : ℕ} (hb0 : 1 ≤ b) :
    geomChoosePoly (p := p) b =
      ∑ j ∈ range (p - 1), C ((j + 1).choose b : ZMod p) * (1 + X) ^ (j + 1) := by
  unfold geomChoosePoly
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hpe : range p = range ((p - 1) + 1) := by
    congr 1
    exact (Nat.sub_add_cancel hp1).symm
  have hz : (0 : ℕ).choose b = 0 := choose_eq_zero_of_lt hb0
  rw [hpe, sum_range_succ']
  simp [hz]

lemma choose_succ_add (j b : ℕ) (hb : 1 ≤ b) :
    (j + 1).choose b = j.choose (b - 1) + j.choose b := by
  have hb' : b = (b - 1) + 1 := (Nat.sub_add_cancel hb).symm
  rw [hb', choose_succ_succ, Nat.add_sub_cancel]

lemma geomChoosePoly_pascal_sum {b : ℕ} (hb0 : 1 ≤ b) :
    ∑ j ∈ range (p - 1), C ((j + 1).choose b : ZMod p) * (1 + X : (ZMod p)[X]) ^ (j + 1) =
      (1 + X) * ∑ j ∈ range (p - 1), C (j.choose (b - 1) : ZMod p) * (1 + X) ^ j +
        (1 + X) * ∑ j ∈ range (p - 1), C (j.choose b : ZMod p) * (1 + X) ^ j := by
  have hterm : ∀ j ∈ range (p - 1),
      C ((j + 1).choose b : ZMod p) * (1 + X : (ZMod p)[X]) ^ (j + 1) =
        (1 + X) * (C (j.choose (b - 1) : ZMod p) * (1 + X) ^ j) +
          (1 + X) * (C (j.choose b : ZMod p) * (1 + X) ^ j) := by
    intro j _hj
    have hch : ((j + 1).choose b : ZMod p) =
        (j.choose (b - 1) : ZMod p) + (j.choose b : ZMod p) := by
      have := congrArg (fun n : ℕ => (n : ZMod p)) (choose_succ_add j b hb0)
      push_cast at this
      exact this
    rw [hch, C_add, pow_succ, add_mul]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, mul_sum, mul_sum]

lemma sum_range_pred_eq_sub (c : ℕ) :
    ∑ j ∈ range (p - 1), C (j.choose c : ZMod p) * (1 + X : (ZMod p)[X]) ^ j =
      geomChoosePoly (p := p) c -
        C ((p - 1).choose c : ZMod p) * (1 + X) ^ (p - 1) := by
  unfold geomChoosePoly
  rw [sum_range_p_succ]
  ring

lemma geomChoosePoly_succ {b : ℕ} (hb0 : 1 ≤ b) (_hbp : b < p) :
    geomChoosePoly (p := p) b =
      (1 + X) * (geomChoosePoly (p := p) (b - 1) -
        C ((p - 1).choose (b - 1) : ZMod p) * (1 + X) ^ (p - 1)) +
      (1 + X) * (geomChoosePoly (p := p) b -
        C ((p - 1).choose b : ZMod p) * (1 + X) ^ (p - 1)) := by
  have hL := (geomChoosePoly_drop_zero (p := p) hb0).trans
    (geomChoosePoly_pascal_sum (p := p) hb0)
  nth_rw 1 [hL]
  rw [sum_range_pred_eq_sub (b - 1), sum_range_pred_eq_sub b]

lemma geomChoosePoly_mul_X {b : ℕ} (hb0 : 1 ≤ b) (hbp : b < p) :
    (X : (ZMod p)[X]) * geomChoosePoly (p := p) b +
      (1 + X) * geomChoosePoly (p := p) (b - 1) = 0 := by
  have h := geomChoosePoly_succ (p := p) hb0 hbp
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hch : ((p - 1).choose (b - 1) : ZMod p) + ((p - 1).choose b : ZMod p) =
      (p.choose b : ZMod p) := by
    have hpe : p = (p - 1) + 1 := (Nat.sub_add_cancel hp1).symm
    have hb' : b = (b - 1) + 1 := (Nat.sub_add_cancel hb0).symm
    have hc : p.choose b = (p - 1).choose (b - 1) + (p - 1).choose b := by
      rw [hpe, hb']
      simpa [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        choose_succ_succ (p - 1) (b - 1)
    have := congrArg (fun n : ℕ => (n : ZMod p)) hc
    push_cast at this
    exact this.symm
  have hC0 : (p.choose b : ZMod p) = 0 := choose_prime_mid (by omega) hbp
  set Sb := geomChoosePoly (p := p) b
  set Sb1 := geomChoosePoly (p := p) (b - 1)
  set q : (ZMod p)[X] := 1 + X
  set lastb : (ZMod p)[X] := C ((p - 1).choose b : ZMod p) * q ^ (p - 1)
  set lastb1 : (ZMod p)[X] := C ((p - 1).choose (b - 1) : ZMod p) * q ^ (p - 1)
  have h' : Sb = q * (Sb1 - lastb1) + q * (Sb - lastb) := by
    simpa [Sb, Sb1, q, lastb, lastb1] using h
  have hlast : q * lastb1 + q * lastb = 0 := by
    have : C ((p - 1).choose (b - 1) : ZMod p) + C ((p - 1).choose b : ZMod p) =
        C (0 : ZMod p) := by
      rw [← C_add, hch, hC0]
    calc
      q * lastb1 + q * lastb = q * (lastb1 + lastb) := by ring
      _ = q * (C ((p - 1).choose (b - 1) : ZMod p) +
            C ((p - 1).choose b : ZMod p)) * q ^ (p - 1) := by
          simp only [lastb, lastb1]; ring
      _ = q * C (0 : ZMod p) * q ^ (p - 1) := by rw [this]
      _ = 0 := by simp
  have : Sb = q * Sb1 + q * Sb := by
    calc
      Sb = q * (Sb1 - lastb1) + q * (Sb - lastb) := h'
      _ = q * Sb1 + q * Sb - (q * lastb1 + q * lastb) := by ring
      _ = q * Sb1 + q * Sb - 0 := by rw [hlast]
      _ = q * Sb1 + q * Sb := by ring
  have hsub : Sb - q * Sb - q * Sb1 = 0 := by
    linear_combination this
  have hq : (1 : (ZMod p)[X]) - q = -X := by
    unfold q; ring
  calc
    X * Sb + q * Sb1 = -((1 - q) * Sb - q * Sb1) := by rw [hq]; ring
    _ = -(Sb - q * Sb - q * Sb1) := by ring
    _ = -0 := by rw [hsub]
    _ = 0 := by ring

lemma geomChoosePoly_eq {b : ℕ} (hbp : b ≤ p - 1) :
    geomChoosePoly (p := p) b =
      C ((-1 : ZMod p) ^ b) * ((1 + X : (ZMod p)[X]) ^ b * X ^ (p - 1 - b)) := by
  induction b with
  | zero =>
    simp only [pow_zero, map_one, one_mul, tsub_zero]
    exact geomChoosePoly_zero
  | succ b ih =>
    have hb0 : 1 ≤ b + 1 := Nat.succ_pos _
    have hbp' : b + 1 < p := by omega
    have hble : b ≤ p - 1 := by omega
    have hmul := geomChoosePoly_mul_X (p := p) (b := b + 1) hb0 hbp'
    simp only [Nat.add_sub_cancel] at hmul
    have ih' := ih hble
    have hL : (X : (ZMod p)[X]) * geomChoosePoly (p := p) (b + 1) =
        - (1 + X) * geomChoosePoly (p := p) b := by
      linear_combination hmul
    have hR : (X : (ZMod p)[X]) *
        (C ((-1 : ZMod p) ^ (b + 1)) * ((1 + X) ^ (b + 1) * X ^ (p - 1 - (b + 1)))) =
        - (1 + X) * geomChoosePoly (p := p) b := by
      have hexp : p - 1 - b = p - 1 - (b + 1) + 1 := by omega
      have hpow : (X : (ZMod p)[X]) ^ (p - 1 - b) =
          X * X ^ (p - 1 - (b + 1)) := by
        have : (X : (ZMod p)[X]) ^ (p - 1 - b) =
            X ^ (p - 1 - (b + 1) + 1) := congrArg (fun n => X ^ n) hexp
        rw [this, pow_succ]
        ring
      rw [ih', pow_succ, pow_succ]
      simp only [map_mul, map_neg, map_one]
      rw [hpow]
      ring
    have hX : (X : (ZMod p)[X]) *
        (geomChoosePoly (p := p) (b + 1) -
          C ((-1 : ZMod p) ^ (b + 1)) * ((1 + X) ^ (b + 1) * X ^ (p - 1 - (b + 1)))) = 0 := by
      rw [mul_sub, hL, hR]
      ring
    have hXne : (X : (ZMod p)[X]) ≠ 0 := X_ne_zero
    exact sub_eq_zero.mp ((mul_eq_zero.mp hX).resolve_left hXne)

/-- `∑_{j=0}^{p-1} C(j,a) C(j,b) = [X^a] S_b`. -/
lemma sum_choose_mul_choose_eq_coeff (a b : ℕ) :
    (∑ j ∈ range p, (j.choose a : ZMod p) * (j.choose b : ZMod p)) =
      (geomChoosePoly (p := p) b).coeff a := by
  unfold geomChoosePoly
  rw [finset_sum_coeff]
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul, coeff_one_add_X_pow]
  ring

/-- Closed form for `J_full(a,b)`. -/
lemma sum_choose_mul_choose (a b : ℕ) (hb : b ≤ p - 1) :
    (∑ j ∈ range p, (j.choose a : ZMod p) * (j.choose b : ZMod p)) =
      if p - 1 - b ≤ a then
        ((-1 : ZMod p) ^ b) * (b.choose (a - (p - 1 - b)) : ZMod p)
      else 0 := by
  rw [sum_choose_mul_choose_eq_coeff, geomChoosePoly_eq hb, coeff_C_mul]
  have hcomm :
      (((1 + X : (ZMod p)[X]) ^ b * X ^ (p - 1 - b)).coeff a) =
        ((X ^ (p - 1 - b) * (1 + X) ^ b : (ZMod p)[X]).coeff a) := by
    rw [mul_comm]
  rw [hcomm, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_one_add_X_pow]
  · simp

end GeomChoose

lemma sum_choose_mul_choose_upto {p a b : ℕ} [Fact p.Prime] [NeZero p]
    (ha : a ≤ p - 2) (hb : b ≤ p - 2) :
    (∑ j ∈ range (p - 1), (j.choose a : ZMod p) * (j.choose b : ZMod p)) =
      (∑ j ∈ range p, (j.choose a : ZMod p) * (j.choose b : ZMod p)) -
        ((-1 : ZMod p) ^ (a + b)) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hrange : range p = insert (p - 1) (range (p - 1)) := by
    have h : range p = range ((p - 1) + 1) := by
      congr 1
      exact (Nat.sub_add_cancel hp1).symm
    rw [h, range_add_one]
  rw [hrange, sum_insert (by simp [mem_range])]
  have ha' : a ≤ p - 1 := by omega
  have hb' : b ≤ p - 1 := by omega
  rw [choose_prime_pred ha', choose_prime_pred hb', pow_add]
  ring

lemma harmonic_div_eq_alt (n : ℕ) (hn : 1 ≤ n) :
    harmonic n / n =
      ∑ k ∈ Icc 1 n,
        ((-1 : ℚ) ^ (k - 1) * (n - 1).choose (k - 1) / (k : ℚ) ^ 2) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h := (sum_alternating_choose_div n).symm
  have hdiv : harmonic n / n =
      ∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / ((n : ℚ) * k)) := by
    have h' := congrArg (fun t : ℚ => t / (n : ℚ)) h
    dsimp at h'
    rw [h', sum_div]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : (k : ℚ) ≠ 0 := by
      have := (mem_Icc.mp hk).1; exact_mod_cast (show k ≠ 0 by omega)
    field_simp [hn0, hk0]
  rw [hdiv]
  refine sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hid : ((n - 1).choose (k - 1) : ℚ) / k = (n.choose k : ℚ) / n := by
    have h := choose_pred_div_eq (n - 1) k hk1
    have hnQ : ((n - 1 : ℕ) : ℚ) + 1 = n := by
      rw [Nat.cast_sub hn, Nat.cast_one]; ring
    rwa [Nat.sub_add_cancel hn, hnQ] at h
  have hL : ((-1 : ℚ) ^ (k - 1) * n.choose k / ((n : ℚ) * k)) =
      ((-1 : ℚ) ^ (k - 1)) * ((n.choose k : ℚ) / n / k) := by
    field_simp [hn0, hk0]
  have hR : ((-1 : ℚ) ^ (k - 1) * (n - 1).choose (k - 1) / (k : ℚ) ^ 2) =
      ((-1 : ℚ) ^ (k - 1)) * (((n - 1).choose (k - 1) : ℚ) / k / k) := by
    field_simp [hk0]
  rw [hL, hR, hid]

lemma ratZMod_neg_one_pow {q m : ℕ} [NeZero q] :
    ratZMod q ((-1 : ℚ) ^ m) = (-1 : ZMod q) ^ m := by
  induction m with
  | zero => simp [ratZMod_one]
  | succ m ih =>
    rw [pow_succ, pow_succ, ratZMod_mul (by simp) (by simp), ih]
    simp [ratZMod_neg, ratZMod_one]

lemma den_inv_nat_unit_prime {p k : ℕ} [Fact p.Prime] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (((1 : ℚ) / k).den : ZMod p) := by
  have hk0 : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
  have : (1 : ℚ) / k = ((1 : ℤ) : ℚ) / (k : ℕ) := by simp
  rw [this]
  exact isUnit_natCast_of_dvd (den_div_of_int_div_nat (a := 1) (d := k) hk0)
    (isUnit_zmod_prime hk)

lemma den_inv_sq_unit_prime {p k : ℕ} [Fact p.Prime] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit (((1 : ℚ) / (k : ℚ) ^ 2).den : ZMod p) := by
  have hk0n : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk0n
  have : (1 : ℚ) / (k : ℚ) ^ 2 = ((1 : ℤ) : ℚ) / (k ^ 2 : ℕ) := by
    push_cast; field_simp [hk0]
  rw [this]
  have hunit2 : IsUnit ((k ^ 2 : ℕ) : ZMod p) := by
    rw [Nat.cast_pow]; exact (isUnit_zmod_prime hk).pow 2
  exact isUnit_natCast_of_dvd (den_div_of_int_div_nat (a := 1) (d := k ^ 2)
      (pow_ne_zero 2 hk0n)) hunit2

lemma den_harmonic_unit_prime {p n : ℕ} [Fact p.Prime] [NeZero p]
    (hn : n ≤ p - 1) :
    IsUnit ((harmonic n).den : ZMod p) := by
  rw [harmonic_eq_sum]
  refine den_isUnit_sum _ _ ?_
  intro k hk
  have : k ∈ Icc 1 (p - 1) := by simp only [mem_Icc] at hk ⊢; omega
  exact den_inv_nat_unit_prime this

lemma den_harmonic₂_unit_prime {p n : ℕ} [Fact p.Prime] [NeZero p]
    (hn : n ≤ p - 1) :
    IsUnit ((harmonic₂ n).den : ZMod p) := by
  unfold harmonic₂
  refine den_isUnit_sum _ _ ?_
  intro k hk
  have : k ∈ Icc 1 (p - 1) := by simp only [mem_Icc] at hk ⊢; omega
  exact den_inv_sq_unit_prime this

lemma ratZMod_harmonic_prime {p n : ℕ} [Fact p.Prime] [NeZero p]
    (hn : n ≤ p - 1) :
    ratZMod p (harmonic n) = ∑ k ∈ Icc 1 n, (k : ZMod p)⁻¹ := by
  rw [harmonic_eq_sum]
  refine (ratZMod_sum (s := Icc 1 n) (f := fun k => (1 : ℚ) / k) ?_).trans ?_
  · intro k hk
    have : k ∈ Icc 1 (p - 1) := by simp only [mem_Icc] at hk ⊢; omega
    exact den_inv_nat_unit_prime this
  · refine sum_congr rfl fun k hk => ?_
    have hmem : k ∈ Icc 1 (p - 1) := by simp only [mem_Icc] at hk ⊢; omega
    have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    have : (1 : ℚ) / k = ((1 : ℤ) : ℚ) / (k : ℕ) := by simp
    rw [this, ratZMod_eq_div (n := 1) (d := k) hk0 (isUnit_zmod_prime hmem)]
    simp

lemma ratZMod_inv_sq_prime {p k : ℕ} [Fact p.Prime] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    ratZMod p ((1 : ℚ) / (k : ℚ) ^ 2) = ((k : ZMod p)⁻¹) ^ 2 := by
  have hk0n : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk0n
  have hunit := isUnit_zmod_prime hk
  have : (1 : ℚ) / (k : ℚ) ^ 2 = ((1 : ℤ) : ℚ) / (k ^ 2 : ℕ) := by
    push_cast; field_simp [hk0]
  rw [this]
  have hunit2 : IsUnit ((k ^ 2 : ℕ) : ZMod p) := by
    rw [Nat.cast_pow]; exact hunit.pow 2
  rw [ratZMod_eq_div (n := 1) (d := k ^ 2) (pow_ne_zero 2 hk0n) hunit2]
  simp [Nat.cast_pow, inv_pow]

lemma ratZMod_harmonic₂_prime {p n : ℕ} [Fact p.Prime] [NeZero p]
    (hn : n ≤ p - 1) :
    ratZMod p (harmonic₂ n) = ∑ k ∈ Icc 1 n, ((k : ZMod p)⁻¹) ^ 2 := by
  unfold harmonic₂
  refine (ratZMod_sum (s := Icc 1 n) (f := fun k => (1 : ℚ) / (k : ℚ) ^ 2) ?_).trans ?_
  · intro k hk
    have : k ∈ Icc 1 (p - 1) := by simp only [mem_Icc] at hk ⊢; omega
    exact den_inv_sq_unit_prime this
  · refine sum_congr rfl fun k hk => ?_
    have hmem : k ∈ Icc 1 (p - 1) := by simp only [mem_Icc] at hk ⊢; omega
    exact ratZMod_inv_sq_prime hmem

lemma harm_div_eq_alt_Fp {p n : ℕ} [Fact p.Prime] [NeZero p]
    (hn1 : 1 ≤ n) (hn : n ≤ p - 1) :
    (∑ j ∈ Icc 1 n, (j : ZMod p)⁻¹) * (n : ZMod p)⁻¹ =
      ∑ k ∈ Icc 1 n,
        ((-1 : ZMod p) ^ (k - 1) * ((n - 1).choose (k - 1) : ZMod p) *
          ((k : ZMod p)⁻¹) ^ 2) := by
  have hQ := harmonic_div_eq_alt n hn1
  have hmem : n ∈ Icc 1 (p - 1) := by simp [mem_Icc]; omega
  have hunit_n := isUnit_zmod_prime hmem
  have hn0 : n ≠ 0 := by omega
  have hn0Q : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hdenH := den_harmonic_unit_prime (p := p) hn
  have hdenN : IsUnit (((n : ℚ).den : ZMod p)) := by simp [Rat.den_natCast]
  have hnumN : IsUnit (((n : ℚ).num : ZMod p)) := by
    simpa [Rat.num_natCast] using hunit_n
  have hL : ratZMod p (harmonic n / n) =
      (∑ j ∈ Icc 1 n, (j : ZMod p)⁻¹) * (n : ZMod p)⁻¹ := by
    rw [ratZMod_div hn0Q hdenH hdenN hnumN, ratZMod_harmonic_prime hn, ratZMod_nat]
  have hterm_u : ∀ k ∈ Icc 1 n,
      IsUnit (((( -1 : ℚ) ^ (k - 1) * (n - 1).choose (k - 1) / (k : ℚ) ^ 2).den : ZMod p)) := by
    intro k hk
    have hmemk : k ∈ Icc 1 (p - 1) := by
      simp only [mem_Icc] at hk ⊢; omega
    have h1 : IsUnit (((((-1 : ℚ) ^ (k - 1)).den : ZMod p))) := by simp
    have hC : IsUnit ((((n - 1).choose (k - 1) : ℚ).den : ZMod p)) :=
      choose_den_unit _ _
    have : ((-1 : ℚ) ^ (k - 1) * (n - 1).choose (k - 1) / (k : ℚ) ^ 2) =
        ((-1 : ℚ) ^ (k - 1)) * ((n - 1).choose (k - 1) : ℚ) * (1 / (k : ℚ) ^ 2) := by
      field_simp
    rw [this]
    exact den_isUnit_of_mul (den_isUnit_of_mul h1 hC) (den_inv_sq_unit_prime hmemk)
  have hR : ratZMod p
      (∑ k ∈ Icc 1 n,
        ((-1 : ℚ) ^ (k - 1) * (n - 1).choose (k - 1) / (k : ℚ) ^ 2)) =
      ∑ k ∈ Icc 1 n,
        ((-1 : ZMod p) ^ (k - 1) * ((n - 1).choose (k - 1) : ZMod p) *
          ((k : ZMod p)⁻¹) ^ 2) := by
    rw [ratZMod_sum _ _ hterm_u]
    refine sum_congr rfl fun k hk => ?_
    have hmemk : k ∈ Icc 1 (p - 1) := by
      simp only [mem_Icc] at hk ⊢; omega
    have hk0 : (k : ℚ) ≠ 0 := by
      have := (mem_Icc.mp hk).1; exact_mod_cast (show k ≠ 0 by omega)
    have h1 : IsUnit (((((-1 : ℚ) ^ (k - 1)).den : ZMod p))) := by simp
    have hC : IsUnit ((((n - 1).choose (k - 1) : ℚ).den : ZMod p)) :=
      choose_den_unit _ _
    have : ((-1 : ℚ) ^ (k - 1) * (n - 1).choose (k - 1) / (k : ℚ) ^ 2) =
        ((-1 : ℚ) ^ (k - 1)) * ((n - 1).choose (k - 1) : ℚ) * (1 / (k : ℚ) ^ 2) := by
      field_simp [hk0]
    rw [this, ratZMod_mul (den_isUnit_of_mul h1 hC) (den_inv_sq_unit_prime hmemk),
      ratZMod_mul h1 hC, ratZMod_neg_one_pow, ratZMod_choose,
      ratZMod_inv_sq_prime hmemk]
  exact (hL.symm.trans (by rw [hQ])).trans hR

lemma sum_harm_div_sq_eq_prefix {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
      ((∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (k : ZMod p)⁻¹) ^ 2 =
    ∑ k ∈ Icc 1 (p - 1),
      (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 := by
  have hterm : ∀ k ∈ Icc 1 (p - 1),
      ((∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (k : ZMod p)⁻¹) ^ 2 =
        (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 +
        (2 : ZMod p) * (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) * ((k : ZMod p)⁻¹) ^ 3 +
        ((k : ZMod p)⁻¹) ^ 4 := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
    rw [harmFp_prefix_last (p := p) hk1 hk2]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib]
  have hmid :
      ∑ k ∈ Icc 1 (p - 1),
          (2 : ZMod p) * (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) * ((k : ZMod p)⁻¹) ^ 3 =
        (2 : ZMod p) * ∑ k ∈ Icc 1 (p - 1),
          (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) * ((k : ZMod p)⁻¹) ^ 3 := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => by ring
  rw [hmid, sum_harm_prefix_div_k3 hp, harmFp4_sum hp, mul_zero, add_zero, add_zero]

lemma sum_harm_div_sq_expand {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
      ((∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (k : ZMod p)⁻¹) ^ 2 =
    ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
      ((-1 : ZMod p) ^ (a + b) *
        (∑ j ∈ range (p - 1), (j.choose a : ZMod p) * (j.choose b : ZMod p)) *
        (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
        (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) := by
  have hterm : ∀ k ∈ Icc 1 (p - 1),
      ((∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (k : ZMod p)⁻¹) ^ 2 =
        ∑ a ∈ range k, ∑ b ∈ range k,
          ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
            ((k - 1).choose b : ZMod p) *
            (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
    have halt := harm_div_eq_alt_Fp (p := p) (n := k) hk1 hk2
    have hreind :
        ∑ t ∈ Icc 1 k,
            ((-1 : ZMod p) ^ (t - 1) * ((k - 1).choose (t - 1) : ZMod p) *
              ((t : ZMod p)⁻¹) ^ 2) =
          ∑ a ∈ range k,
            ((-1 : ZMod p) ^ a * ((k - 1).choose a : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2) := by
      have himg : Icc 1 k = (range k).image (fun a => a + 1) := by
        ext x
        simp only [mem_Icc, mem_image, mem_range]
        constructor
        · intro ⟨hx1, hx2⟩; exact ⟨x - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩; omega
      have hinj : Set.InjOn (fun a : ℕ => a + 1) (range k) :=
        fun x _ y _ h => Nat.succ_injective h
      rw [himg, sum_image hinj]
      refine sum_congr rfl fun a _ => ?_
      simp [add_tsub_cancel_right]
    rw [halt, hreind, sq, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [pow_add]
    ring
  rw [sum_congr rfl hterm]
  have hext : ∀ k ∈ Icc 1 (p - 1),
      ∑ a ∈ range k, ∑ b ∈ range k,
          ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
            ((k - 1).choose b : ZMod p) *
            (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) =
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
          (if a < k ∧ b < k then
            ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
              ((k - 1).choose b : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
              (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
          else 0) := by
    intro k hk
    have hk2 : k ≤ p - 1 := (mem_Icc.mp hk).2
    have hsub : range k ⊆ range (p - 1) := by
      intro x hx; simp only [mem_range] at hx ⊢; omega
    have h1 :
        ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
            (if a < k ∧ b < k then
              ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
                ((k - 1).choose b : ZMod p) *
                (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
                (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
            else 0) =
          ∑ a ∈ range k, ∑ b ∈ range (p - 1),
            (if a < k ∧ b < k then
              ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
                ((k - 1).choose b : ZMod p) *
                (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
                (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
            else 0) := by
      refine (sum_subset (s₁ := range k) (s₂ := range (p - 1)) (f := fun a =>
          ∑ b ∈ range (p - 1),
            (if a < k ∧ b < k then
              ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
                ((k - 1).choose b : ZMod p) *
                (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
                (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
            else 0)) hsub ?_).symm
      intro a _ ha
      have : ¬ a < k := by simpa [mem_range] using ha
      exact sum_eq_zero fun b _ => by simp [this]
    have h2 :
        ∑ a ∈ range k, ∑ b ∈ range (p - 1),
            (if a < k ∧ b < k then
              ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
                ((k - 1).choose b : ZMod p) *
                (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
                (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
            else 0) =
          ∑ a ∈ range k, ∑ b ∈ range k,
            (if a < k ∧ b < k then
              ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
                ((k - 1).choose b : ZMod p) *
                (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
                (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
            else 0) := by
      refine sum_congr (s₁ := range k) rfl fun a ha => ?_
      refine (sum_subset (s₁ := range k) (s₂ := range (p - 1)) (f := fun b =>
          (if a < k ∧ b < k then
            ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
              ((k - 1).choose b : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
              (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
          else 0)) hsub ?_).symm
      intro b _ hb
      have : ¬ b < k := by simpa [mem_range] using hb
      simp [this]
    have h3 :
        ∑ a ∈ range k, ∑ b ∈ range k,
            (if a < k ∧ b < k then
              ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
                ((k - 1).choose b : ZMod p) *
                (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
                (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
            else 0) =
          ∑ a ∈ range k, ∑ b ∈ range k,
            ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
              ((k - 1).choose b : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
              (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) := by
      refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
      have : a < k ∧ b < k := ⟨mem_range.mp ha, mem_range.mp hb⟩
      simp [this]
    exact (h3.symm.trans h2.symm).trans h1.symm
  rw [sum_congr rfl hext]
  have hswap :
      ∑ k ∈ Icc 1 (p - 1), ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
          (if a < k ∧ b < k then
            ((-1 : ZMod p) ^ (a + b) * ((k - 1).choose a : ZMod p) *
              ((k - 1).choose b : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
              (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
          else 0) =
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
        ((-1 : ZMod p) ^ (a + b) *
          (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
          (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
          ∑ k ∈ Icc 1 (p - 1),
            (if a < k ∧ b < k then
              ((k - 1).choose a : ZMod p) * ((k - 1).choose b : ZMod p)
            else 0)) := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    simp only [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [hswap]
  refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
  have ha' : a < p - 1 := mem_range.mp ha
  have hb' : b < p - 1 := mem_range.mp hb
  have hJ :
      ∑ k ∈ Icc 1 (p - 1),
          (if a < k ∧ b < k then
            ((k - 1).choose a : ZMod p) * ((k - 1).choose b : ZMod p)
          else 0) =
        ∑ j ∈ range (p - 1), (j.choose a : ZMod p) * (j.choose b : ZMod p) := by
    have himg : Icc 1 (p - 1) = (range (p - 1)).image (fun j => j + 1) := by
      ext x
      simp only [mem_Icc, mem_image, mem_range]
      constructor
      · intro ⟨hx1, hx2⟩; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    have hinj : Set.InjOn (fun j : ℕ => j + 1) (range (p - 1)) :=
      fun x _ y _ h => Nat.succ_injective h
    rw [himg, sum_image hinj]
    refine sum_congr rfl fun j hj => ?_
    have : a < j + 1 ∧ b < j + 1 ↔ a ≤ j ∧ b ≤ j := by omega
    -- C(j,a)=0 if j < a
    by_cases hle : a ≤ j ∧ b ≤ j
    · simp [show a < j + 1 ∧ b < j + 1 by omega, add_tsub_cancel_right]
    · have hzero : (j.choose a : ZMod p) * (j.choose b : ZMod p) = 0 := by
        by_cases ha0 : a ≤ j
        · have : j < b := by omega
          rw [choose_eq_zero_of_lt this, Nat.cast_zero, mul_zero]
        · rw [choose_eq_zero_of_lt (show j < a by omega), Nat.cast_zero, zero_mul]
      simp [show ¬ (a < j + 1 ∧ b < j + 1) by omega, hzero]
  rw [hJ]
  ring

lemma sum_choose_mul_choose_closed {p a b : ℕ} [Fact p.Prime] [NeZero p]
    (ha : a ≤ p - 2) (hb : b ≤ p - 2) :
    (∑ j ∈ range (p - 1), (j.choose a : ZMod p) * (j.choose b : ZMod p)) =
      (if p - 1 - b ≤ a then
        ((-1 : ZMod p) ^ b) * (b.choose (a - (p - 1 - b)) : ZMod p)
      else 0) - ((-1 : ZMod p) ^ (a + b)) := by
  have hb' : b ≤ p - 1 := by omega
  rw [sum_choose_mul_choose_upto ha hb, sum_choose_mul_choose a b hb']

lemma harm2_sq_eq_zero {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2) ^ 2 = 0 := by
  rw [harmFp2_sum hp, sq, mul_zero]

/-- After cancelling the `(-1)^{a+b}` piece against `H₂² = 0`, only the high terms remain. -/
lemma sum_harm_div_sq_high {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
      ((∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (k : ZMod p)⁻¹) ^ 2 =
    ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
      (if p - 1 - b ≤ a then
        ((-1 : ZMod p) ^ a) * (b.choose (a - (p - 1 - b)) : ZMod p) *
          (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2
      else 0) := by
  rw [sum_harm_div_sq_expand hp]
  have hsplit :
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
          ((-1 : ZMod p) ^ (a + b) *
            (∑ j ∈ range (p - 1), (j.choose a : ZMod p) * (j.choose b : ZMod p)) *
            (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) =
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
          ((-1 : ZMod p) ^ (a + b) *
            ((if p - 1 - b ≤ a then
                ((-1 : ZMod p) ^ b) * (b.choose (a - (p - 1 - b)) : ZMod p)
              else 0) - ((-1 : ZMod p) ^ (a + b))) *
            (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) := by
    refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
    have ha' : a ≤ p - 2 := by have := mem_range.mp ha; omega
    have hb' : b ≤ p - 2 := by have := mem_range.mp hb; omega
    rw [sum_choose_mul_choose_closed ha' hb']
  rw [hsplit]
  have hterm : ∀ a b : ℕ,
      ((-1 : ZMod p) ^ (a + b) *
        ((if p - 1 - b ≤ a then
            ((-1 : ZMod p) ^ b) * (b.choose (a - (p - 1 - b)) : ZMod p)
          else 0) - ((-1 : ZMod p) ^ (a + b))) *
        (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
        (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) =
      (if p - 1 - b ≤ a then
        ((-1 : ZMod p) ^ a) * (b.choose (a - (p - 1 - b)) : ZMod p) *
          (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2
      else 0) -
      (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
    intro a b
    have hone : ((-1 : ZMod p) ^ (a + b)) * ((-1 : ZMod p) ^ (a + b)) = 1 := by
      rw [← pow_add, show (a + b) + (a + b) = 2 * (a + b) by ring, pow_mul, neg_one_sq, one_pow]
    have hsgn : ((-1 : ZMod p) ^ (a + b)) * ((-1 : ZMod p) ^ b) = (-1 : ZMod p) ^ a := by
      have hb2 : ((-1 : ZMod p) ^ b) * ((-1 : ZMod p) ^ b) = 1 := by
        rw [← pow_add, show b + b = 2 * b by ring, pow_mul, neg_one_sq, one_pow]
      rw [pow_add, mul_assoc, hb2, mul_one]
    split_ifs with h
    · have hexpand :
          ((-1 : ZMod p) ^ (a + b) *
            (((-1 : ZMod p) ^ b) * (b.choose (a - (p - 1 - b)) : ZMod p) -
              ((-1 : ZMod p) ^ (a + b))) *
            (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) =
          ((((-1 : ZMod p) ^ (a + b)) * ((-1 : ZMod p) ^ b)) *
              (b.choose (a - (p - 1 - b)) : ZMod p) -
            ((-1 : ZMod p) ^ (a + b)) * ((-1 : ZMod p) ^ (a + b))) *
            (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by ring
      rw [hexpand, hsgn, hone]
      ring
    · simp [hone]
  have hdist :
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
          ((-1 : ZMod p) ^ (a + b) *
            ((if p - 1 - b ≤ a then
                ((-1 : ZMod p) ^ b) * (b.choose (a - (p - 1 - b)) : ZMod p)
              else 0) - ((-1 : ZMod p) ^ (a + b))) *
            (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) =
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
          (if p - 1 - b ≤ a then
            ((-1 : ZMod p) ^ a) * (b.choose (a - (p - 1 - b)) : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2
          else 0) -
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
        (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 := by
    have hsum := sum_congr (s₁ := range (p - 1)) rfl
      (fun a _ => sum_congr (s₁ := range (p - 1)) rfl (fun b _ => hterm a b))
    rw [hsum]
    simp_rw [sum_sub_distrib]
  rw [hdist]
  have hH2 :
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
          (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 =
        (∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2) ^ 2 := by
    have hre : ∑ a ∈ range (p - 1), (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 =
        ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 := by
      have himg : Icc 1 (p - 1) = (range (p - 1)).image (fun a => a + 1) := by
        ext x
        simp only [mem_Icc, mem_image, mem_range]
        constructor
        · intro ⟨hx1, hx2⟩; exact ⟨x - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩; omega
      have hinj : Set.InjOn (fun a : ℕ => a + 1) (range (p - 1)) :=
        fun x _ y _ h => Nat.succ_injective h
      rw [himg, sum_image hinj]
    have hprod :
        ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
            (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 =
          (∑ a ∈ range (p - 1), (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2) *
            (∑ b ∈ range (p - 1), (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2) := by
      simp_rw [← mul_sum]
      exact (sum_mul _ _ _).symm
    rw [hprod, hre, sq]
  rw [hH2, harm2_sq_eq_zero hp, sub_zero]

lemma inv_succ_eq_neg_inv {p s : ℕ} [Fact p.Prime] [NeZero p]
    (hs : s ∈ Icc 1 (p - 1)) :
    (((p - s : ℕ) : ZMod p)⁻¹) = -((s : ZMod p)⁻¹) := by
  -- p - s ≡ -s
  have hmem : p - s ∈ Icc 1 (p - 1) := mem_Icc_p_sub hs
  have : ((p - s : ℕ) : ZMod p) = -((s : ZMod p)) := by
    have hsle : s ≤ p := le_p_of_mem_Icc hs
    rw [Nat.cast_sub hsle, CharP.cast_eq_zero, zero_sub]
  rw [this, inv_neg_of_unit (isUnit_zmod_prime hs)]

lemma sum_harm_div_sq_reindex {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
      ((∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (k : ZMod p)⁻¹) ^ 2 =
    ∑ b ∈ range (p - 1),
      (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
        ∑ s ∈ Icc 1 b,
          ((-1 : ZMod p) ^ s * (b.choose s : ZMod p) * ((s : ZMod p)⁻¹) ^ 2) := by
  rw [sum_harm_div_sq_high hp]
  -- only terms with a + b ≥ p - 1, i.e. p-1-b ≤ a, and a,b ≤ p-2
  have hfilter :
      ∑ a ∈ range (p - 1), ∑ b ∈ range (p - 1),
          (if p - 1 - b ≤ a then
            ((-1 : ZMod p) ^ a) * (b.choose (a - (p - 1 - b)) : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2
          else 0) =
      ∑ b ∈ range (p - 1), ∑ a ∈ range (p - 1),
          (if p - 1 - b ≤ a then
            ((-1 : ZMod p) ^ a) * (b.choose (a - (p - 1 - b)) : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2
          else 0) := by
    rw [sum_comm]
  rw [hfilter]
  refine sum_congr rfl fun b hb => ?_
  have hb' : b < p - 1 := mem_range.mp hb
  -- reindex a = p - 1 - s, so s = p - 1 - a
  -- p-1-b ≤ a ≤ p-2 iff 1 ≤ s ≤ b
  have hre :
      ∑ a ∈ range (p - 1),
          (if p - 1 - b ≤ a then
            ((-1 : ZMod p) ^ a) * (b.choose (a - (p - 1 - b)) : ZMod p) *
              (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2
          else 0) =
      (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
        ∑ s ∈ Icc 1 b,
          ((-1 : ZMod p) ^ s * (b.choose s : ZMod p) * ((s : ZMod p)⁻¹) ^ 2) := by
    have hodd : Even (p - 1) := by
      have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
      obtain ⟨m, hm⟩ := hodd
      refine ⟨m, by omega⟩
    -- pull out (b+1)^{-2}
    have :
        ∑ a ∈ range (p - 1),
            (if p - 1 - b ≤ a then
              ((-1 : ZMod p) ^ a) * (b.choose (a - (p - 1 - b)) : ZMod p) *
                (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2
            else 0) =
        (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
          ∑ a ∈ range (p - 1),
            (if p - 1 - b ≤ a then
              ((-1 : ZMod p) ^ a) * (b.choose (a - (p - 1 - b)) : ZMod p) *
                (((a + 1 : ℕ) : ZMod p)⁻¹) ^ 2
            else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun a _ => ?_
      split_ifs <;> ring
    rw [this]
    refine congrArg (fun t => (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 * t) ?_
    have hset :
        (range (p - 1)).filter (fun a => p - 1 - b ≤ a) =
          (Icc 1 b).image (fun s => p - 1 - s) := by
      ext a
      simp only [mem_filter, mem_range, mem_image, mem_Icc]
      constructor
      · intro ⟨ha, hle⟩
        refine ⟨p - 1 - a, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨s, ⟨hs1, hsb⟩, rfl⟩
        exact ⟨by omega, by omega⟩
    have hinj : Set.InjOn (fun s : ℕ => p - 1 - s) (Icc 1 b) :=
      fun x hx y hy hxy => by
        have hx' : x ≤ p - 1 := by
          simp only [mem_coe, mem_Icc] at hx; omega
        have hy' : y ≤ p - 1 := by
          simp only [mem_coe, mem_Icc] at hy; omega
        have : p - 1 - x = p - 1 - y := hxy
        omega
    rw [← sum_filter (p := fun a => p - 1 - b ≤ a), hset, sum_image hinj]
    refine sum_congr rfl fun s hs => ?_
    have hs1 : 1 ≤ s := (mem_Icc.mp hs).1
    have hsb : s ≤ b := (mem_Icc.mp hs).2
    have ha : p - 1 - s ≤ p - 2 := by omega
    have hsub : (p - 1 - s) - (p - 1 - b) = b - s := by omega
    have hch : b.choose ((p - 1 - s) - (p - 1 - b)) = b.choose s := by
      rw [hsub, Nat.choose_symm hsb]
    have hsgn : ((-1 : ZMod p) ^ (p - 1 - s)) = (-1 : ZMod p) ^ s := by
      have hpe : (p - 1 - s) + s = p - 1 := by omega
      have hmul : ((-1 : ZMod p) ^ (p - 1 - s)) * ((-1 : ZMod p) ^ s) =
          ((-1 : ZMod p) ^ (p - 1)) := by
        rw [← pow_add, hpe]
      have heven : ((-1 : ZMod p) ^ (p - 1)) = 1 := Even.neg_one_pow hodd
      have hss : ((-1 : ZMod p) ^ s) * ((-1 : ZMod p) ^ s) = 1 := by
        rw [← pow_add, show s + s = 2 * s by ring, pow_mul, neg_one_sq, one_pow]
      apply (mul_left_inj' (show ((-1 : ZMod p) ^ s) ≠ 0 from pow_ne_zero _ (by norm_num))).mp
      rw [hmul, heven, hss]
    have hsmem : s ∈ Icc 1 (p - 1) := by
      simp [mem_Icc]; omega
    have hcast : (((p - 1 - s + 1 : ℕ) : ZMod p)) = ((p - s : ℕ) : ZMod p) := by
      congr 1; omega
    rw [hch, hsgn, hcast, inv_succ_eq_neg_inv hsmem, neg_sq]
  exact hre

lemma sum_alt_choose_div_sq_Fp {p n : ℕ} [Fact p.Prime] [NeZero p]
    (hn : n ≤ p - 2) (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 n, ((-1 : ZMod p) ^ (k - 1) * (n.choose k : ZMod p) *
        ((k : ZMod p)⁻¹) ^ 2) =
      (2 : ZMod p)⁻¹ *
        ((∑ j ∈ Icc 1 n, (j : ZMod p)⁻¹) ^ 2 +
          ∑ j ∈ Icc 1 n, ((j : ZMod p)⁻¹) ^ 2) := by
  have hn' : n ≤ p - 1 := by omega
  have hQ := sum_alternating_choose_div_sq n
  have h2u : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr (two_ne_zero_zmod hp)
  have hL : ratZMod p
      (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2)) =
    ∑ k ∈ Icc 1 n, ((-1 : ZMod p) ^ (k - 1) * (n.choose k : ZMod p) *
        ((k : ZMod p)⁻¹) ^ 2) := by
    have hu : ∀ k ∈ Icc 1 n,
        IsUnit (((( -1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2).den : ZMod p)) := by
      intro k hk
      have hmemk : k ∈ Icc 1 (p - 1) := by simp only [mem_Icc] at hk ⊢; omega
      have h1 : IsUnit (((((-1 : ℚ) ^ (k - 1)).den : ZMod p))) := by simp
      have hC : IsUnit ((((n.choose k : ℚ).den : ZMod p))) := choose_den_unit _ _
      have : ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) =
          ((-1 : ℚ) ^ (k - 1)) * (n.choose k : ℚ) * (1 / (k : ℚ) ^ 2) := by
        field_simp
      rw [this]
      exact den_isUnit_of_mul (den_isUnit_of_mul h1 hC) (den_inv_sq_unit_prime hmemk)
    rw [ratZMod_sum _ _ hu]
    refine sum_congr rfl fun k hk => ?_
    have hmemk : k ∈ Icc 1 (p - 1) := by simp only [mem_Icc] at hk ⊢; omega
    have hk0 : (k : ℚ) ≠ 0 := by
      have := (mem_Icc.mp hk).1; exact_mod_cast (show k ≠ 0 by omega)
    have h1 : IsUnit (((((-1 : ℚ) ^ (k - 1)).den : ZMod p))) := by simp
    have hC : IsUnit ((((n.choose k : ℚ).den : ZMod p))) := choose_den_unit _ _
    have : ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2) =
        ((-1 : ℚ) ^ (k - 1)) * (n.choose k : ℚ) * (1 / (k : ℚ) ^ 2) := by
      field_simp [hk0]
    rw [this, ratZMod_mul (den_isUnit_of_mul h1 hC) (den_inv_sq_unit_prime hmemk),
      ratZMod_mul h1 hC, ratZMod_neg_one_pow, ratZMod_choose,
      ratZMod_inv_sq_prime hmemk]
  have hR : ratZMod p ((harmonic n ^ 2 + harmonic₂ n) / 2) =
      (2 : ZMod p)⁻¹ *
        ((∑ j ∈ Icc 1 n, (j : ZMod p)⁻¹) ^ 2 +
          ∑ j ∈ Icc 1 n, ((j : ZMod p)⁻¹) ^ 2) := by
    have h2n : (2 : ℚ) ≠ 0 := by norm_num
    have hden2 : IsUnit (((2 : ℚ).den : ZMod p)) := by simp
    have hnum2 : IsUnit (((2 : ℚ).num : ZMod p)) := by
      change IsUnit ((2 : ℤ) : ZMod p)
      simpa using h2u
    have hdenN : IsUnit (((harmonic n ^ 2 + harmonic₂ n).den : ZMod p)) :=
      den_isUnit_of_add (den_isUnit_pow (den_harmonic_unit_prime hn') 2)
        (den_harmonic₂_unit_prime hn')
    rw [ratZMod_div h2n hdenN hden2 hnum2, ratZMod_add
        (den_isUnit_pow (den_harmonic_unit_prime hn') 2)
        (den_harmonic₂_unit_prime hn'),
      ratZMod_pow (den_harmonic_unit_prime hn') 2,
      ratZMod_harmonic_prime hn',
      ratZMod_harmonic₂_prime hn']
    have h2eq : ratZMod p 2 = (2 : ZMod p) := ratZMod_nat p 2
    rw [h2eq]
    ring
  have heq : ratZMod p
      (∑ k ∈ Icc 1 n, ((-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2)) =
      ratZMod p ((harmonic n ^ 2 + harmonic₂ n) / 2) := by
    rw [hQ]
  exact hL.symm.trans (heq.trans hR)

lemma sum_harm_sq_prefix_div_k2 {p : ℕ} [Fact p.Prime] [NeZero p] (hp : 7 ≤ p) :
    ∑ k ∈ Icc 1 (p - 1),
      (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 = 0 := by
  have hXeq : ∑ k ∈ Icc 1 (p - 1),
      ((∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (k : ZMod p)⁻¹) ^ 2 =
    ∑ k ∈ Icc 1 (p - 1),
      (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 :=
    sum_harm_div_sq_eq_prefix hp
  have hre := sum_harm_div_sq_reindex hp
  have h2u : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr (two_ne_zero_zmod hp)
  have h2ne : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have halt :
      ∑ b ∈ range (p - 1),
          (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            ∑ s ∈ Icc 1 b,
              ((-1 : ZMod p) ^ s * (b.choose s : ZMod p) * ((s : ZMod p)⁻¹) ^ 2) =
        - (2 : ZMod p)⁻¹ *
          ∑ b ∈ range (p - 1),
            (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
              ((∑ j ∈ Icc 1 b, (j : ZMod p)⁻¹) ^ 2 +
                ∑ j ∈ Icc 1 b, ((j : ZMod p)⁻¹) ^ 2) := by
    have hinner : ∀ b ∈ range (p - 1),
        (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
          ∑ s ∈ Icc 1 b,
            ((-1 : ZMod p) ^ s * (b.choose s : ZMod p) * ((s : ZMod p)⁻¹) ^ 2) =
        (-(2 : ZMod p)⁻¹) *
          ((((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            ((∑ j ∈ Icc 1 b, (j : ZMod p)⁻¹) ^ 2 +
              ∑ j ∈ Icc 1 b, ((j : ZMod p)⁻¹) ^ 2)) := by
      intro b hb
      have hb' : b ≤ p - 2 := by have := mem_range.mp hb; omega
      have hsign :
          ∑ s ∈ Icc 1 b,
              ((-1 : ZMod p) ^ s * (b.choose s : ZMod p) * ((s : ZMod p)⁻¹) ^ 2) =
            -∑ s ∈ Icc 1 b,
              ((-1 : ZMod p) ^ (s - 1) * (b.choose s : ZMod p) * ((s : ZMod p)⁻¹) ^ 2) := by
        rw [← sum_neg_distrib]
        refine sum_congr rfl fun s hs => ?_
        have hs1 : 1 ≤ s := (mem_Icc.mp hs).1
        have hpow : ((-1 : ZMod p) ^ s) = - ((-1 : ZMod p) ^ (s - 1)) := by
          have : ((-1 : ZMod p) ^ s) = ((-1 : ZMod p) ^ (s - 1 + 1)) := by
            congr 1
            exact (Nat.sub_add_cancel hs1).symm
          rw [this, pow_add, pow_one]
          ring
        rw [hpow]
        ring
      have halt' := sum_alt_choose_div_sq_Fp (p := p) (n := b) hb' hp
      rw [hsign, halt']
      ring
    have hL := sum_congr (s₁ := range (p - 1)) rfl hinner
    have hR :
        ∑ b ∈ range (p - 1),
            (-(2 : ZMod p)⁻¹) *
              ((((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
                ((∑ j ∈ Icc 1 b, (j : ZMod p)⁻¹) ^ 2 +
                  ∑ j ∈ Icc 1 b, ((j : ZMod p)⁻¹) ^ 2)) =
          (-(2 : ZMod p)⁻¹) *
            ∑ b ∈ range (p - 1),
              (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
                ((∑ j ∈ Icc 1 b, (j : ZMod p)⁻¹) ^ 2 +
                  ∑ j ∈ Icc 1 b, ((j : ZMod p)⁻¹) ^ 2) :=
      (mul_sum _ _ _).symm
    exact hL.trans hR
  have hreind2 :
      ∑ b ∈ range (p - 1),
          (((b + 1 : ℕ) : ZMod p)⁻¹) ^ 2 *
            ((∑ j ∈ Icc 1 b, (j : ZMod p)⁻¹) ^ 2 +
              ∑ j ∈ Icc 1 b, ((j : ZMod p)⁻¹) ^ 2) =
        ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod p)⁻¹) ^ 2 *
            ((∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 +
              ∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) := by
    have himg : Icc 1 (p - 1) = (range (p - 1)).image (fun b => b + 1) := by
      ext x
      simp only [mem_Icc, mem_image, mem_range]
      constructor
      · intro ⟨hx1, hx2⟩; exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨b, hb, rfl⟩; omega
    have hinj : Set.InjOn (fun b : ℕ => b + 1) (range (p - 1)) :=
      fun x _ y _ h => Nat.succ_injective h
    rw [himg, sum_image hinj]
    refine sum_congr rfl fun b _ => ?_
    simp [add_tsub_cancel_right]
  have hsplit :
      ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod p)⁻¹) ^ 2 *
            ((∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 +
              ∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) =
        ∑ k ∈ Icc 1 (p - 1),
          (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 +
        ∑ k ∈ Icc 1 (p - 1),
          (∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => by ring
  have hsum : ∑ k ∈ Icc 1 (p - 1),
      ((∑ j ∈ Icc 1 k, (j : ZMod p)⁻¹) * (k : ZMod p)⁻¹) ^ 2 =
      - (2 : ZMod p)⁻¹ *
        ∑ k ∈ Icc 1 (p - 1),
          (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 := by
    rw [hre, halt, hreind2, hsplit, sum_harm2_prefix_div_k2 hp, add_zero]
  rw [hXeq] at hsum
  -- X = - (1/2) X
  have : (1 + (2 : ZMod p)⁻¹) *
      ∑ k ∈ Icc 1 (p - 1),
        (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 = 0 := by
    have := hsum
    linear_combination this
  have hcoeff : (1 + (2 : ZMod p)⁻¹) = (2 : ZMod p)⁻¹ * (3 : ZMod p) := by
    have h2inv : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2u
    calc
      1 + (2 : ZMod p)⁻¹ = (2 : ZMod p) * (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ := by rw [h2inv]
      _ = (2 : ZMod p)⁻¹ * (2 + 1) := by ring
      _ = (2 : ZMod p)⁻¹ * 3 := by norm_num
  rw [hcoeff] at this
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h
    exact Nat.not_dvd_of_pos_of_lt (by norm_num : 0 < 3) (by omega) hdvd
  have h2inv_ne : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2ne
  have hmul := mul_eq_zero.mp this
  rcases hmul with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h h2inv_ne
    · exact absurd h h3
  · exact h

lemma ratZMod_inv_sq {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ratZMod (p ^ r) ((1 : ℚ) / (k : ℚ) ^ 2) = ((k : ZMod (p ^ r))⁻¹) ^ 2 := by
  have hk0n : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk0n
  have hunit : IsUnit (k : ZMod (p ^ r)) := isUnit_of_mem_Icc hk
  have : (1 : ℚ) / (k : ℚ) ^ 2 = ((1 : ℤ) : ℚ) / (k ^ 2 : ℕ) := by
    push_cast; field_simp [hk0]
  rw [this]
  have hunit2 : IsUnit ((k ^ 2 : ℕ) : ZMod (p ^ r)) := by
    rw [Nat.cast_pow]; exact hunit.pow 2
  rw [ratZMod_eq_div (n := 1) (d := k ^ 2) (pow_ne_zero 2 hk0n) hunit2]
  simp only [Int.cast_one, one_mul, Nat.cast_pow]
  refine ZMod.inv_eq_of_mul_eq_one (p ^ r) ((k : ZMod (p ^ r)) ^ 2)
      (((k : ZMod (p ^ r))⁻¹) ^ 2) ?_
  have hk1 : (k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  rw [pow_two, pow_two]
  calc
    (k : ZMod (p ^ r)) * k * ((k : ZMod (p ^ r))⁻¹ * (k : ZMod (p ^ r))⁻¹) =
        ((k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
          ((k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by ring
    _ = 1 := by rw [hk1, mul_one]

lemma ratZMod_frac_pm {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ratZMod (p ^ r) (((1 : ℚ) - (p : ℚ) / k) / (1 + (p : ℚ) / k)) =
      (1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
        (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)⁻¹ := by
  have hk0n : k ≠ 0 := (mem_Icc_lt_prime (p := p) hk).1.ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk0n
  have hunit : IsUnit (k : ZMod (p ^ r)) := isUnit_of_mem_Icc hk
  have hkp0 : k + p ≠ 0 := by
    have : 0 < k + p := by
      have := (mem_Icc_lt_prime (p := p) hk).1; omega
    exact this.ne'
  set n : ℤ := (k : ℤ) - (p : ℤ)
  have hform : ((1 : ℚ) - (p : ℚ) / k) / (1 + (p : ℚ) / k) =
      (n : ℚ) / (k + p : ℕ) := by
    have hkpn : ((k : ℚ) + (p : ℚ)) = ((k + p : ℕ) : ℚ) := by push_cast; rfl
    change _ = (((k : ℤ) - (p : ℤ) : ℤ) : ℚ) / (k + p : ℕ)
    field_simp [hk0]
    rw [hkpn]
    push_cast
    ring
  rw [hform]
  have hunit_kp : IsUnit ((k + p : ℕ) : ZMod (p ^ r)) := by
    have hklt := mem_Icc_lt_prime (p := p) hk
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right r ?_
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
      intro hdvd'
      have : p ∣ k := (Nat.dvd_add_iff_left (dvd_refl p)).mpr hdvd'
      exact Nat.not_dvd_of_pos_of_lt hklt.1 hklt.2 this)).symm
  rw [ratZMod_eq_div (n := n) (d := k + p) hkp0 hunit_kp]
  have hk1 : (k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hnZ : (n : ZMod (p ^ r)) = (k : ZMod (p ^ r)) - (p : ZMod (p ^ r)) := by
    simp [n]
  have hden : ((k + p : ℕ) : ZMod (p ^ r)) =
      (k : ZMod (p ^ r)) * (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by
    rw [Nat.cast_add]
    refine Eq.symm ?_
    calc
      (k : ZMod (p ^ r)) * (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)
          = (k : ZMod (p ^ r)) * 1 +
              (k : ZMod (p ^ r)) * ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by
            rw [mul_add]
      _ = (k : ZMod (p ^ r)) +
            ((k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) * p := by ring
      _ = (k : ZMod (p ^ r)) + 1 * p := by rw [hk1]
      _ = (k : ZMod (p ^ r)) + p := by ring
  have hnum : (n : ZMod (p ^ r)) =
      (k : ZMod (p ^ r)) * (1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by
    rw [hnZ]
    refine Eq.symm ?_
    calc
      (k : ZMod (p ^ r)) * (1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)
          = (k : ZMod (p ^ r)) * 1 -
              (k : ZMod (p ^ r)) * ((p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by
            rw [mul_sub]
      _ = (k : ZMod (p ^ r)) -
            ((k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) * p := by ring
      _ = (k : ZMod (p ^ r)) - 1 * p := by rw [hk1]
      _ = (k : ZMod (p ^ r)) - p := by ring
  have hunit_fac : IsUnit (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) := by
    have hprod : (k : ZMod (p ^ r)) * (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) =
        ((k + p : ℕ) : ZMod (p ^ r)) := hden.symm
    have := (Commute.all (k : ZMod (p ^ r))
        (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)).isUnit_mul_iff
    exact (this.mp (by rw [hprod]; exact hunit_kp)).2
  have hinv :
      ((k : ZMod (p ^ r)) *
          (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹))⁻¹ =
        (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)⁻¹ *
          (k : ZMod (p ^ r))⁻¹ := by
    refine ZMod.inv_eq_of_mul_eq_one (p ^ r) _ _ ?_
    calc
      (k : ZMod (p ^ r)) * (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
          ((1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)⁻¹ *
            (k : ZMod (p ^ r))⁻¹)
          = (k : ZMod (p ^ r)) *
              ((1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
                (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)⁻¹) *
              (k : ZMod (p ^ r))⁻¹ := by ring
      _ = (k : ZMod (p ^ r)) * 1 * (k : ZMod (p ^ r))⁻¹ := by
            rw [ZMod.mul_inv_of_unit _ hunit_fac]
      _ = 1 := by rw [mul_one, hk1]
  rw [hnum, hden, hinv]
  calc
    (k : ZMod (p ^ r)) * (1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
        ((1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)⁻¹ *
          (k : ZMod (p ^ r))⁻¹)
        = ((k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
            ((1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
              (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)⁻¹) := by ring
    _ = (1 - (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹) *
            (1 + (p : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹)⁻¹ := by
          rw [hk1, one_mul]

lemma ratZMod_quad {p r i : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hi : i ∈ Icc 1 (p - 1)) :
    ratZMod (p ^ r) (1 - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2) =
      1 - (3 : ZMod (p ^ r)) * p * (i : ZMod (p ^ r))⁻¹ +
        (2 : ZMod (p ^ r)) * p ^ 2 * ((i : ZMod (p ^ r))⁻¹) ^ 2 := by
  have hi0n : i ≠ 0 := (mem_Icc_lt_prime (p := p) hi).1.ne'
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast hi0n
  have hunit : IsUnit (i : ZMod (p ^ r)) := isUnit_of_mem_Icc hi
  have hform : (1 : ℚ) - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2 =
      ((i : ℤ) ^ 2 - 3 * p * i + 2 * p ^ 2 : ℤ) / (i ^ 2 : ℕ) := by
    field_simp [hi0]
    push_cast
    ring
  rw [hform]
  have hunit2 : IsUnit ((i ^ 2 : ℕ) : ZMod (p ^ r)) := by
    rw [Nat.cast_pow]; exact hunit.pow 2
  rw [ratZMod_eq_div (n := (i : ℤ) ^ 2 - 3 * p * i + 2 * p ^ 2) (d := i ^ 2)
      (pow_ne_zero 2 hi0n) hunit2]
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Nat.cast_pow]
  have hi1 : (i : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hinv2 : ((i : ZMod (p ^ r)) ^ 2)⁻¹ = ((i : ZMod (p ^ r))⁻¹) ^ 2 := by
    refine ZMod.inv_eq_of_mul_eq_one (p ^ r) _ _ ?_
    rw [pow_two, pow_two]
    calc
      (i : ZMod (p ^ r)) * i * ((i : ZMod (p ^ r))⁻¹ * (i : ZMod (p ^ r))⁻¹) =
          ((i : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) *
            ((i : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) := by ring
      _ = 1 := by rw [hi1, mul_one]
  rw [hinv2]
  have hi2 : (i : ZMod (p ^ r)) ^ 2 * ((i : ZMod (p ^ r))⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, hi1, one_pow]
  have hi3 : (i : ZMod (p ^ r)) * ((i : ZMod (p ^ r))⁻¹) ^ 2 =
      (i : ZMod (p ^ r))⁻¹ := by
    rw [pow_two, ← mul_assoc, hi1, one_mul]
  simp only [Int.cast_ofNat]
  rw [add_mul, sub_mul, hi2]
  have hmid : ((3 : ZMod (p ^ r)) * p * i) * ((i : ZMod (p ^ r))⁻¹) ^ 2 =
      (3 : ZMod (p ^ r)) * p * (i : ZMod (p ^ r))⁻¹ := by
    calc
      ((3 : ZMod (p ^ r)) * p * i) * ((i : ZMod (p ^ r))⁻¹) ^ 2
          = (3 : ZMod (p ^ r)) * p * (i * ((i : ZMod (p ^ r))⁻¹) ^ 2) := by
            ring
      _ = (3 : ZMod (p ^ r)) * p * (i : ZMod (p ^ r))⁻¹ := by rw [hi3]
  rw [hmid]

lemma ratZMod_Wrat {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)] :
    ratZMod (p ^ r) (Wrat p) = Wz p r := by
  unfold Wrat Wz
  refine (ratZMod_sum _ _ (fun k hk => den_Wrat_term_unit hk)).trans ?_
  refine sum_congr rfl fun k hk => ?_
  have h1 := den_inv_sq_unit (p := p) (r := r) hk
  have h2 := den_frac_pm_unit (p := p) (r := r) hk
  have h3 : IsUnit (((∏ i ∈ Icc 1 (k - 1),
        (1 - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2)).den : ZMod (p ^ r))) := by
    refine den_isUnit_prod _ _ ?_
    intro i hi
    have hik : i ∈ Icc 1 (p - 1) := by
      have hi' := mem_Icc.mp hi
      have hk' := mem_Icc.mp hk
      exact mem_Icc.mpr ⟨hi'.1, by omega⟩
    exact den_quad_unit hik
  rw [ratZMod_mul (den_isUnit_of_mul h1 h2) h3, ratZMod_mul h1 h2,
    ratZMod_inv_sq hk, ratZMod_frac_pm hk]
  have hf : ∀ i ∈ Icc 1 (k - 1),
      IsUnit (((1 : ℚ) - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2).den :
        ZMod (p ^ r)) := by
    intro i hi
    have hik : i ∈ Icc 1 (p - 1) := by
      have hi' := mem_Icc.mp hi
      have hk' := mem_Icc.mp hk
      exact mem_Icc.mpr ⟨hi'.1, by omega⟩
    exact den_quad_unit hik
  rw [ratZMod_prod (Icc 1 (k - 1))
      (fun i => (1 : ℚ) - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2) hf]
  congr 1
  refine Finset.prod_congr (s₁ := Icc 1 (k - 1)) (s₂ := Icc 1 (k - 1))
      (f := fun i => ratZMod (p ^ r)
        (1 - 3 * (p : ℚ) / i + 2 * (p : ℚ) ^ 2 / i ^ 2))
      (g := fun i =>
        (1 : ZMod (p ^ r)) - (3 : ZMod (p ^ r)) * p * (i : ZMod (p ^ r))⁻¹ +
          (2 : ZMod (p ^ r)) * p ^ 2 * ((i : ZMod (p ^ r))⁻¹) ^ 2) rfl
      fun i hi => ?_
  have hik : i ∈ Icc 1 (p - 1) := by
    have hi' := mem_Icc.mp hi
    have hk' := mem_Icc.mp hk
    exact mem_Icc.mpr ⟨hi'.1, by omega⟩
  exact ratZMod_quad hik

lemma p_pow_five_eq_zero (p : ℕ) [NeZero (p ^ 5)] :
    (p : ZMod (p ^ 5)) ^ 5 = 0 :=
  nat_cast_p_pow_eq_zero p 5

lemma p_mul_inv_pow_five {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ((p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) ^ 5 = 0 := by
  rw [mul_pow, p_pow_five_eq_zero, zero_mul]

/-- `(1 + p/k)⁻¹ = ∑_{i<5} (-p/k)^i` in `ZMod (p⁵)`. -/
lemma inv_one_add_p_div {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    (hk : k ∈ Icc 1 (p - 1)) :
    (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹ =
      ∑ i ∈ range 5, (-((p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)) ^ i :=
  inv_one_add_of_pow_eq_zero _ (p_mul_inv_pow_five hk)

lemma frac_pm_eq {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    (hk : k ∈ Icc 1 (p - 1)) :
    (1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
      (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹ =
      (1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
        ∑ i ∈ range 5, (-((p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)) ^ i := by
  rw [inv_one_add_p_div hk]

/-- The factor `(1-p/k)/(1+p/k)` equals `1 - 2p/k + 2 (p/k)²` plus a multiple of `p³`. -/
lemma frac_pm_mod_p3 {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ∃ e : ZMod (p ^ 5),
      (1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
          (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹ =
        1 - (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹ +
          (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 +
          (p : ZMod (p ^ 5)) ^ 3 * e := by
  rw [frac_pm_eq hk]
  set x : ZMod (p ^ 5) := (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹
  have hsum : ∑ i ∈ range 5, (-x) ^ i = 1 - x + x ^ 2 - x ^ 3 + x ^ 4 := by
    simp [sum_range_succ, sum_range_zero, pow_zero, pow_one, pow_two, pow_three]
    ring
  rw [hsum]
  have hx5 : x ^ 5 = 0 := by
    unfold x
    rw [mul_pow, p_pow_five_eq_zero, zero_mul]
  refine ⟨-2 * ((k : ZMod (p ^ 5))⁻¹) ^ 3 +
      2 * (p : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 4, ?_⟩
  have hx3 : x ^ 3 = (p : ZMod (p ^ 5)) ^ 3 * ((k : ZMod (p ^ 5))⁻¹) ^ 3 := by
    unfold x; rw [mul_pow]
  have hx4 : x ^ 4 = (p : ZMod (p ^ 5)) ^ 4 * ((k : ZMod (p ^ 5))⁻¹) ^ 4 := by
    unfold x; rw [mul_pow]
  have hexpand : (1 - x) * (1 - x + x ^ 2 - x ^ 3 + x ^ 4) =
      1 - 2 * x + 2 * x ^ 2 - 2 * x ^ 3 + 2 * x ^ 4 - x ^ 5 := by
    ring
  rw [hexpand, hx5, sub_zero, hx3, hx4]
  ring

lemma prod_p_y {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    (t : Finset ℕ) (y : ℕ → ZMod (p ^ 5)) :
    ∏ i ∈ t, (p : ZMod (p ^ 5)) * y i =
      (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i := by
  rw [prod_mul_distrib, prod_const]

lemma sum_powersetCard_one_eq {R : Type*} [CommRing R] [DecidableEq ℕ]
    (s : Finset ℕ) (y : ℕ → R) :
    ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, y i = ∑ i ∈ s, y i := by
  simp [powersetCard_one, prod_singleton]

/-- Product `∏ (1 + p y_i) = 1 + p ∑ y + (p²/2)((∑ y)² - ∑ y²)` plus `p³` error. -/
lemma prod_one_add_p_y {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] (hp : 7 ≤ p)
    (s : Finset ℕ) (y : ℕ → ZMod (p ^ 5)) :
    ∃ e : ZMod (p ^ 5),
      ∏ i ∈ s, (1 + (p : ZMod (p ^ 5)) * y i) =
        1 + (p : ZMod (p ^ 5)) * ∑ i ∈ s, y i +
          (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
            ((∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, (y i) ^ 2) +
          (p : ZMod (p ^ 5)) ^ 3 * e := by
  have h2u : IsUnit (2 : ZMod (p ^ 5)) := isUnit_two_zmod (by omega)
  have hprod : ∏ i ∈ s, (1 + (p : ZMod (p ^ 5)) * y i) =
      ∑ t ∈ s.powerset, (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i := by
    rw [prod_one_add]
    refine sum_congr rfl fun t _ => prod_p_y t y
  rw [hprod, sum_powerset_by_card]
  set R : Finset ℕ := range (s.card + 1)
  set R0 : Finset ℕ := R ∩ ({0} : Finset ℕ)
  set R1 : Finset ℕ := R ∩ ({1} : Finset ℕ)
  set R2 : Finset ℕ := R ∩ ({2} : Finset ℕ)
  set R3 : Finset ℕ := R.filter (fun n => 3 ≤ n)
  have hrange : R = R0 ∪ R1 ∪ R2 ∪ R3 := by
    ext n
    simp only [R, R0, R1, R2, R3, mem_union, mem_inter, mem_singleton, mem_filter,
      mem_range]
    omega
  have hd01 : Disjoint R0 R1 := by
    refine disjoint_left.mpr ?_
    intro n hn0 hn1
    simp only [R0, R1, mem_inter, mem_singleton] at hn0 hn1
    omega
  have hd012 : Disjoint (R0 ∪ R1) R2 := by
    refine disjoint_left.mpr ?_
    intro n hn hn2
    simp only [R0, R1, R2, mem_union, mem_inter, mem_singleton] at hn hn2
    omega
  have hd0123 : Disjoint (R0 ∪ R1 ∪ R2) R3 := by
    refine disjoint_left.mpr ?_
    intro n hn hn3
    simp only [R0, R1, R2, R3, mem_union, mem_inter, mem_singleton, mem_filter] at hn hn3
    omega
  rw [hrange, sum_union hd0123, sum_union hd012, sum_union hd01]
  have h0mem : (0 ∈ R) := by simp [R]
  have h0 : ∑ n ∈ R0, ∑ t ∈ s.powersetCard n,
      (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i = 1 := by
    have : R0 = ({0} : Finset ℕ) := by
      ext n; simp [R0, R, h0mem, mem_inter, mem_singleton, mem_range]
    rw [this, sum_singleton]
    simp [powersetCard_zero]
  have h1 : ∑ n ∈ R1, ∑ t ∈ s.powersetCard n,
      (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
      (p : ZMod (p ^ 5)) * ∑ i ∈ s, y i := by
    by_cases h : 1 ∈ R
    · have : R1 = ({1} : Finset ℕ) := by
        ext n; simp [R1, R, h, mem_inter, mem_singleton]
      rw [this, sum_singleton]
      have : ∑ t ∈ s.powersetCard 1,
          (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
        (p : ZMod (p ^ 5)) * ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, y i := by
        have h' : ∑ t ∈ s.powersetCard 1,
            (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
          ∑ t ∈ s.powersetCard 1,
            (p : ZMod (p ^ 5)) ^ (1 : ℕ) * ∏ i ∈ t, y i :=
          sum_congr rfl fun t ht => by
            have : t.card = 1 := (mem_powersetCard.mp ht).2
            rw [this]
        rw [h', ← mul_sum, pow_one]
      rw [this, sum_powersetCard_one_eq]
    · have : R1 = (∅ : Finset ℕ) := by
        ext n; simp [R1, h, mem_inter, mem_singleton]
      rw [this, sum_empty]
      have hcard : s.card = 0 := by
        simp only [R, mem_range, not_lt] at h
        omega
      have hs : s = ∅ := card_eq_zero.mp hcard
      simp [hs]
  have h2sum : ∑ n ∈ R2, ∑ t ∈ s.powersetCard n,
      (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
      (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
        ((∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, (y i) ^ 2) := by
    have hsq := sum_sq_eq_sum_sq_add_two_esymm s y
    have hpair : ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i =
        (2 : ZMod (p ^ 5))⁻¹ * ((∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, (y i) ^ 2) := by
      have heq : (2 : ZMod (p ^ 5)) * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i =
          (∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, (y i) ^ 2 := by
        rw [hsq]; ring
      have := congrArg (fun z : ZMod (p ^ 5) => (2 : ZMod (p ^ 5))⁻¹ * z) heq
      dsimp at this
      rw [← mul_assoc, ZMod.inv_mul_of_unit _ h2u, one_mul] at this
      exact this
    by_cases h : 2 ∈ R
    · have : R2 = ({2} : Finset ℕ) := by
        ext n; simp [R2, R, h, mem_inter, mem_singleton]
      rw [this, sum_singleton]
      have hcard : ∑ t ∈ s.powersetCard 2,
          (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
        (p : ZMod (p ^ 5)) ^ 2 * ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i := by
        have : ∑ t ∈ s.powersetCard 2,
            (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
          ∑ t ∈ s.powersetCard 2,
            (p : ZMod (p ^ 5)) ^ (2 : ℕ) * ∏ i ∈ t, y i :=
          sum_congr rfl fun t ht => by
            have : t.card = 2 := (mem_powersetCard.mp ht).2
            rw [this]
        rw [this, ← mul_sum]
      rw [hcard, hpair, mul_assoc]
    · have : R2 = (∅ : Finset ℕ) := by
        ext n; simp [R2, h, mem_inter, mem_singleton]
      rw [this, sum_empty]
      have hcardlt : s.card < 2 := by
        simp only [R, mem_range, not_lt] at h
        omega
      have hpc : s.powersetCard 2 = ∅ :=
        powersetCard_eq_empty.mpr hcardlt
      have hpair0 : ∑ t ∈ s.powersetCard 2, ∏ i ∈ t, y i = 0 := by
        simp [hpc]
      have hdiff0 : (∑ i ∈ s, y i) ^ 2 - ∑ i ∈ s, (y i) ^ 2 = 0 := by
        have htmp := hpair
        rw [hpair0] at htmp
        have hmul := congrArg (fun z => (2 : ZMod (p ^ 5)) * z) htmp.symm
        dsimp at hmul
        rw [← mul_assoc, ZMod.mul_inv_of_unit _ h2u, one_mul, mul_zero] at hmul
        exact hmul
      rw [hdiff0, mul_zero]
  refine ⟨∑ n ∈ R3, (p : ZMod (p ^ 5)) ^ (n - 3) *
      ∑ t ∈ s.powersetCard n, ∏ i ∈ t, y i, ?_⟩
  have hrest :
      ∑ n ∈ R3, ∑ t ∈ s.powersetCard n,
          (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
        (p : ZMod (p ^ 5)) ^ 3 *
          ∑ n ∈ R3, (p : ZMod (p ^ 5)) ^ (n - 3) *
            ∑ t ∈ s.powersetCard n, ∏ i ∈ t, y i := by
    rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn3 : 3 ≤ n := (mem_filter.mp hn).2
    have hinner :
        ∑ t ∈ s.powersetCard n,
            (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
          (p : ZMod (p ^ 5)) ^ n * ∑ t ∈ s.powersetCard n, ∏ i ∈ t, y i := by
      have : ∑ t ∈ s.powersetCard n,
          (p : ZMod (p ^ 5)) ^ t.card * ∏ i ∈ t, y i =
        ∑ t ∈ s.powersetCard n,
          (p : ZMod (p ^ 5)) ^ n * ∏ i ∈ t, y i :=
        sum_congr rfl fun t ht => by
          have : t.card = n := (mem_powersetCard.mp ht).2
          rw [this]
      rw [this, ← mul_sum]
    rw [hinner]
    have hpow : (p : ZMod (p ^ 5)) ^ n =
        (p : ZMod (p ^ 5)) ^ 3 * (p : ZMod (p ^ 5)) ^ (n - 3) := by
      rw [← pow_add, Nat.add_sub_cancel' hn3]
    rw [hpow]
    ring
  rw [h0, h1, h2sum, hrest]

/-- The local coefficient `y_i = -3/i + 2p/i²`. -/
def yQuad (p i : ℕ) [NeZero (p ^ 5)] : ZMod (p ^ 5) :=
  -(3 : ZMod (p ^ 5)) * (i : ZMod (p ^ 5))⁻¹ +
    (2 : ZMod (p ^ 5)) * p * ((i : ZMod (p ^ 5))⁻¹) ^ 2

lemma quad_eq_one_add_p_y {p i : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] :
    (1 : ZMod (p ^ 5)) - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
      (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2 =
      1 + (p : ZMod (p ^ 5)) * yQuad p i := by
  unfold yQuad; ring

lemma sum_yQuad {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ∑ i ∈ Icc 1 (k - 1), yQuad p i =
      -(3 : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1) +
        (2 : ZMod (p ^ 5)) * p * harmZ p 5 2 (k - 1) := by
  unfold yQuad harmZ
  simp only [sum_add_distrib, ← mul_sum, pow_one]

lemma prod_quad_expand {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] (hp : 7 ≤ p)
    (hk : k ∈ Icc 1 (p - 1)) :
    ∃ e : ZMod (p ^ 5),
      ∏ i ∈ Icc 1 (k - 1),
          (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
            (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2) =
        1 + (p : ZMod (p ^ 5)) * ∑ i ∈ Icc 1 (k - 1), yQuad p i +
          (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
            ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
              ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) +
          (p : ZMod (p ^ 5)) ^ 3 * e := by
  have hcongr : ∏ i ∈ Icc 1 (k - 1),
      (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
        (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2) =
      ∏ i ∈ Icc 1 (k - 1), (1 + (p : ZMod (p ^ 5)) * yQuad p i) :=
    prod_congr rfl fun i _ => quad_eq_one_add_p_y
  rw [hcongr]
  exact prod_one_add_p_y hp (Icc 1 (k - 1)) (fun i => yQuad p i)

/-- `y_i² ≡ 9 i⁻²` modulo `p`. -/
lemma yQuad_sq_mod_p {p i : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero p]
    (hi : i ∈ Icc 1 (p - 1)) :
    ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      ((yQuad p i) ^ 2) =
      (3 : ZMod p) ^ 2 * ((i : ZMod p)⁻¹) ^ 2 := by
  have hu : IsUnit (i : ZMod (p ^ 5)) := isUnit_of_mem_Icc hi
  have hp0 : ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      (p : ZMod (p ^ 5)) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_prime_self_pow (by norm_num : 0 < 5))]
    exact CharP.cast_eq_zero (ZMod p) p
  have h2p : ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      ((2 : ZMod (p ^ 5)) * p) = 0 := by
    rw [map_mul, map_ofNat, hp0, mul_zero]
  unfold yQuad
  rw [map_pow, map_add, map_mul, map_neg, map_ofNat,
    castHom_inv (dvd_prime_self_pow (by norm_num : 0 < 5)) hu]
  rw [map_mul, h2p, zero_mul, add_zero]
  ring

/-- Auxiliary: product of the two cubic expansions, before multiplying by `k⁻²`. -/
lemma frac_mul_prod_mod_p3 {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] (hp : 7 ≤ p)
    (hk : k ∈ Icc 1 (p - 1)) :
    ∃ e : ZMod (p ^ 5),
      ((1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
          (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹) *
        ∏ i ∈ Icc 1 (k - 1),
          (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
            (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2) =
      1 + (p : ZMod (p ^ 5)) *
          (∑ i ∈ Icc 1 (k - 1), yQuad p i -
            (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) +
        (p : ZMod (p ^ 5)) ^ 2 *
          ((2 : ZMod (p ^ 5))⁻¹ *
              ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
                ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
            (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
              (k : ZMod (p ^ 5))⁻¹ +
            (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) +
        (p : ZMod (p ^ 5)) ^ 3 * e := by
  obtain ⟨efrac, hfrac⟩ := frac_pm_mod_p3 hk
  obtain ⟨eprod, hprod⟩ := prod_quad_expand hp hk
  set Y : ZMod (p ^ 5) := ∑ i ∈ Icc 1 (k - 1), yQuad p i
  set Z : ZMod (p ^ 5) :=
    (2 : ZMod (p ^ 5))⁻¹ * (Y ^ 2 - ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2)
  set invk : ZMod (p ^ 5) := (k : ZMod (p ^ 5))⁻¹
  have hprod' :
      ∏ i ∈ Icc 1 (k - 1),
          (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
            (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2) =
        1 + (p : ZMod (p ^ 5)) * Y + (p : ZMod (p ^ 5)) ^ 2 * Z +
          (p : ZMod (p ^ 5)) ^ 3 * eprod := by
    convert hprod using 1
    unfold Y Z
    ring
  -- Explicit cubic remainder after multiplying the two expansions.
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := p_pow_five_eq_zero p
  refine ⟨(2 : ZMod (p ^ 5)) * Y * invk ^ 2 -
      (2 : ZMod (p ^ 5)) * Z * invk + efrac + eprod +
      (p : ZMod (p ^ 5)) * (Y * efrac + (2 : ZMod (p ^ 5)) * Z * invk ^ 2 -
        (2 : ZMod (p ^ 5)) * eprod * invk) +
      (p : ZMod (p ^ 5)) ^ 2 * (Z * efrac + (2 : ZMod (p ^ 5)) * eprod * invk ^ 2), ?_⟩
  rw [hfrac, hprod']
  have hp6 : (p : ZMod (p ^ 5)) ^ 6 = 0 :=
    nat_cast_p_pow_eq_zero_of_le (by norm_num : 5 ≤ 6)
  ring_nf
  simp [hp5, hp6, Y, Z, invk]

/-- Single-summand expansion of `W` modulo `p³`, before expanding `Y`. -/
lemma W_summand_mod_p3 {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] (hp : 7 ≤ p)
    (hk : k ∈ Icc 1 (p - 1)) :
    ∃ e : ZMod (p ^ 5),
      ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
        ((1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
          (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹) *
        ∏ i ∈ Icc 1 (k - 1),
          (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
            (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2) =
      ((k : ZMod (p ^ 5))⁻¹) ^ 2 +
        (p : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
          (∑ i ∈ Icc 1 (k - 1), yQuad p i -
            (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) +
        (p : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
          ((2 : ZMod (p ^ 5))⁻¹ *
              ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
                ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
            (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
              (k : ZMod (p ^ 5))⁻¹ +
            (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) +
        (p : ZMod (p ^ 5)) ^ 3 * e := by
  obtain ⟨emul, hmul⟩ := frac_mul_prod_mod_p3 hp hk
  refine ⟨((k : ZMod (p ^ 5))⁻¹) ^ 2 * emul, ?_⟩
  have hassoc :
      ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
          ((1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
            (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹) *
          ∏ i ∈ Icc 1 (k - 1),
            (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
              (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2) =
        ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
          (((1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
              (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹) *
            ∏ i ∈ Icc 1 (k - 1),
              (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
                (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2)) := by
    ring
  rw [hassoc, hmul]
  ring

/-- Summation of `W_summand_mod_p3`. -/
lemma Wz_expand_mod_p3 {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] (hp : 7 ≤ p) :
    ∃ e : ZMod (p ^ 5),
      Wz p 5 =
        harmZ p 5 2 (p - 1) +
          (p : ZMod (p ^ 5)) *
            ∑ k ∈ Icc 1 (p - 1),
              ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
                (∑ i ∈ Icc 1 (k - 1), yQuad p i -
                  (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) +
          (p : ZMod (p ^ 5)) ^ 2 *
            ∑ k ∈ Icc 1 (p - 1),
              ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
                ((2 : ZMod (p ^ 5))⁻¹ *
                    ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
                      ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
                  (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
                    (k : ZMod (p ^ 5))⁻¹ +
                  (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) +
          (p : ZMod (p ^ 5)) ^ 3 * e := by
  have hforall : ∀ k ∈ Icc 1 (p - 1), ∃ e : ZMod (p ^ 5),
      ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
          ((1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
            (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹) *
          ∏ i ∈ Icc 1 (k - 1),
            (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
              (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2) =
        ((k : ZMod (p ^ 5))⁻¹) ^ 2 +
          (p : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            (∑ i ∈ Icc 1 (k - 1), yQuad p i -
              (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) +
          (p : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            ((2 : ZMod (p ^ 5))⁻¹ *
                ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
                  ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
              (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
                (k : ZMod (p ^ 5))⁻¹ +
              (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) +
          (p : ZMod (p ^ 5)) ^ 3 * e :=
    fun k hk => W_summand_mod_p3 hp hk
  let e : ℕ → ZMod (p ^ 5) := fun k =>
    if hk : k ∈ Icc 1 (p - 1) then Classical.choose (hforall k hk) else 0
  have he : ∀ k ∈ Icc 1 (p - 1),
      ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
          ((1 - (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) *
            (1 + (p : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)⁻¹) *
          ∏ i ∈ Icc 1 (k - 1),
            (1 - (3 : ZMod (p ^ 5)) * p * (i : ZMod (p ^ 5))⁻¹ +
              (2 : ZMod (p ^ 5)) * p ^ 2 * ((i : ZMod (p ^ 5))⁻¹) ^ 2) =
        ((k : ZMod (p ^ 5))⁻¹) ^ 2 +
          (p : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            (∑ i ∈ Icc 1 (k - 1), yQuad p i -
              (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) +
          (p : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            ((2 : ZMod (p ^ 5))⁻¹ *
                ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
                  ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
              (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
                (k : ZMod (p ^ 5))⁻¹ +
              (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) +
          (p : ZMod (p ^ 5)) ^ 3 * e k := by
    intro k hk
    have hek : e k = Classical.choose (hforall k hk) := dif_pos hk
    rw [hek]
    exact Classical.choose_spec (hforall k hk)
  refine ⟨∑ k ∈ Icc 1 (p - 1), e k, ?_⟩
  unfold Wz harmZ
  rw [sum_congr rfl he, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  have hp1 :
      ∑ k ∈ Icc 1 (p - 1),
          (p : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            (∑ i ∈ Icc 1 (k - 1), yQuad p i -
              (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) =
        (p : ZMod (p ^ 5)) *
          ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
              (∑ i ∈ Icc 1 (k - 1), yQuad p i -
                (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) := by
    simp only [mul_assoc]
    rw [mul_sum]
  have hp2 :
      ∑ k ∈ Icc 1 (p - 1),
          (p : ZMod (p ^ 5)) ^ 2 * ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            ((2 : ZMod (p ^ 5))⁻¹ *
                ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
                  ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
              (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
                (k : ZMod (p ^ 5))⁻¹ +
              (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) =
        (p : ZMod (p ^ 5)) ^ 2 *
          ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
              ((2 : ZMod (p ^ 5))⁻¹ *
                  ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
                    ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
                (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
                  (k : ZMod (p ^ 5))⁻¹ +
                (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) := by
    simp only [mul_assoc]
    rw [mul_sum]
  have hp3 :
      ∑ k ∈ Icc 1 (p - 1), (p : ZMod (p ^ 5)) ^ 3 * e k =
        (p : ZMod (p ^ 5)) ^ 3 * ∑ k ∈ Icc 1 (p - 1), e k :=
    (mul_sum _ _ _).symm
  rw [hp1, hp2, hp3]

/-- The linear `yQuad` contribution to `W`. -/
lemma sum_invsq_yQuad {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] :
    ∑ k ∈ Icc 1 (p - 1),
        ((k : ZMod (p ^ 5))⁻¹) ^ 2 * ∑ i ∈ Icc 1 (k - 1), yQuad p i =
      -(3 : ZMod (p ^ 5)) * SZ p 5 +
        (2 : ZMod (p ^ 5)) * p *
          ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 * harmZ p 5 2 (k - 1) := by
  have hcongr :
      ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 5))⁻¹) ^ 2 * ∑ i ∈ Icc 1 (k - 1), yQuad p i =
        ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            (-(3 : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1) +
              (2 : ZMod (p ^ 5)) * p * harmZ p 5 2 (k - 1)) := by
    refine sum_congr rfl fun k hk => ?_
    rw [sum_yQuad hk]
  rw [hcongr]
  simp only [mul_add, sum_add_distrib]
  have h1 :
      ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 5))⁻¹) ^ 2 * (-(3 : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1)) =
        -(3 : ZMod (p ^ 5)) * SZ p 5 := by
    unfold SZ
    have hneg :
        ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 * (-(3 : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1)) =
          -∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 * ((3 : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1)) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [hneg]
    have hmul :
        ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 * ((3 : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1)) =
          (3 : ZMod (p ^ 5)) *
            ∑ k ∈ Icc 1 (p - 1),
              harmZ p 5 1 (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 := by
      refine Eq.trans (sum_congr rfl fun k _ => ?_) (mul_sum _ _ _).symm
      ring
    rw [hmul]
    ring
  have h2 :
      ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            ((2 : ZMod (p ^ 5)) * p * harmZ p 5 2 (k - 1)) =
        (2 : ZMod (p ^ 5)) * p *
          ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 * harmZ p 5 2 (k - 1) := by
    simp only [← mul_assoc, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [h1, h2]

lemma harmonic_num_mod_p2 {p : ℕ} [Fact p.Prime] [NeZero (p ^ 2)] [NeZero p]
    (hp : 7 ≤ p) :
    ((harmonic (p - 1)).num : ZMod (p ^ 2)) = 0 := by
  have hden : IsUnit ((harmonic (p - 1)).den : ZMod (p ^ 2)) :=
    den_harmonic_prefix_unit (hn := by omega)
  have h0 : ratZMod (p ^ 2) (harmonic (p - 1)) = 0 := by
    rw [ratZMod_harmonic (hn := by omega)]
    exact (harmZ_odd_mod_p2 hp).1
  have := ratZMod_mul_den (harmonic (p - 1)) hden
  rw [h0, zero_mul] at this
  exact this.symm

lemma wolstenholme_sum_ratZMod {p : ℕ} [Fact p.Prime] [NeZero (p ^ 4)] [NeZero p]
    (hp : 7 ≤ p) :
    ratZMod (p ^ 4)
      (harmonic (p - 1) + (p : ℚ) / 2 * harmonic₂ (p - 1)) = 0 := by
  have hdenH : IsUnit ((harmonic (p - 1)).den : ZMod (p ^ 4)) :=
    den_harmonic_prefix_unit (hn := by omega)
  have hdenH2 : IsUnit ((harmonic₂ (p - 1)).den : ZMod (p ^ 4)) :=
    den_harmonic₂_prefix_unit (hn := by omega)
  have h2u : IsUnit (2 : ZMod (p ^ 4)) := isUnit_two_zmod (by omega)
  have hH := ratZMod_harmonic (p := p) (r := 4) (n := p - 1) (by omega)
  have hH2 := ratZMod_harmonic₂ (p := p) (r := 4) (n := p - 1) (by omega)
  have hhalf : ratZMod (p ^ 4) ((p : ℚ) / 2) =
      (p : ZMod (p ^ 4)) * (2 : ZMod (p ^ 4))⁻¹ := by
    have : (p : ℚ) / 2 = ((p : ℤ) : ℚ) / (2 : ℕ) := by simp
    rw [this, ratZMod_eq_div (n := (p : ℤ)) (d := 2) (by norm_num) h2u]
    simp
  have hden_half : IsUnit ((((p : ℚ) / 2).den : ZMod (p ^ 4))) := by
    have : (p : ℚ) / 2 = ((p : ℤ) : ℚ) / (2 : ℕ) := by simp
    rw [this]
    exact isUnit_natCast_of_dvd
      (den_div_of_int_div_nat (a := (p : ℤ)) (d := 2) (by norm_num)) h2u
  have hden_prod : IsUnit ((((p : ℚ) / 2 * harmonic₂ (p - 1)).den : ZMod (p ^ 4))) :=
    den_isUnit_of_mul hden_half hdenH2
  rw [ratZMod_add hdenH hden_prod, ratZMod_mul hden_half hdenH2, hhalf, hH, hH2]
  have hw := harmZ_eq_neg_p_div_two_H2 (p := p) hp
  linear_combination hw

lemma wolstenholme_sum_den_unit {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    [NeZero p] (hp : 7 ≤ p) :
    IsUnit (((harmonic (p - 1) + (p : ℚ) / 2 * harmonic₂ (p - 1)).den : ZMod (p ^ r))) := by
  have hdenH : IsUnit ((harmonic (p - 1)).den : ZMod (p ^ r)) :=
    den_harmonic_prefix_unit (hn := by omega)
  have hdenH2 : IsUnit ((harmonic₂ (p - 1)).den : ZMod (p ^ r)) :=
    den_harmonic₂_prefix_unit (hn := by omega)
  have h2u : IsUnit (2 : ZMod (p ^ r)) := isUnit_two_zmod (by omega)
  have hden_half : IsUnit ((((p : ℚ) / 2).den : ZMod (p ^ r))) := by
    have : (p : ℚ) / 2 = ((p : ℤ) : ℚ) / (2 : ℕ) := by simp
    rw [this]
    exact isUnit_natCast_of_dvd
      (den_div_of_int_div_nat (a := (p : ℤ)) (d := 2) (by norm_num)) h2u
  exact den_isUnit_of_add hdenH (den_isUnit_of_mul hden_half hdenH2)

lemma wolstenholme_sum_num_mod_p4 {p : ℕ} [Fact p.Prime] [NeZero (p ^ 4)] [NeZero p]
    (hp : 7 ≤ p) :
    ((harmonic (p - 1) + (p : ℚ) / 2 * harmonic₂ (p - 1)).num : ZMod (p ^ 4)) = 0 := by
  have hden := wolstenholme_sum_den_unit (p := p) (r := 4) hp
  have h0 := wolstenholme_sum_ratZMod hp
  have := ratZMod_mul_den _ hden
  rw [h0, zero_mul] at this
  exact this.symm

lemma den_harmonic_div_p_unit {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    [NeZero (p ^ 2)] [NeZero p] (hp : 7 ≤ p) :
    IsUnit (((harmonic (p - 1) / (p : ℚ)).den : ZMod (p ^ r))) := by
  have hnum := harmonic_num_mod_p2 (p := p) hp
  have hdvd : (p ^ 2 : ℤ) ∣ (harmonic (p - 1)).num :=
    (CharP.intCast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2) _).mp hnum
  obtain ⟨m, hm⟩ := hdvd
  have hdenH : IsUnit ((harmonic (p - 1)).den : ZMod (p ^ r)) :=
    den_harmonic_prefix_unit (hn := by omega)
  have hform : harmonic (p - 1) / (p : ℚ) =
      ((p * m : ℤ) : ℚ) / (harmonic (p - 1)).den := by
    have hp0 : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hden0 : ((harmonic (p - 1)).den : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (harmonic (p - 1)).den_nz
    have hH := Rat.num_div_den (harmonic (p - 1))
    apply Eq.trans (congrArg (fun t : ℚ => t / (p : ℚ)) hH.symm)
    rw [hm]
    push_cast
    field_simp [hp0, hden0]
  have hdvd' : ((harmonic (p - 1) / (p : ℚ)).den) ∣ (harmonic (p - 1)).den := by
    have : harmonic (p - 1) / (p : ℚ) =
        ((p * m : ℤ) : ℚ) / ((harmonic (p - 1)).den : ℕ) := hform
    rw [this]
    exact den_div_of_int_div_nat (a := (p * m : ℤ)) (d := (harmonic (p - 1)).den)
      (harmonic (p - 1)).den_nz
  exact isUnit_natCast_of_dvd hdvd' hdenH

lemma ratZMod_castHom {p r s : ℕ} [Fact p.Prime] [NeZero (p ^ r)] [NeZero (p ^ s)]
    (hr : 0 < r) (hsr : s ≤ r) {a : ℚ} (ha : IsUnit (a.den : ZMod (p ^ r))) :
    ZMod.castHom (pow_dvd_pow p hsr) (ZMod (p ^ s)) (ratZMod (p ^ r) a) =
      ratZMod (p ^ s) a := by
  have ha' : IsUnit (a.den : ZMod (p ^ s)) := by
    rw [ZMod.isUnit_iff_coprime] at ha ⊢
    have hcop : a.den.Coprime p := (Nat.coprime_pow_right_iff hr a.den p).mp ha
    exact hcop.pow_right s
  unfold ratZMod
  rw [map_mul, map_intCast]
  have hinv : ZMod.castHom (pow_dvd_pow p hsr) (ZMod (p ^ s)) (a.den : ZMod (p ^ r))⁻¹ =
      (a.den : ZMod (p ^ s))⁻¹ :=
    castHom_inv (pow_dvd_pow p hsr) ha
  rw [hinv]

lemma den_wolstenholme_div_p_unit {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    [NeZero (p ^ 4)] [NeZero p] (hp : 7 ≤ p) :
    IsUnit ((((harmonic (p - 1) + (p : ℚ) / 2 * harmonic₂ (p - 1)) / (p : ℚ)).den :
      ZMod (p ^ r))) := by
  set a : ℚ := harmonic (p - 1) + (p : ℚ) / 2 * harmonic₂ (p - 1)
  have hnum : (a.num : ZMod (p ^ 4)) = 0 := wolstenholme_sum_num_mod_p4 hp
  have hdvd : (p ^ 4 : ℤ) ∣ a.num :=
    (CharP.intCast_eq_zero_iff (ZMod (p ^ 4)) (p ^ 4) _).mp hnum
  obtain ⟨m, hm⟩ := hdvd
  have hdena : IsUnit (a.den : ZMod (p ^ r)) := wolstenholme_sum_den_unit hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hden0 : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hH := Rat.num_div_den a
  have hform : a / (p : ℚ) = ((p ^ 3 * m : ℤ) : ℚ) / a.den := by
    apply Eq.trans (congrArg (fun t : ℚ => t / (p : ℚ)) hH.symm)
    rw [hm]
    push_cast
    field_simp [hp0, hden0]
  have hdvd' : (a / (p : ℚ)).den ∣ a.den := by
    have : a / (p : ℚ) = ((p ^ 3 * m : ℤ) : ℚ) / (a.den : ℕ) := hform
    rw [this]
    exact den_div_of_int_div_nat (a := (p ^ 3 * m : ℤ)) (d := a.den) a.den_nz
  exact isUnit_natCast_of_dvd hdvd' hdena

lemma ratZMod_harmonic_div_p_add_half_H2 {p : ℕ}
    [Fact p.Prime] [NeZero (p ^ 5)] [NeZero (p ^ 4)] [NeZero (p ^ 3)] [NeZero p]
    (hp : 7 ≤ p) :
    ∃ e : ZMod (p ^ 5),
      ratZMod (p ^ 5) (harmonic (p - 1) / (p : ℚ)) +
          (2 : ZMod (p ^ 5))⁻¹ * harmZ p 5 2 (p - 1) =
        (p : ZMod (p ^ 5)) ^ 3 * e := by
  set a : ℚ := harmonic (p - 1) + (p : ℚ) / 2 * harmonic₂ (p - 1)
  have hden_div := den_wolstenholme_div_p_unit (p := p) (r := 5) hp
  have hden_div3 := den_wolstenholme_div_p_unit (p := p) (r := 3) hp
  have hnum := wolstenholme_sum_num_mod_p4 hp
  have hdvd : (p ^ 4 : ℤ) ∣ a.num :=
    (CharP.intCast_eq_zero_iff (ZMod (p ^ 4)) (p ^ 4) _).mp hnum
  obtain ⟨m, hm⟩ := hdvd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hden0 : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hH := Rat.num_div_den a
  have hform : a / (p : ℚ) = ((p ^ 3 * m : ℤ) : ℚ) / a.den := by
    apply Eq.trans (congrArg (fun t : ℚ => t / (p : ℚ)) hH.symm)
    rw [hm]; push_cast; field_simp [hp0, hden0]
  have hcast0 : ratZMod (p ^ 3) (a / (p : ℚ)) = 0 := by
    have hdena3 : IsUnit (a.den : ZMod (p ^ 3)) := wolstenholme_sum_den_unit hp
    have : a / (p : ℚ) = ((p ^ 3 * m : ℤ) : ℚ) / (a.den : ℕ) := hform
    rw [this, ratZMod_eq_div (n := (p ^ 3 * m : ℤ)) (d := a.den) a.den_nz hdena3]
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    have hp3 : ((p : ZMod (p ^ 3)) ^ 3) = 0 := by
      rw [← Nat.cast_pow]; exact CharP.cast_eq_zero _ _
    rw [hp3]
    simp
  have hcast5 :
      ZMod.castHom (pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3))
        (ratZMod (p ^ 5) (a / (p : ℚ))) = 0 := by
    rw [ratZMod_castHom (by norm_num : 0 < 5) (by norm_num : 3 ≤ 5) hden_div, hcast0]
  obtain ⟨e, he⟩ :=
    eq_mul_pow_of_cast_eq_zero (pow_dvd_pow p (by norm_num : 3 ≤ 5)) hcast5
  -- a/p = H/p + H2/2
  have hsplit : a / (p : ℚ) =
      harmonic (p - 1) / (p : ℚ) + harmonic₂ (p - 1) / 2 := by
    unfold a
    have hp0' : (p : ℚ) ≠ 0 := hp0
    field_simp [hp0']
  have hdenH := den_harmonic_div_p_unit (p := p) (r := 5) hp
  have h2u : IsUnit (2 : ZMod (p ^ 5)) := isUnit_two_zmod (by omega)
  have hdenH2 : IsUnit ((harmonic₂ (p - 1)).den : ZMod (p ^ 5)) :=
    den_harmonic₂_prefix_unit (hn := by omega)
  have hden2 : IsUnit (((2 : ℚ).den : ZMod (p ^ 5))) := by simp
  have hnum2 : IsUnit (((2 : ℚ).num : ZMod (p ^ 5))) := by
    change IsUnit ((2 : ℤ) : ZMod (p ^ 5)); simpa using h2u
  have hdenH2d2 : IsUnit (((harmonic₂ (p - 1) / 2).den : ZMod (p ^ 5))) := by
    have : harmonic₂ (p - 1) / 2 = harmonic₂ (p - 1) * (2 : ℚ)⁻¹ :=
      div_eq_mul_inv _ _
    rw [this]
    refine den_isUnit_of_mul hdenH2 ?_
    have h2n : (2 : ℚ) ≠ 0 := by norm_num
    rw [Rat.den_inv_of_ne_zero h2n]
    simpa [show (2 : ℚ).num = 2 from rfl] using
      (isUnit_natAbs_iff (2 : ℤ)).mpr (by simpa using h2u)
  have himg := ratZMod_add (q := p ^ 5) hdenH hdenH2d2
  have hH2img : ratZMod (p ^ 5) (harmonic₂ (p - 1) / 2) =
      (2 : ZMod (p ^ 5))⁻¹ * harmZ p 5 2 (p - 1) := by
    have h2n : (2 : ℚ) ≠ 0 := by norm_num
    rw [ratZMod_div h2n hdenH2 hden2 hnum2, ratZMod_harmonic₂ (hn := by omega)]
    have : ratZMod (p ^ 5) (2 : ℚ) = (2 : ZMod (p ^ 5)) := ratZMod_nat (p ^ 5) 2
    rw [this]
    ring
  refine ⟨e, ?_⟩
  have : ratZMod (p ^ 5) (a / (p : ℚ)) = (p : ZMod (p ^ 5)) ^ 3 * e := by
    rw [← Nat.cast_pow]; exact he
  rw [hsplit, himg, hH2img] at this
  exact this

lemma den_one_sub_p_div_unit {p r i : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hi : i ∈ Icc 1 (p - 1)) :
    IsUnit ((((1 : ℚ) - (p : ℚ) / i).den : ZMod (p ^ r))) := by
  have hi0n : i ≠ 0 := (mem_Icc_lt_prime (p := p) hi).1.ne'
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast hi0n
  have hL : (1 : ℚ) - (p : ℚ) / i = ((i : ℚ) - (p : ℚ)) / (i : ℚ) := by
    field_simp [hi0]
  have hR : ((i : ℚ) - (p : ℚ)) / (i : ℚ) =
      ((((i : ℤ) - (p : ℤ) : ℤ) : ℚ) / (i : ℕ)) := by
    rw [← Int.cast_natCast i, ← Int.cast_natCast p, ← Int.cast_sub]
  rw [hL, hR]
  exact isUnit_natCast_of_dvd
    (den_div_of_int_div_nat (a := (i : ℤ) - (p : ℤ)) (d := i) hi0n)
    (isUnit_of_mem_Icc hi)

lemma ratZMod_one_sub_p_div {p r i : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hi : i ∈ Icc 1 (p - 1)) :
    ratZMod (p ^ r) ((1 : ℚ) - (p : ℚ) / i) =
      (1 : ZMod (p ^ r)) - (p : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹ := by
  have hi0n : i ≠ 0 := (mem_Icc_lt_prime (p := p) hi).1.ne'
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast hi0n
  have hden1 : IsUnit (((1 : ℚ).den : ZMod (p ^ r))) := by simp
  have hden_pi : IsUnit ((((p : ℚ) / i).den : ZMod (p ^ r))) := by
    have : (p : ℚ) / i = ((p : ℤ) : ℚ) / i := by simp
    rw [this]
    exact isUnit_natCast_of_dvd
      (den_div_of_int_div_nat (a := (p : ℤ)) (d := i) hi0n)
      (isUnit_of_mem_Icc hi)
  have hdeni : IsUnit (((i : ℚ).den : ZMod (p ^ r))) := by simp [Rat.den_natCast]
  have hnumi : IsUnit (((i : ℚ).num : ZMod (p ^ r))) := by
    simpa [Rat.num_natCast] using isUnit_of_mem_Icc (p := p) (r := r) hi
  rw [ratZMod_sub hden1 hden_pi, ratZMod_one]
  have : (p : ℚ) / i = ((p : ℤ) : ℚ) / (i : ℕ) := by simp
  rw [this, ratZMod_eq_div (n := (p : ℤ)) (d := i) hi0n (isUnit_of_mem_Icc hi)]
  simp

lemma ratZMod_prod_one_sub_p {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    ratZMod (p ^ r) (∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) =
      ∏ i ∈ Icc 1 (k - 1),
        ((1 : ZMod (p ^ r)) - (p : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) := by
  refine (ratZMod_prod (Icc 1 (k - 1)) (fun i => (1 : ℚ) - (p : ℚ) / i) ?_).trans ?_
  · intro i hi
    have : i ∈ Icc 1 (p - 1) := by
      have := mem_Icc.mp hi; have := mem_Icc.mp hk
      simp only [mem_Icc]; omega
    exact den_one_sub_p_div_unit this
  · refine prod_congr rfl fun i hi => ?_
    have : i ∈ Icc 1 (p - 1) := by
      have := mem_Icc.mp hi; have := mem_Icc.mp hk
      simp only [mem_Icc]; omega
    exact ratZMod_one_sub_p_div this

lemma den_prod_one_sub_p_div_k2_unit {p r k : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hk : k ∈ Icc 1 (p - 1)) :
    IsUnit ((((∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) / (k : ℚ) ^ 2).den :
      ZMod (p ^ r))) := by
  have hP : IsUnit (((∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)).den : ZMod (p ^ r))) := by
    refine den_isUnit_prod _ _ ?_
    intro i hi
    have : i ∈ Icc 1 (p - 1) := by
      have := mem_Icc.mp hi; have := mem_Icc.mp hk
      simp only [mem_Icc]; omega
    exact den_one_sub_p_div_unit this
  have : (∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) / (k : ℚ) ^ 2 =
      (∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) * (1 / (k : ℚ) ^ 2) := by
    field_simp
  rw [this]
  exact den_isUnit_of_mul hP (den_inv_sq_unit hk)

lemma ratZMod_sum_prod_one_sub_p_div_k2 {p r : ℕ} [Fact p.Prime] [NeZero (p ^ r)]
    (hp : 7 ≤ p) :
    ratZMod (p ^ r)
      (∑ k ∈ Icc 1 (p - 1),
        ((∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) / (k : ℚ) ^ 2)) =
    ∑ k ∈ Icc 1 (p - 1),
      (∏ i ∈ Icc 1 (k - 1),
        ((1 : ZMod (p ^ r)) - (p : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹)) *
        ((k : ZMod (p ^ r))⁻¹) ^ 2 := by
  have hu : ∀ k ∈ Icc 1 (p - 1),
      IsUnit ((((∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) / (k : ℚ) ^ 2).den :
        ZMod (p ^ r))) :=
    fun k hk => den_prod_one_sub_p_div_k2_unit hk
  rw [ratZMod_sum _ _ hu]
  refine sum_congr rfl fun k hk => ?_
  have hP : IsUnit (((∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)).den : ZMod (p ^ r))) :=
    den_isUnit_prod (Icc 1 (k - 1)) (fun i => (1 : ℚ) - (p : ℚ) / i)
      (fun i hi => by
        have himem : i ∈ Icc 1 (p - 1) := by
          have := mem_Icc.mp hi; have := mem_Icc.mp hk
          simp only [mem_Icc]; omega
        exact den_one_sub_p_div_unit himem)
  have : (∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) / (k : ℚ) ^ 2 =
      (∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) * (1 / (k : ℚ) ^ 2) := by
    field_simp
  rw [this, ratZMod_mul hP (den_inv_sq_unit hk), ratZMod_prod_one_sub_p hk,
    ratZMod_inv_sq hk]

lemma mem_Icc_of_prefix {p k j : ℕ} [Fact p.Prime]
    (hk : k ∈ Icc 1 (p - 1)) (hj : j ∈ Icc 1 (k - 1)) :
    j ∈ Icc 1 (p - 1) := by
  have := mem_Icc.mp hj
  have := mem_Icc.mp hk
  simp only [mem_Icc]
  omega

lemma castHom_inv_pow_five {p k n : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      (((k : ZMod (p ^ 5))⁻¹) ^ n) = ((k : ZMod p)⁻¹) ^ n := by
  have hu : IsUnit (k : ZMod (p ^ 5)) := isUnit_of_mem_Icc hk
  rw [map_pow, castHom_inv (dvd_prime_self_pow (by norm_num : 0 < 5)) hu]

lemma castHom_harmZ_prefix {p k m : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero p]
    (hk : k ∈ Icc 1 (p - 1)) :
    ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      (harmZ p 5 m (k - 1)) =
    ∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ m := by
  unfold harmZ
  rw [map_sum]
  refine sum_congr rfl fun j hj => ?_
  exact castHom_inv_pow_five (mem_Icc_of_prefix hk hj)

lemma castHom_yQuad {p i : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero p]
    (hi : i ∈ Icc 1 (p - 1)) :
    ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p) (yQuad p i) =
      -(3 : ZMod p) * (i : ZMod p)⁻¹ := by
  have hu : IsUnit (i : ZMod (p ^ 5)) := isUnit_of_mem_Icc hi
  have hp0 : ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      (p : ZMod (p ^ 5)) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_prime_self_pow (by norm_num : 0 < 5))]
    exact CharP.cast_eq_zero (ZMod p) p
  have h2p : ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      ((2 : ZMod (p ^ 5)) * p) = 0 := by
    rw [map_mul, map_ofNat, hp0, mul_zero]
  unfold yQuad
  rw [map_add, map_mul, map_neg, map_ofNat,
    castHom_inv (dvd_prime_self_pow (by norm_num : 0 < 5)) hu]
  rw [map_mul, h2p, zero_mul, add_zero]

lemma castHom_unit_inv {a b : ℕ} [NeZero a] [NeZero b] (hba : b ∣ a)
    {x : ZMod a} (hu : IsUnit x) :
    ZMod.castHom hba (ZMod b) x⁻¹ = (ZMod.castHom hba (ZMod b) x)⁻¹ := by
  refine (ZMod.inv_eq_of_mul_eq_one b _ _ ?_).symm
  rw [← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]

lemma prod_one_sub_p_expand {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] (hp : 7 ≤ p)
    (hk : k ∈ Icc 1 (p - 1)) :
    ∃ e : ZMod (p ^ 5),
      ∏ i ∈ Icc 1 (k - 1),
          (1 - (p : ZMod (p ^ 5)) * (i : ZMod (p ^ 5))⁻¹) =
        1 - (p : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1) +
          (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
            ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) +
          (p : ZMod (p ^ 5)) ^ 3 * e := by
  have ⟨e, he⟩ := prod_one_add_p_y (p := p) hp (Icc 1 (k - 1))
    (fun i => -((i : ZMod (p ^ 5))⁻¹))
  refine ⟨e, ?_⟩
  have hcong : ∏ i ∈ Icc 1 (k - 1),
      (1 - (p : ZMod (p ^ 5)) * (i : ZMod (p ^ 5))⁻¹) =
      ∏ i ∈ Icc 1 (k - 1),
        (1 + (p : ZMod (p ^ 5)) * (-((i : ZMod (p ^ 5))⁻¹))) :=
    prod_congr rfl fun i _ => by ring
  rw [hcong, he]
  have hy : ∑ i ∈ Icc 1 (k - 1), -((i : ZMod (p ^ 5))⁻¹) =
      -harmZ p 5 1 (k - 1) := by
    unfold harmZ; simp [pow_one, ← sum_neg_distrib]
  have hy2 : ∑ i ∈ Icc 1 (k - 1), (-((i : ZMod (p ^ 5))⁻¹)) ^ 2 =
      harmZ p 5 2 (k - 1) := by
    unfold harmZ
    refine sum_congr rfl fun i _ => by ring
  rw [hy, hy2]
  ring

lemma sum_prod_one_sub_p_expand {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] (hp : 7 ≤ p) :
    ∃ eQ : ZMod (p ^ 5),
      ∑ k ∈ Icc 1 (p - 1),
          (∏ i ∈ Icc 1 (k - 1),
            (1 - (p : ZMod (p ^ 5)) * (i : ZMod (p ^ 5))⁻¹)) *
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 =
        harmZ p 5 2 (p - 1) - (p : ZMod (p ^ 5)) * SZ p 5 +
          (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
            (∑ k ∈ Icc 1 (p - 1),
              ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) *
                ((k : ZMod (p ^ 5))⁻¹) ^ 2) +
          (p : ZMod (p ^ 5)) ^ 3 * eQ := by
  have hforall : ∀ k ∈ Icc 1 (p - 1), ∃ e : ZMod (p ^ 5),
      ∏ i ∈ Icc 1 (k - 1),
          (1 - (p : ZMod (p ^ 5)) * (i : ZMod (p ^ 5))⁻¹) =
        1 - (p : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1) +
          (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
            ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) +
          (p : ZMod (p ^ 5)) ^ 3 * e :=
    fun k hk => prod_one_sub_p_expand hp hk
  let e : ℕ → ZMod (p ^ 5) := fun k =>
    if hk : k ∈ Icc 1 (p - 1) then Classical.choose (hforall k hk) else 0
  have hek : ∀ k ∈ Icc 1 (p - 1),
      ∏ i ∈ Icc 1 (k - 1),
          (1 - (p : ZMod (p ^ 5)) * (i : ZMod (p ^ 5))⁻¹) =
        1 - (p : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1) +
          (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
            ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) +
          (p : ZMod (p ^ 5)) ^ 3 * e k := by
    intro k hk
    have : e k = Classical.choose (hforall k hk) := dif_pos hk
    rw [this]
    exact Classical.choose_spec (hforall k hk)
  refine ⟨∑ k ∈ Icc 1 (p - 1), e k * ((k : ZMod (p ^ 5))⁻¹) ^ 2, ?_⟩
  have hsum := sum_congr (s₁ := Icc 1 (p - 1)) rfl fun k hk =>
    congrArg (fun t => t * ((k : ZMod (p ^ 5))⁻¹) ^ 2) (hek k hk)
  rw [hsum]
  simp only [add_mul, sub_mul]
  rw [sum_add_distrib, sum_add_distrib, sum_sub_distrib]
  have h1 : ∑ k ∈ Icc 1 (p - 1), (1 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 =
      harmZ p 5 2 (p - 1) := by
    unfold harmZ
    simp only [one_mul]
  have hp1 :
      ∑ k ∈ Icc 1 (p - 1),
          (p : ZMod (p ^ 5)) * harmZ p 5 1 (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 =
        (p : ZMod (p ^ 5)) * SZ p 5 := by
    unfold SZ
    refine Eq.trans (sum_congr rfl fun k _ => ?_) (mul_sum _ _ _).symm
    ring
  have hp2 :
      ∑ k ∈ Icc 1 (p - 1),
          ((p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
            ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1))) *
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 =
        (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
          ∑ k ∈ Icc 1 (p - 1),
            ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) *
              ((k : ZMod (p ^ 5))⁻¹) ^ 2 := by
    refine Eq.trans (sum_congr rfl fun k _ => ?_) (mul_sum _ _ _).symm
    ring
  have hp3 :
      ∑ k ∈ Icc 1 (p - 1),
          ((p : ZMod (p ^ 5)) ^ 3 * e k) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 =
        (p : ZMod (p ^ 5)) ^ 3 *
          ∑ k ∈ Icc 1 (p - 1), e k * ((k : ZMod (p ^ 5))⁻¹) ^ 2 := by
    refine Eq.trans (sum_congr rfl fun k _ => ?_) (mul_sum _ _ _).symm
    ring
  rw [h1, hp1, hp2, hp3]
  refine congr_arg₂ (· + ·) ?_ rfl
  refine congr_arg₂ (· + ·) rfl ?_
  refine congr_arg
      (fun t => (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ * t) ?_
  refine sum_congr rfl fun _ _ => by ring

lemma mid_sum_cast_zero {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero p]
    (hp : 7 ≤ p) :
    ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      (∑ k ∈ Icc 1 (p - 1),
        ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) *
          ((k : ZMod (p ^ 5))⁻¹) ^ 2) = 0 := by
  rw [map_sum]
  have hterm : ∀ k ∈ Icc 1 (p - 1),
      ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
        (((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) *
          ((k : ZMod (p ^ 5))⁻¹) ^ 2) =
      ((∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 -
        ∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) *
        ((k : ZMod p)⁻¹) ^ 2 := by
    intro k hk
    rw [map_mul, map_sub, map_pow, castHom_harmZ_prefix hk,
      castHom_harmZ_prefix hk, castHom_inv_pow_five hk]
    simp only [pow_one]
  rw [sum_congr rfl hterm]
  have hsplit :
      ∑ k ∈ Icc 1 (p - 1),
          ((∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 -
            ∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) *
            ((k : ZMod p)⁻¹) ^ 2 =
        ∑ k ∈ Icc 1 (p - 1),
            (∑ j ∈ Icc 1 (k - 1), (j : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 -
          ∑ k ∈ Icc 1 (p - 1),
            (∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 := by
    rw [sum_congr rfl (fun k _ => sub_mul _ _ _), sum_sub_distrib]
  rw [hsplit, sum_harm_sq_prefix_div_k2 hp, sum_harm2_prefix_div_k2 hp, sub_zero]

lemma harm2_prefix_div_k2_dvd_p {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero p]
    (hp : 7 ≤ p) :
    ∃ y : ZMod (p ^ 5),
      ∑ k ∈ Icc 1 (p - 1),
          harmZ p 5 2 (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 =
        (p : ZMod (p ^ 5)) * y := by
  have hcast :
      ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
        (∑ k ∈ Icc 1 (p - 1),
          harmZ p 5 2 (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) = 0 := by
    rw [map_sum]
    have hterm : ∀ k ∈ Icc 1 (p - 1),
        ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
          (harmZ p 5 2 (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) =
        (∑ j ∈ Icc 1 (k - 1), ((j : ZMod p)⁻¹) ^ 2) * ((k : ZMod p)⁻¹) ^ 2 := by
      intro k hk
      rw [map_mul, castHom_harmZ_prefix hk, castHom_inv_pow_five hk]
    rw [sum_congr rfl hterm, sum_harm2_prefix_div_k2 hp]
  exact eq_mul_pow_of_cast_eq_zero (dvd_prime_self_pow (by norm_num : 0 < 5)) hcast

lemma sum_invsq_L {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] :
    ∑ k ∈ Icc 1 (p - 1),
        ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
          (∑ i ∈ Icc 1 (k - 1), yQuad p i -
            (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) =
      -(3 : ZMod (p ^ 5)) * SZ p 5 +
        (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) *
          ∑ k ∈ Icc 1 (p - 1),
            harmZ p 5 2 (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 -
        (2 : ZMod (p ^ 5)) * harmZ p 5 3 (p - 1) := by
  have hsplit :
      ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            (∑ i ∈ Icc 1 (k - 1), yQuad p i -
              (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) =
        ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 * ∑ i ∈ Icc 1 (k - 1), yQuad p i -
          ∑ k ∈ Icc 1 (p - 1),
            ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
              ((2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k _ => by ring
  have h2k :
      ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
            ((2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹) =
        (2 : ZMod (p ^ 5)) * harmZ p 5 3 (p - 1) := by
    unfold harmZ
    refine Eq.trans (sum_congr rfl fun k _ => ?_) (mul_sum _ _ _).symm
    ring
  have hcomm :
      ∑ k ∈ Icc 1 (p - 1),
          ((k : ZMod (p ^ 5))⁻¹) ^ 2 * harmZ p 5 2 (k - 1) =
        ∑ k ∈ Icc 1 (p - 1),
          harmZ p 5 2 (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2 :=
    sum_congr rfl fun k _ => mul_comm _ _
  rw [hsplit, sum_invsq_yQuad, h2k, hcomm]

lemma three_H2_sub_two_p_SZ {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    [NeZero (p ^ 4)] [NeZero (p ^ 3)] [NeZero p] (hp : 7 ≤ p) :
    ∃ z : ZMod (p ^ 5),
      (3 : ZMod (p ^ 5)) * harmZ p 5 2 (p - 1) -
        (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * SZ p 5 =
      (p : ZMod (p ^ 5)) ^ 3 * z := by
  obtain ⟨eQ, hQ⟩ := sum_prod_one_sub_p_expand (p := p) hp
  have hsumQ := ratZMod_sum_prod_one_sub_p_div_k2 (p := p) (r := 5) hp
  have hQrat := sum_prod_one_sub_p_div_k2 p Fact.out (by omega)
  have himgHp : ratZMod (p ^ 5)
      (∑ k ∈ Icc 1 (p - 1),
        ((∏ i ∈ Icc 1 (k - 1), (1 - (p : ℚ) / i)) / (k : ℚ) ^ 2)) =
      ratZMod (p ^ 5) (harmonic (p - 1) / p) := by
    rw [hQrat]
  obtain ⟨eHp, hHp⟩ := ratZMod_harmonic_div_p_add_half_H2 (p := p) hp
  have h3 : ratZMod (p ^ 5) (harmonic (p - 1) / p) =
      - (2 : ZMod (p ^ 5))⁻¹ * harmZ p 5 2 (p - 1) +
        (p : ZMod (p ^ 5)) ^ 3 * eHp := by
    have := eq_sub_of_add_eq hHp
    convert this using 1
    ring
  have hrel :
      harmZ p 5 2 (p - 1) - (p : ZMod (p ^ 5)) * SZ p 5 +
        (p : ZMod (p ^ 5)) ^ 2 * (2 : ZMod (p ^ 5))⁻¹ *
          (∑ k ∈ Icc 1 (p - 1),
            ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) *
              ((k : ZMod (p ^ 5))⁻¹) ^ 2) +
        (p : ZMod (p ^ 5)) ^ 3 * eQ =
      - (2 : ZMod (p ^ 5))⁻¹ * harmZ p 5 2 (p - 1) +
        (p : ZMod (p ^ 5)) ^ 3 * eHp :=
    (hQ.symm.trans hsumQ.symm).trans (himgHp.trans h3)
  have hmid0 := mid_sum_cast_zero (p := p) hp
  obtain ⟨ymid, hmid⟩ :=
    eq_mul_pow_of_cast_eq_zero (dvd_prime_self_pow (by norm_num : 0 < 5)) hmid0
  have h2u : IsUnit (2 : ZMod (p ^ 5)) := isUnit_two_zmod (by omega)
  have h2inv : (2 : ZMod (p ^ 5)) * (2 : ZMod (p ^ 5))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ h2u
  rw [hmid] at hrel
  set H2 : ZMod (p ^ 5) := harmZ p 5 2 (p - 1)
  set pp : ZMod (p ^ 5) := (p : ZMod (p ^ 5))
  set mid : ZMod (p ^ 5) :=
    ∑ k ∈ Icc 1 (p - 1),
      ((harmZ p 5 1 (k - 1)) ^ 2 - harmZ p 5 2 (k - 1)) *
        ((k : ZMod (p ^ 5))⁻¹) ^ 2
  -- hrel : H2 - pp*SZ + pp^2 * 2⁻¹ * (pp * ymid) + pp^3 * eQ = -2⁻¹*H2 + pp^3*eHp
  have hmul := congrArg (fun t : ZMod (p ^ 5) => (2 : ZMod (p ^ 5)) * t) hrel
  refine ⟨(2 : ZMod (p ^ 5)) * eHp - (2 : ZMod (p ^ 5)) * eQ - ymid, ?_⟩
  have hrearr :
      (2 : ZMod (p ^ 5)) *
          (H2 - pp * SZ p 5 + pp ^ 2 * (2 : ZMod (p ^ 5))⁻¹ * (pp * ymid) +
            pp ^ 3 * eQ) =
        (2 : ZMod (p ^ 5)) * H2 - (2 : ZMod (p ^ 5)) * pp * SZ p 5 +
          pp ^ 3 * ymid + (2 : ZMod (p ^ 5)) * pp ^ 3 * eQ := by
    calc
      (2 : ZMod (p ^ 5)) *
          (H2 - pp * SZ p 5 + pp ^ 2 * (2 : ZMod (p ^ 5))⁻¹ * (pp * ymid) +
            pp ^ 3 * eQ)
          = (2 : ZMod (p ^ 5)) * H2 - (2 : ZMod (p ^ 5)) * pp * SZ p 5 +
              (2 : ZMod (p ^ 5)) * (2 : ZMod (p ^ 5))⁻¹ * (pp ^ 3 * ymid) +
              (2 : ZMod (p ^ 5)) * pp ^ 3 * eQ := by
            ring
      _ = (2 : ZMod (p ^ 5)) * H2 - (2 : ZMod (p ^ 5)) * pp * SZ p 5 +
              1 * (pp ^ 3 * ymid) +
              (2 : ZMod (p ^ 5)) * pp ^ 3 * eQ := by
            rw [h2inv]
      _ = (2 : ZMod (p ^ 5)) * H2 - (2 : ZMod (p ^ 5)) * pp * SZ p 5 +
              pp ^ 3 * ymid + (2 : ZMod (p ^ 5)) * pp ^ 3 * eQ := by
            ring
  have hrhs :
      (2 : ZMod (p ^ 5)) *
          (- (2 : ZMod (p ^ 5))⁻¹ * H2 + pp ^ 3 * eHp) =
        - H2 + (2 : ZMod (p ^ 5)) * pp ^ 3 * eHp := by
    calc
      (2 : ZMod (p ^ 5)) *
          (- (2 : ZMod (p ^ 5))⁻¹ * H2 + pp ^ 3 * eHp)
          = - ((2 : ZMod (p ^ 5)) * (2 : ZMod (p ^ 5))⁻¹) * H2 +
              (2 : ZMod (p ^ 5)) * pp ^ 3 * eHp := by
            ring
      _ = - (1 : ZMod (p ^ 5)) * H2 +
              (2 : ZMod (p ^ 5)) * pp ^ 3 * eHp := by
            rw [h2inv]
      _ = - H2 + (2 : ZMod (p ^ 5)) * pp ^ 3 * eHp := by
            ring
  have heq := hrearr.symm.trans (hmul.trans hrhs)
  -- heq : 2 H2 - 2 pp SZ + pp^3 ymid + 2 pp^3 eQ = -H2 + 2 pp^3 eHp
  have hmove := congrArg (fun t : ZMod (p ^ 5) => t + H2 - pp ^ 3 * ymid -
      (2 : ZMod (p ^ 5)) * pp ^ 3 * eQ) heq
  -- LHS becomes 3 H2 - 2 pp SZ, RHS becomes 2 pp^3 eHp - pp^3 ymid - 2 pp^3 eQ
  have : (3 : ZMod (p ^ 5)) * H2 - (2 : ZMod (p ^ 5)) * pp * SZ p 5 =
      pp ^ 3 * ((2 : ZMod (p ^ 5)) * eHp - (2 : ZMod (p ^ 5)) * eQ - ymid) := by
    convert hmove using 1 <;> ring
  simpa [H2, pp] using this

lemma Qinner_cast {p k : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero p]
    (hp : 7 ≤ p) (hk : k ∈ Icc 1 (p - 1)) :
    ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      (((k : ZMod (p ^ 5))⁻¹) ^ 2 *
        ((2 : ZMod (p ^ 5))⁻¹ *
            ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
              ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
          (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
            (k : ZMod (p ^ 5))⁻¹ +
          (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2)) =
      (9 : ZMod p) * (2 : ZMod p)⁻¹ *
          ((∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹) ^ 2 -
            ∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2) *
          ((k : ZMod p)⁻¹) ^ 2 +
        (6 : ZMod p) * (∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹) *
          ((k : ZMod p)⁻¹) ^ 3 +
        (2 : ZMod p) * ((k : ZMod p)⁻¹) ^ 4 := by
  set phi := ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
  set Y : ZMod (p ^ 5) := ∑ i ∈ Icc 1 (k - 1), yQuad p i
  set Zsq : ZMod (p ^ 5) := ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2
  set invk : ZMod (p ^ 5) := (k : ZMod (p ^ 5))⁻¹
  have hY : phi Y = -(3 : ZMod p) * ∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹ := by
    unfold phi Y
    rw [map_sum]
    have hmul : -(3 : ZMod p) * ∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹ =
        ∑ i ∈ Icc 1 (k - 1), -(3 : ZMod p) * (i : ZMod p)⁻¹ :=
      mul_sum _ _ _
    rw [hmul]
    refine sum_congr rfl fun i hi => ?_
    exact castHom_yQuad (mem_Icc_of_prefix hk hi)
  have hZ : phi Zsq = (9 : ZMod p) * ∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2 := by
    unfold phi Zsq
    rw [map_sum]
    refine Eq.trans (sum_congr rfl fun i hi => ?_) (mul_sum _ _ _).symm
    have := yQuad_sq_mod_p (mem_Icc_of_prefix hk hi)
    rw [this]
    ring
  have hinv : phi invk = (k : ZMod p)⁻¹ := by
    unfold phi invk
    exact castHom_inv (dvd_prime_self_pow (by norm_num : 0 < 5)) (isUnit_of_mem_Icc hk)
  have h2 : phi (2 : ZMod (p ^ 5)) = (2 : ZMod p) := map_ofNat _ _
  have h2u : IsUnit (2 : ZMod (p ^ 5)) := isUnit_two_zmod (by omega)
  have h2inv : phi ((2 : ZMod (p ^ 5))⁻¹) = (2 : ZMod p)⁻¹ := by
    unfold phi
    rw [castHom_unit_inv (dvd_prime_self_pow (by norm_num : 0 < 5)) h2u, h2]
  have hmap :
      phi (invk ^ 2 *
        ((2 : ZMod (p ^ 5))⁻¹ * (Y ^ 2 - Zsq) -
          (2 : ZMod (p ^ 5)) * Y * invk +
          (2 : ZMod (p ^ 5)) * invk ^ 2)) =
      (phi invk) ^ 2 *
        ((phi ((2 : ZMod (p ^ 5))⁻¹)) * ((phi Y) ^ 2 - phi Zsq) -
          phi (2 : ZMod (p ^ 5)) * phi Y * phi invk +
          phi (2 : ZMod (p ^ 5)) * (phi invk) ^ 2) := by
    unfold phi
    simp only [map_mul, map_add, map_sub, map_pow]
  -- rewrite the original expression to use Y, Zsq, invk
  have hform :
      ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
        ((2 : ZMod (p ^ 5))⁻¹ *
            ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
              ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
          (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
            (k : ZMod (p ^ 5))⁻¹ +
          (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2) =
      invk ^ 2 *
        ((2 : ZMod (p ^ 5))⁻¹ * (Y ^ 2 - Zsq) -
          (2 : ZMod (p ^ 5)) * Y * invk +
          (2 : ZMod (p ^ 5)) * invk ^ 2) := by
    unfold Y Zsq invk; rfl
  rw [hform, hmap, hY, hZ, hinv, h2, h2inv]
  ring

lemma Qsum_cast_zero {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)] [NeZero p]
    (hp : 7 ≤ p) :
    ZMod.castHom (dvd_prime_self_pow (by norm_num : 0 < 5)) (ZMod p)
      (∑ k ∈ Icc 1 (p - 1),
        ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
          ((2 : ZMod (p ^ 5))⁻¹ *
              ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
                ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
            (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
              (k : ZMod (p ^ 5))⁻¹ +
            (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2)) = 0 := by
  rw [map_sum, sum_congr rfl (fun k hk => Qinner_cast hp hk)]
  rw [sum_add_distrib, sum_add_distrib]
  have hX' :
      ∑ k ∈ Icc 1 (p - 1),
          (9 : ZMod p) * (2 : ZMod p)⁻¹ *
            ((∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹) ^ 2 -
              ∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2) *
            ((k : ZMod p)⁻¹) ^ 2 = 0 := by
    have hmid :
        ∑ k ∈ Icc 1 (p - 1),
            ((∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹) ^ 2 -
              ∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2) *
            ((k : ZMod p)⁻¹) ^ 2 = 0 := by
      have hsplit :
          ∑ k ∈ Icc 1 (p - 1),
              ((∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹) ^ 2 -
                ∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2) *
              ((k : ZMod p)⁻¹) ^ 2 =
            ∑ k ∈ Icc 1 (p - 1),
                (∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 -
              ∑ k ∈ Icc 1 (p - 1),
                (∑ i ∈ Icc 1 (k - 1), ((i : ZMod p)⁻¹) ^ 2) *
                  ((k : ZMod p)⁻¹) ^ 2 := by
        rw [sum_congr rfl (fun k _ => sub_mul _ _ _), sum_sub_distrib]
      rw [hsplit, sum_harm_sq_prefix_div_k2 hp, sum_harm2_prefix_div_k2 hp, sub_zero]
    have hconst := congrArg (fun t => (9 : ZMod p) * (2 : ZMod p)⁻¹ * t) hmid
    dsimp at hconst
    rw [mul_zero] at hconst
    refine Eq.trans ?_ hconst
    refine Eq.trans (sum_congr rfl fun k _ => ?_) (mul_sum _ _ _).symm
    ring
  have hH3' :
      ∑ k ∈ Icc 1 (p - 1),
          (6 : ZMod p) * (∑ i ∈ Icc 1 (k - 1), (i : ZMod p)⁻¹) *
            ((k : ZMod p)⁻¹) ^ 3 = 0 := by
    have hconst := congrArg (fun t => (6 : ZMod p) * t) (sum_harm_prefix_div_k3 hp)
    dsimp at hconst
    rw [mul_zero] at hconst
    refine Eq.trans ?_ hconst
    refine Eq.trans (sum_congr rfl fun k _ => ?_) (mul_sum _ _ _).symm
    ring
  have hH4' :
      ∑ k ∈ Icc 1 (p - 1), (2 : ZMod p) * ((k : ZMod p)⁻¹) ^ 4 = 0 := by
    rw [← mul_sum, harmFp4_sum hp, mul_zero]
  rw [hX', hH3', hH4', add_zero, add_zero]

lemma two_W_add_seven_H2 {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    [NeZero (p ^ 3)] [NeZero (p ^ 2)] [NeZero p] (hp : 7 ≤ p) :
    (p : ZMod (p ^ 5)) ^ 2 *
      (2 * ratZMod (p ^ 5) (Wrat p) + 7 * harmZ p 5 2 (p - 1)) = 0 := by
  have hW : ratZMod (p ^ 5) (Wrat p) = Wz p 5 := ratZMod_Wrat
  rw [hW]
  haveI : NeZero (p ^ 4) := neZero_pow_of_prime
  obtain ⟨eW, hWexp⟩ := Wz_expand_mod_p3 hp
  obtain ⟨yH3, hH3⟩ := harmZ_three_dvd_p2 (p := p) (r := 5) (by norm_num) hp
  obtain ⟨yH2p, hH2p⟩ := harm2_prefix_div_k2_dvd_p (p := p) hp
  obtain ⟨yQ, hQ0⟩ :=
    eq_mul_pow_of_cast_eq_zero (dvd_prime_self_pow (by norm_num : 0 < 5))
      (Qsum_cast_zero (p := p) hp)
  obtain ⟨zSZ, hSZ⟩ := three_H2_sub_two_p_SZ (p := p) hp
  have hL := sum_invsq_L (p := p)
  set H2 : ZMod (p ^ 5) := harmZ p 5 2 (p - 1)
  set L : ZMod (p ^ 5) :=
    ∑ k ∈ Icc 1 (p - 1),
      ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
        (∑ i ∈ Icc 1 (k - 1), yQuad p i -
          (2 : ZMod (p ^ 5)) * (k : ZMod (p ^ 5))⁻¹)
  set Q : ZMod (p ^ 5) :=
    ∑ k ∈ Icc 1 (p - 1),
      ((k : ZMod (p ^ 5))⁻¹) ^ 2 *
        ((2 : ZMod (p ^ 5))⁻¹ *
            ((∑ i ∈ Icc 1 (k - 1), yQuad p i) ^ 2 -
              ∑ i ∈ Icc 1 (k - 1), (yQuad p i) ^ 2) -
          (2 : ZMod (p ^ 5)) * (∑ i ∈ Icc 1 (k - 1), yQuad p i) *
            (k : ZMod (p ^ 5))⁻¹ +
          (2 : ZMod (p ^ 5)) * ((k : ZMod (p ^ 5))⁻¹) ^ 2)
  set SH2 : ZMod (p ^ 5) :=
    ∑ k ∈ Icc 1 (p - 1),
      harmZ p 5 2 (k - 1) * ((k : ZMod (p ^ 5))⁻¹) ^ 2
  have h2W : 2 * Wz p 5 + 7 * H2 =
      9 * H2 + (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * L +
        (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * Q +
        (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * eW := by
    unfold L Q H2
    rw [hWexp]
    ring
  have hL' : L = -(3 : ZMod (p ^ 5)) * SZ p 5 +
      (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * SH2 -
      (2 : ZMod (p ^ 5)) * harmZ p 5 3 (p - 1) := by
    unfold L SH2
    exact hL
  have hH2p' : SH2 = (p : ZMod (p ^ 5)) * yH2p := by
    unfold SH2; exact hH2p
  have hQ' : Q = (p : ZMod (p ^ 5)) * yQ := by
    unfold Q; exact hQ0
  have h9 : (9 : ZMod (p ^ 5)) * H2 -
      (6 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * SZ p 5 =
      (p : ZMod (p ^ 5)) ^ 3 * ((3 : ZMod (p ^ 5)) * zSZ) := by
    have := congrArg (fun t : ZMod (p ^ 5) => (3 : ZMod (p ^ 5)) * t) hSZ
    unfold H2 at this ⊢
    ring_nf at this ⊢
    exact this
  have hgoal : 2 * Wz p 5 + 7 * H2 =
      (p : ZMod (p ^ 5)) ^ 3 *
        ((3 : ZMod (p ^ 5)) * zSZ + (4 : ZMod (p ^ 5)) * yH2p -
          (4 : ZMod (p ^ 5)) * yH3 + (2 : ZMod (p ^ 5)) * yQ +
          (2 : ZMod (p ^ 5)) * eW) := by
    rw [h2W, hL', hH2p', hH3, hQ']
    have hexpand :
        (9 : ZMod (p ^ 5)) * H2 +
          (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) *
            (-(3 : ZMod (p ^ 5)) * SZ p 5 +
              (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) * yH2p) -
              (2 : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 * yH3)) +
          (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * ((p : ZMod (p ^ 5)) * yQ) +
          (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * eW =
        ((9 : ZMod (p ^ 5)) * H2 -
          (6 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * SZ p 5) +
          (p : ZMod (p ^ 5)) ^ 3 *
            ((4 : ZMod (p ^ 5)) * yH2p - (4 : ZMod (p ^ 5)) * yH3 +
              (2 : ZMod (p ^ 5)) * yQ + (2 : ZMod (p ^ 5)) * eW) := by
      ring
    rw [hexpand, h9]
    ring
  have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := p_pow_five_eq_zero p
  calc
    (p : ZMod (p ^ 5)) ^ 2 * (2 * Wz p 5 + 7 * H2)
        = (p : ZMod (p ^ 5)) ^ 2 *
            ((p : ZMod (p ^ 5)) ^ 3 *
              ((3 : ZMod (p ^ 5)) * zSZ + (4 : ZMod (p ^ 5)) * yH2p -
                (4 : ZMod (p ^ 5)) * yH3 + (2 : ZMod (p ^ 5)) * yQ +
                (2 : ZMod (p ^ 5)) * eW)) := by
          rw [hgoal]
    _ = (p : ZMod (p ^ 5)) ^ 5 *
          ((3 : ZMod (p ^ 5)) * zSZ + (4 : ZMod (p ^ 5)) * yH2p -
            (4 : ZMod (p ^ 5)) * yH3 + (2 : ZMod (p ^ 5)) * yQ +
            (2 : ZMod (p ^ 5)) * eW) := by
          ring
    _ = 0 := by rw [hp5, zero_mul]

lemma p2W_sq_eq_zero {p : ℕ} [Fact p.Prime] [NeZero (p ^ 5)]
    [NeZero (p ^ 3)] [NeZero (p ^ 2)] [NeZero p] (hp : 7 ≤ p) :
    ((p : ZMod (p ^ 5)) ^ 2 * ratZMod (p ^ 5) (Wrat p)) ^ 2 = 0 := by
  have hkey := two_W_add_seven_H2 (p := p) hp
  obtain ⟨z, hz⟩ := harmZ_two_dvd_p (p := p) (r := 5) (by norm_num) hp
  have hunit2 : IsUnit (2 : ZMod (p ^ 5)) := isUnit_two_p5 hp
  have hp6 : (p : ZMod (p ^ 5)) ^ 6 = 0 :=
    nat_cast_p_pow_eq_zero_of_le (by norm_num : 5 ≤ 6)
  set W : ZMod (p ^ 5) := ratZMod (p ^ 5) (Wrat p)
  have hlin : (2 : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 * W) +
      (7 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * z = 0 := by
    have := hkey
    rw [hz] at this
    ring_nf at this ⊢
    exact this
  have hW : (p : ZMod (p ^ 5)) ^ 2 * W =
      (p : ZMod (p ^ 5)) ^ 3 * (-(7 : ZMod (p ^ 5)) * (2 : ZMod (p ^ 5))⁻¹ * z) := by
    have h2inv : (2 : ZMod (p ^ 5))⁻¹ * 2 = 1 :=
      ZMod.inv_mul_of_unit _ hunit2
    have := congrArg (fun t : ZMod (p ^ 5) => (2 : ZMod (p ^ 5))⁻¹ * t) hlin
    dsimp at this
    have hrearr :
        (2 : ZMod (p ^ 5))⁻¹ *
            ((2 : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 * W) +
              (7 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * z) =
          (p : ZMod (p ^ 5)) ^ 2 * W +
            (2 : ZMod (p ^ 5))⁻¹ * ((7 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * z) := by
      calc
        (2 : ZMod (p ^ 5))⁻¹ *
            ((2 : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 * W) +
              (7 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * z)
            = (2 : ZMod (p ^ 5))⁻¹ * 2 * ((p : ZMod (p ^ 5)) ^ 2 * W) +
                (2 : ZMod (p ^ 5))⁻¹ * ((7 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * z) := by
              ring
        _ = 1 * ((p : ZMod (p ^ 5)) ^ 2 * W) +
                (2 : ZMod (p ^ 5))⁻¹ * ((7 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * z) := by
              rw [h2inv]
        _ = (p : ZMod (p ^ 5)) ^ 2 * W +
                (2 : ZMod (p ^ 5))⁻¹ * ((7 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * z) := by
              ring
    rw [hrearr, mul_zero] at this
    have hzero : (p : ZMod (p ^ 5)) ^ 2 * W +
        (2 : ZMod (p ^ 5))⁻¹ * ((7 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 * z) = 0 := this
    have := eq_neg_of_add_eq_zero_left hzero
    convert this using 1
    ring
  change ((p : ZMod (p ^ 5)) ^ 2 * W) ^ 2 = 0
  rw [hW]
  ring_nf
  simp [hp6]

lemma A357674_conjecture_1_of_ge_seven (p : ℕ) (hp : p.Prime) (hge : 7 ≤ p) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ 5) := neZero_pow_of_prime
  haveI : NeZero (p ^ 4) := neZero_pow_of_prime
  haveI : NeZero (p ^ 3) := neZero_pow_of_prime
  haveI : NeZero (p ^ 2) := neZero_pow_of_prime
  haveI : NeZero p := neZero_p
  rw [A357674_eq, A357674_one, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  have hS1 := S1_cast_eq_three_betaZ (p := p) (r := 5) hge
  have hδ := betaZ_sub_one (p := p) hge
  have hδ2 := betaZ_sub_one_sq (p := p) hge
  have hS2 := S2_cast_eq_S1_mul (p := p) (r := 5) hge
  have hkey := two_W_add_seven_H2 (p := p) hge
  have hWsq := p2W_sq_eq_zero (p := p) hge
  set W : ZMod (p ^ 5) := ratZMod (p ^ 5) (Wrat p)
  set H2 : ZMod (p ^ 5) := harmZ p 5 2 (p - 1)
  set δ : ZMod (p ^ 5) := betaZ p 5 - 1
  have hβ7 : (betaZ p 5) ^ 7 = 1 + (7 : ZMod (p ^ 5)) * δ := by
    have hβ : betaZ p 5 = 1 + δ := by unfold δ; ring
    calc
      (betaZ p 5) ^ 7 = (1 + δ) ^ 7 := by rw [hβ]
      _ = 1 + (7 : ZMod (p ^ 5)) * δ := pow_one_add_of_sq_eq_zero (by
            unfold δ; exact hδ2) 7
  have hprod :
      (S1 p : ZMod (p ^ 5)) ^ 4 * (S2 p : ZMod (p ^ 5)) ^ 3 =
        (S1 p : ZMod (p ^ 5)) ^ 7 *
          (1 - (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W) ^ 3 := by
    unfold W; rw [hS2]; ring
  have hS17 :
      (S1 p : ZMod (p ^ 5)) ^ 7 =
        (3 : ZMod (p ^ 5)) ^ 7 * (1 + (7 : ZMod (p ^ 5)) * δ) := by
    rw [hS1, mul_pow, hβ7]
  have hx : ((2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W) ^ 2 = 0 := by
    have : ((2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W) ^ 2 =
        (4 : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 * W) ^ 2 := by ring
    unfold W at hWsq
    rw [this, hWsq, mul_zero]
  have hcube :
      (1 - (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W) ^ 3 =
      1 - (6 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W := by
    have hx' : (-((2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W)) ^ 2 = 0 := by
      rw [neg_sq, hx]
    have hpow := pow_one_add_of_sq_eq_zero hx' 3
    have hL : (1 - (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W) ^ 3 =
        (1 + -((2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W)) ^ 3 := by
      ring
    have hR : 1 + (3 : ℕ) *
        (-((2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W)) =
        1 - (6 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W := by
      simp only [Nat.cast_ofNat]
      ring
    rw [hL, hpow, hR]
  have hcross : ((p : ZMod (p ^ 5)) ^ 2 * W) * ((p : ZMod (p ^ 5)) ^ 2 * H2) = 0 := by
    obtain ⟨z, hz⟩ := harmZ_two_dvd_p (p := p) (r := 5) (by norm_num) hge
    have hp5 : (p : ZMod (p ^ 5)) ^ 5 = 0 := nat_cast_p_pow_eq_zero p 5
    unfold H2
    rw [hz]
    have : ((p : ZMod (p ^ 5)) ^ 2 * W) *
        ((p : ZMod (p ^ 5)) ^ 2 * ((p : ZMod (p ^ 5)) * z)) =
        (p : ZMod (p ^ 5)) ^ 5 * (W * z) := by ring
    rw [this, hp5, zero_mul]
  have hδ' : δ = -((3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * H2) := by
    unfold δ H2; exact hδ
  have hcancel :
      (1 + (7 : ZMod (p ^ 5)) * δ) *
        (1 - (6 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W) = 1 := by
    rw [hδ']
    have hexpand :
        (1 + (7 : ZMod (p ^ 5)) *
            (-((3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * H2))) *
          (1 - (6 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 * W) =
        1 - (3 : ZMod (p ^ 5)) * ((p : ZMod (p ^ 5)) ^ 2 * (2 * W + 7 * H2)) +
          (126 : ZMod (p ^ 5)) *
            (((p : ZMod (p ^ 5)) ^ 2 * W) * ((p : ZMod (p ^ 5)) ^ 2 * H2)) := by
      ring
    rw [hexpand, hcross, mul_zero, add_zero]
    have : (p : ZMod (p ^ 5)) ^ 2 * (2 * W + 7 * H2) = 0 := hkey
    rw [this, mul_zero, sub_zero]
  rw [hprod, hS17, hcube]
  have h2187 : (2187 : ZMod (p ^ 5)) = (3 : ZMod (p ^ 5)) ^ 7 := by
    norm_num
  rw [h2187]
  calc
    (3 : ZMod (p ^ 5)) ^ 7 * (1 + 7 * δ) *
        (1 - 6 * (p : ZMod (p ^ 5)) ^ 2 * W)
        = (3 : ZMod (p ^ 5)) ^ 7 *
            ((1 + 7 * δ) * (1 - 6 * (p : ZMod (p ^ 5)) ^ 2 * W)) := by
          ring
    _ = (3 : ZMod (p ^ 5)) ^ 7 * 1 := by rw [hcancel]
    _ = (3 : ZMod (p ^ 5)) ^ 7 := by ring

/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  rcases lt_or_ge p 7 with hlt | hge
  · interval_cases p
    · exact A357674_conjecture_1_three
    · exact absurd hp (fun h => by
        have := h.eq_one_or_self_of_dvd 2 (by norm_num : 2 ∣ 4)
        omega)
    · exact A357674_conjecture_1_five
    · exact absurd hp (fun h => by
        have := h.eq_one_or_self_of_dvd 2 (by norm_num : 2 ∣ 6)
        omega)
  · exact A357674_conjecture_1_of_ge_seven p hp hge
