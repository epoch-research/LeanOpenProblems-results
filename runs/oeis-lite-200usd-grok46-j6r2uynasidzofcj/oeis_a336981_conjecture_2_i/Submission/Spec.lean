import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped BigOperators

/--
The coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$ T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i $$
-/
def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    -- The multinomial coefficient $\binom{k}{i, i, k-2i}$
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    -- Powers of b and c
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

/--
A336981: $$a(n) = \frac{\sum_{k=0}^{n-1} (4290k + 367) \cdot 3136^{n-1-k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)}{n \cdot \binom{2n-1}{n-1}}$$
where $T_k(b, c)$ denotes the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
The sequence is defined as a function $\mathbb{N} \to \mathbb{Q}$.
-/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 0
  else
    let numerator_sum : ℚ :=
      Finset.sum (range n) (fun k : ℕ =>
        let T1k : ℚ := T_k k 14 1
        let T2k : ℚ := T_k k 17 16

        let k_q : ℚ := k
        -- We use casting for the exponent subtraction to ensure it stays non-negative when k <= n-1
        let n_prime : ℕ := n - 1 - k

        let term_factor : ℚ := 4290 * k_q + 367
        let power_factor : ℚ := (3136 : ℚ) ^ n_prime
        let central_binomial : ℚ := (Nat.choose (2 * k) k : ℚ)

        term_factor * power_factor * central_binomial * T1k * T2k)

    let divisor : ℚ := (n : ℚ) * (Nat.choose (2 * n - 1) (n - 1) : ℚ)

    numerator_sum / divisor

-- Definition for t(k) for the infinite sum
/--
$$t(k) = \frac{4290k+367}{3136^k} \cdot \binom{2k}{k} \cdot T_k(14, 1) \cdot T_k(17, 16)$$
-/
noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)

  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k

  term_factor / power_factor * central_binomial * T1k * T2k

open Real intervalIntegral Filter Topology

lemma choose_mul_choose_central (k i : ℕ) (h : 2 * i ≤ k) :
    (k.choose (2 * i) * (2 * i).choose i : ℚ) =
      (k.choose i * (k - i).choose i : ℚ) := by
  have hi : i ≤ k := le_trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)) h
  have hi' : i ≤ k - i := by
    have : i + i ≤ k := by simpa [two_mul] using h
    exact Nat.le_sub_of_add_le this
  have hi2 : i ≤ 2 * i := Nat.le_mul_of_pos_left _ (by decide)
  have hki : k - i - i = k - 2 * i := by rw [Nat.sub_sub, two_mul]
  have h2i : (2 * i) - i = i := by rw [two_mul, Nat.add_sub_cancel]
  have hL : (k.choose (2 * i) : ℚ) * ((2 * i).choose i : ℚ) =
      (k.factorial : ℚ) / ((i.factorial : ℚ) * (i.factorial : ℚ) * ((k - 2 * i).factorial : ℚ)) := by
    rw [Nat.cast_choose ℚ h, Nat.cast_choose ℚ hi2, h2i]
    have hA : ((2 * i).factorial : ℚ) ≠ 0 := by exact_mod_cast (2 * i).factorial_ne_zero
    field_simp [hA]
  have hR : (k.choose i : ℚ) * ((k - i).choose i : ℚ) =
      (k.factorial : ℚ) / ((i.factorial : ℚ) * (i.factorial : ℚ) * ((k - 2 * i).factorial : ℚ)) := by
    rw [Nat.cast_choose ℚ hi, Nat.cast_choose ℚ hi', hki]
    have hA : ((k - i).factorial : ℚ) ≠ 0 := by exact_mod_cast (k - i).factorial_ne_zero
    field_simp [hA]
  simpa using hL.trans hR.symm

lemma prod_odd_div_even (n : ℕ) :
    (∏ i ∈ range n, ((2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 2))) =
      (n.centralBinom : ℝ) / (4 : ℝ) ^ n := by
  induction n with
  | zero => simp [Nat.centralBinom]
  | succ n ih =>
    rw [prod_range_succ, ih]
    have hnat : ((n + 1 : ℕ) : ℝ) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * (n : ℝ) + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have h4 : (4 : ℝ) ^ (n + 1) = (4 : ℝ) ^ n * 4 := pow_succ _ _
    have htwo : (2 * (n : ℝ) + 2) = 2 * ((n : ℝ) + 1) := by ring
    rw [htwo]
    have hn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
    rw [hn1] at hnat hn0
    have hmain :
        ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) =
          ((n + 1).centralBinom : ℝ) / (4 : ℝ) ^ (n + 1) := by
      have h4n : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h4n1 : (4 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hLHS :
          ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) =
            ((2 * (n : ℝ) + 1) * (n.centralBinom : ℝ)) /
              (2 * ((n : ℝ) + 1) * (4 : ℝ) ^ n) := by field_simp
      rw [hLHS]
      have hdenEq : (2 * ((n : ℝ) + 1) * (4 : ℝ) ^ n) = 2 * (((n : ℝ) + 1) * (4 : ℝ) ^ n) := by ring
      rw [hdenEq]
      apply (div_eq_div_iff (mul_ne_zero (by positivity : (2 : ℝ) ≠ 0)
          (mul_ne_zero hn0 h4n)) h4n1).mpr
      calc
        (2 * (n : ℝ) + 1) * (n.centralBinom : ℝ) * (4 : ℝ) ^ (n + 1)
          = (2 * (n : ℝ) + 1) * (n.centralBinom : ℝ) * ((4 : ℝ) ^ n * 4) := by rw [h4]
        _ = (2 * (2 * (n : ℝ) + 1) * (n.centralBinom : ℝ)) * (2 * (4 : ℝ) ^ n) := by ring
        _ = (((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ)) * (2 * (4 : ℝ) ^ n) := by
            rw [← hnat]
        _ = (2 * ((n : ℝ) + 1) * (4 : ℝ) ^ n) * ((n + 1).centralBinom : ℝ) := by ring
        _ = ((n + 1).centralBinom : ℝ) * (2 * (((n : ℝ) + 1) * (4 : ℝ) ^ n)) := by ring
    simpa [mul_comm] using hmain

lemma integral_sin_pow_two_mul (n : ℕ) :
    ∫ x in (0 : ℝ)..π, sin x ^ (2 * n) = π * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) := by
  rw [integral_sin_pow_even, prod_odd_div_even]

lemma integral_cos_pow_even (n : ℕ) :
    ∫ x in (0 : ℝ)..π, cos x ^ (2 * n) =
      π * ∏ i ∈ range n, ((2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 2)) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hred := integral_cos_pow (a := (0 : ℝ)) (b := π) (n := 2 * n)
    simp [sin_pi, sin_zero] at hred
    -- hred : ∫ cos^{2n+2} = (2n+1)/(2n+2) * ∫ cos^{2n}
    have hpow : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [hpow, hred, ih, prod_range_succ]
    ring

lemma integral_cos_pow_two_mul (n : ℕ) :
    ∫ x in (0 : ℝ)..π, cos x ^ (2 * n) = π * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) := by
  rw [integral_cos_pow_even, prod_odd_div_even]

lemma integral_cos_pow_odd_zero (i : ℕ) :
    ∫ x in (0 : ℝ)..π, cos x ^ (2 * i + 1) = 0 := by
  have hsub : ∫ x in (0 : ℝ)..π, cos (π - x) ^ (2 * i + 1) =
      ∫ x in (0 : ℝ)..π, cos x ^ (2 * i + 1) := by
    simpa using
      (integral_comp_sub_left (f := fun x => cos x ^ (2 * i + 1)) (a := (0 : ℝ)) (b := π) (d := π))
  have hneg : ∫ x in (0 : ℝ)..π, cos (π - x) ^ (2 * i + 1) =
      ∫ x in (0 : ℝ)..π, -(cos x ^ (2 * i + 1)) := by
    apply integral_congr
    intro x _hx
    dsimp
    rw [cos_pi_sub, Odd.neg_pow (odd_two_mul_add_one i)]
  have eqneg : ∫ x in (0 : ℝ)..π, cos x ^ (2 * i + 1) =
      -∫ x in (0 : ℝ)..π, cos x ^ (2 * i + 1) := by
    calc
      ∫ x in (0 : ℝ)..π, cos x ^ (2 * i + 1)
        = ∫ x in (0 : ℝ)..π, cos (π - x) ^ (2 * i + 1) := hsub.symm
      _ = ∫ x in (0 : ℝ)..π, -(cos x ^ (2 * i + 1)) := hneg
      _ = -∫ x in (0 : ℝ)..π, cos x ^ (2 * i + 1) := by rw [integral_neg]
  linarith [eqneg]

lemma T_k_nonneg (k : ℕ) (b c : ℤ) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ T_k k b c := by
  refine Finset.sum_nonneg ?_
  intro i hi
  have : 0 ≤ ((k.choose i * (k - i).choose i : ℕ) : ℚ) := by exact_mod_cast Nat.zero_le _
  have hb' : 0 ≤ (b : ℚ) := by exact_mod_cast hb
  have hc' : 0 ≤ (c : ℚ) := by exact_mod_cast hc
  positivity

lemma T_k_14_1_eq_sum (k : ℕ) :
    (T_k k 14 1 : ℝ) =
      ∑ i ∈ range (k / 2 + 1),
        ((k.choose i * (k - i).choose i : ℕ) : ℝ) * (14 : ℝ) ^ (k - 2 * i) := by
  simp [T_k]

lemma two_mul_le_of_mem_div_two (k i : ℕ) (hi : i ∈ range (k / 2 + 1)) :
    2 * i ≤ k := by
  have : i * 2 ≤ k :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 (Nat.lt_succ_iff.mp (mem_range.mp hi))
  omega

lemma two_mul_mem_range_of_lt_div_two_succ (k i : ℕ) (hi : i ∈ range (k / 2 + 1)) :
    2 * i ∈ range (k + 1) := by
  rw [mem_range]
  exact Nat.lt_succ_iff.mpr (two_mul_le_of_mem_div_two k i hi)

lemma filter_even_range_eq_image (k : ℕ) :
    (range (k + 1)).filter Even = (range (k / 2 + 1)).image (fun i => 2 * i) := by
  ext j
  constructor
  · intro hj
    obtain ⟨hjlt, hEven⟩ := mem_filter.mp hj
    obtain ⟨i, hi⟩ := even_iff_exists_two_mul.mp hEven
    refine mem_image.mpr ⟨i, ?_, hi.symm⟩
    have hle : 2 * i ≤ k := by
      rw [← hi]
      exact Nat.lt_succ_iff.mp (mem_range.mp hjlt)
    have : i * 2 ≤ k := by rwa [mul_comm]
    exact mem_range.mpr
      (Nat.lt_succ_iff.mpr ((Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 this))
  · intro hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact mem_filter.mpr
      ⟨two_mul_mem_range_of_lt_div_two_succ k i hi, even_two_mul i⟩

lemma injOn_two_mul_range (k : ℕ) :
    Set.InjOn (fun i : ℕ => 2 * i) (range (k / 2 + 1)) := by
  intro i _hi j _hj hij
  exact Nat.mul_left_cancel (by decide : 0 < 2) hij

lemma sum_even_terms {α : Type*} [AddCommMonoid α] (k : ℕ) (f : ℕ → α) :
    ∑ m ∈ (range (k + 1)).filter Even, f m =
      ∑ i ∈ range (k / 2 + 1), f (2 * i) := by
  rw [filter_even_range_eq_image, sum_image (injOn_two_mul_range k)]

lemma odd_pow_cos_integral_zero {m : ℕ} (hm : Odd m) :
    ∫ t in (0 : ℝ)..π, cos t ^ m = 0 := by
  obtain ⟨i, rfl⟩ := hm
  simpa [two_mul, add_comm] using integral_cos_pow_odd_zero i

lemma integral_binomial_cos_mul (k : ℕ) (a d : ℝ) :
    ∫ x in (0 : ℝ)..π, (a + d * cos x) ^ k =
      ∑ i ∈ range (k / 2 + 1),
        (k.choose (2 * i) : ℝ) * a ^ (k - 2 * i) * d ^ (2 * i) *
          (π * ((i.centralBinom : ℝ) / (4 : ℝ) ^ i)) := by
  have hexp : ∀ t : ℝ, (a + d * cos t) ^ k =
      ∑ m ∈ range (k + 1),
        (k.choose m : ℝ) * a ^ (k - m) * (d * cos t) ^ m := by
    intro t
    -- `(x+y)^n = ∑ x^{n-m} y^m C(n,m)`; rewrite via `add_comm` on the binomial sum.
    have h := add_pow a (d * cos t) k
    -- `add_pow x y n` is `∑ x^m y^{n-m} C(n,m)`. Flip by substituting the opposite order.
    have h' := add_pow (d * cos t) a k
    -- We want ∑ C * a^{k-m} * (d cos)^m, which is `add_pow (d*cos) a` after commuting.
    simpa [add_comm a, mul_comm, mul_left_comm, mul_assoc] using h'
  have hswap :
      ∫ t in (0 : ℝ)..π, (a + d * cos t) ^ k =
        ∑ m ∈ range (k + 1),
          (k.choose m : ℝ) * a ^ (k - m) * d ^ m *
            ∫ t in (0 : ℝ)..π, cos t ^ m := by
    have hcongr :
        ∫ t in (0 : ℝ)..π, (a + d * cos t) ^ k =
          ∫ t in (0 : ℝ)..π,
            ∑ m ∈ range (k + 1),
              (k.choose m : ℝ) * a ^ (k - m) * (d * cos t) ^ m :=
      integral_congr (fun t _ => hexp t)
    rw [hcongr, integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro m _hm
      have hpow : ∀ t : ℝ, (d * cos t) ^ m = d ^ m * cos t ^ m := fun t => mul_pow _ _ _
      have :
          ∫ t in (0 : ℝ)..π,
              (k.choose m : ℝ) * a ^ (k - m) * (d * cos t) ^ m =
            (k.choose m : ℝ) * a ^ (k - m) * d ^ m *
              ∫ t in (0 : ℝ)..π, cos t ^ m := by
        have h1 :
            ∫ t in (0 : ℝ)..π,
                (k.choose m : ℝ) * a ^ (k - m) * (d * cos t) ^ m =
              ∫ t in (0 : ℝ)..π,
                (k.choose m : ℝ) * a ^ (k - m) * d ^ m * cos t ^ m :=
          integral_congr (fun t _ => by rw [hpow]; ring)
        rw [h1]
        simpa [mul_assoc] using
          (integral_const_mul
            (c := (k.choose m : ℝ) * a ^ (k - m) * d ^ m)
            (f := fun t : ℝ => cos t ^ m))
      exact this
    · intro m _hm
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hswap]
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (range (k + 1)) (fun m => Even m)
      (fun m =>
        (k.choose m : ℝ) * a ^ (k - m) * d ^ m * ∫ t in (0 : ℝ)..π, cos t ^ m)
  have hodd :
      ∑ m ∈ (range (k + 1)).filter (fun m => ¬ Even m),
          (k.choose m : ℝ) * a ^ (k - m) * d ^ m *
            ∫ t in (0 : ℝ)..π, cos t ^ m = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    have hOdd : Odd m := Nat.not_even_iff_odd.1 (mem_filter.mp hm).2
    rw [odd_pow_cos_integral_zero hOdd, mul_zero]
  have heven :
      ∑ m ∈ (range (k + 1)).filter Even,
          (k.choose m : ℝ) * a ^ (k - m) * d ^ m *
            ∫ t in (0 : ℝ)..π, cos t ^ m =
        ∑ i ∈ range (k / 2 + 1),
          (k.choose (2 * i) : ℝ) * a ^ (k - 2 * i) * d ^ (2 * i) *
            ∫ t in (0 : ℝ)..π, cos t ^ (2 * i) :=
    sum_even_terms k (fun m =>
      (k.choose m : ℝ) * a ^ (k - m) * d ^ m * ∫ t in (0 : ℝ)..π, cos t ^ m)
  rw [← hsplit, heven, hodd, add_zero]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [integral_cos_pow_two_mul]

lemma T_k_eq_sum (k : ℕ) (b c : ℤ) :
    (T_k k b c : ℝ) =
      ∑ i ∈ range (k / 2 + 1),
        ((k.choose i * (k - i).choose i : ℕ) : ℝ) *
          (b : ℝ) ^ (k - 2 * i) * (c : ℝ) ^ i := by
  simp [T_k, mul_assoc]

lemma T_k_cos_integral (k : ℕ) (b c : ℤ) (hc : 0 ≤ (c : ℝ)) :
    (T_k k b c : ℝ) =
      (1 / π) * ∫ x in (0 : ℝ)..π, ((b : ℝ) + 2 * Real.sqrt (c : ℝ) * cos x) ^ k := by
  have hπ : π ≠ 0 := pi_ne_zero
  rw [T_k_eq_sum, integral_binomial_cos_mul]
  have hterm : ∀ i ∈ range (k / 2 + 1),
      ((k.choose i * (k - i).choose i : ℕ) : ℝ) *
          (b : ℝ) ^ (k - 2 * i) * (c : ℝ) ^ i =
        (1 / π) *
          ((k.choose (2 * i) : ℝ) * (b : ℝ) ^ (k - 2 * i) *
            (2 * Real.sqrt (c : ℝ)) ^ (2 * i) *
            (π * ((i.centralBinom : ℝ) / (4 : ℝ) ^ i))) := by
    intro i hi
    have h2i : 2 * i ≤ k := two_mul_le_of_mem_div_two k i hi
    have hch : ((k.choose i * (k - i).choose i : ℕ) : ℝ) =
        (k.choose (2 * i) * (2 * i).choose i : ℝ) := by
      exact_mod_cast (choose_mul_choose_central k i h2i).symm
    have hcent : ((2 * i).choose i : ℝ) = (i.centralBinom : ℝ) := by
      simp [Nat.centralBinom]
    have h4i : (4 : ℝ) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
    have hsqrt : (Real.sqrt (c : ℝ)) ^ (2 * i) = (c : ℝ) ^ i := by
      rw [pow_mul, Real.sq_sqrt hc]
    have htwo : (2 : ℝ) ^ (2 * i) = (4 : ℝ) ^ i := by
      rw [pow_mul, show (2 : ℝ) ^ 2 = 4 from by norm_num]
    have hd : (2 * Real.sqrt (c : ℝ)) ^ (2 * i) =
        (4 : ℝ) ^ i * (c : ℝ) ^ i := by
      rw [mul_pow, htwo, hsqrt]
    have hπi : π ≠ 0 := hπ
    -- After cancelling `4^i` and `π`, both sides match.
    calc
      ((k.choose i * (k - i).choose i : ℕ) : ℝ) *
          (b : ℝ) ^ (k - 2 * i) * (c : ℝ) ^ i
          = (k.choose (2 * i) : ℝ) * (i.centralBinom : ℝ) *
              (b : ℝ) ^ (k - 2 * i) * (c : ℝ) ^ i := by
            rw [hch, hcent]
      _ = (1 / π) *
            ((k.choose (2 * i) : ℝ) * (b : ℝ) ^ (k - 2 * i) *
              (2 * Real.sqrt (c : ℝ)) ^ (2 * i) *
              (π * ((i.centralBinom : ℝ) / (4 : ℝ) ^ i))) := by
            rw [hd]
            field_simp [hπi, h4i]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

lemma T_k_14_1_integral (k : ℕ) :
    (T_k k 14 1 : ℝ) = (2 : ℝ) ^ k / π * ∫ x in (0 : ℝ)..π, (7 + cos x) ^ k := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hc : 0 ≤ ((1 : ℤ) : ℝ) := by norm_num
  have hmain := T_k_cos_integral k 14 1 hc
  have hsqrt : Real.sqrt ((1 : ℤ) : ℝ) = 1 := by
    simp [Real.sqrt_one]
  have hcongr : ∀ x : ℝ,
      (((14 : ℤ) : ℝ) + 2 * Real.sqrt ((1 : ℤ) : ℝ) * cos x) ^ k =
        (2 : ℝ) ^ k * (7 + cos x) ^ k := by
    intro x
    have : ((14 : ℤ) : ℝ) + 2 * Real.sqrt ((1 : ℤ) : ℝ) * cos x = 2 * (7 + cos x) := by
      rw [hsqrt]; norm_cast; ring
    rw [this, mul_pow]
  have hint :
      ∫ x in (0 : ℝ)..π,
          (((14 : ℤ) : ℝ) + 2 * Real.sqrt ((1 : ℤ) : ℝ) * cos x) ^ k =
        (2 : ℝ) ^ k * ∫ x in (0 : ℝ)..π, (7 + cos x) ^ k := by
    have :=
      (integral_congr (a := (0 : ℝ)) (b := π) (fun x _ => hcongr x) :
        ∫ x in (0 : ℝ)..π,
            (((14 : ℤ) : ℝ) + 2 * Real.sqrt ((1 : ℤ) : ℝ) * cos x) ^ k =
          ∫ x in (0 : ℝ)..π, (2 : ℝ) ^ k * (7 + cos x) ^ k)
    rw [this, integral_const_mul]
  rw [hmain, hint]
  field_simp [hπ]

lemma T_k_17_16_integral (k : ℕ) :
    (T_k k 17 16 : ℝ) = (1 / π) * ∫ x in (0 : ℝ)..π, (17 + 8 * cos x) ^ k := by
  have hc : 0 ≤ ((16 : ℤ) : ℝ) := by norm_num
  have hmain := T_k_cos_integral k 17 16 hc
  have hsqrt : Real.sqrt ((16 : ℤ) : ℝ) = 4 := by
    have : ((16 : ℤ) : ℝ) = (4 : ℝ) ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  have hcongr : ∀ x : ℝ,
      (((17 : ℤ) : ℝ) + 2 * Real.sqrt ((16 : ℤ) : ℝ) * cos x) ^ k =
        (17 + 8 * cos x) ^ k := by
    intro x
    congr 1
    rw [hsqrt]
    norm_num
  have hint :
      ∫ x in (0 : ℝ)..π,
          (((17 : ℤ) : ℝ) + 2 * Real.sqrt ((16 : ℤ) : ℝ) * cos x) ^ k =
        ∫ x in (0 : ℝ)..π, (17 + 8 * cos x) ^ k :=
    integral_congr (fun x _ => hcongr x)
  rw [hmain, hint]


lemma centralBinom_integral (k : ℕ) :
    ((2 * k).choose k : ℝ) = (4 : ℝ) ^ k / π * ∫ θ in (0 : ℝ)..π, cos θ ^ (2 * k) := by
  have hπ : π ≠ 0 := pi_ne_zero
  have h := integral_cos_pow_two_mul k
  have h4 : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have : (k.centralBinom : ℝ) = ((2 * k).choose k : ℝ) := by
    simp [Nat.centralBinom]
  rw [this] at h
  field_simp [hπ, h4] at h ⊢
  linarith [h]

lemma T_k_14_1_nonneg (k : ℕ) : 0 ≤ (T_k k 14 1 : ℝ) := by
  have : 0 ≤ T_k k 14 1 := T_k_nonneg k 14 1 (by decide) (by decide)
  exact_mod_cast this

lemma T_k_17_16_nonneg (k : ℕ) : 0 ≤ (T_k k 17 16 : ℝ) := by
  have : 0 ≤ T_k k 17 16 := T_k_nonneg k 17 16 (by decide) (by decide)
  exact_mod_cast this

lemma t_nonneg (k : ℕ) : 0 ≤ t k := by
  simp only [t]
  have h3136 : 0 < (3136 : ℝ) ^ k := pow_pos (by norm_num) _
  have hT1 : 0 ≤ (T_k k 14 1 : ℝ) := T_k_14_1_nonneg k
  have hT2 : 0 ≤ (T_k k 17 16 : ℝ) := T_k_17_16_nonneg k
  have hC : 0 ≤ ((2 * k).choose k : ℝ) := by exact_mod_cast Nat.zero_le _
  have htf : 0 ≤ 4290 * (k : ℝ) + 367 := by positivity
  positivity

lemma integral_le_const_mul_length {f : ℝ → ℝ} {M a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hM : ∀ x, a ≤ x → x ≤ b → f x ≤ M) :
    ∫ x in a..b, f x ≤ M * (b - a) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable continuous_const a b
  have hfI : IntervalIntegrable f MeasureTheory.volume a b :=
    Continuous.intervalIntegrable hf a b
  have hmono :=
    intervalIntegral.integral_mono_on hab hfI hconst (fun x hx => hM x hx.1 hx.2)
  have hMval : ∫ x in a..b, (M : ℝ) = M * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  exact hmono.trans_eq hMval

lemma T_k_14_1_le (k : ℕ) : (T_k k 14 1 : ℝ) ≤ (16 : ℝ) ^ k := by
  have hπ0 : π ≠ 0 := pi_ne_zero
  have hbound : ∀ x, 0 ≤ x → x ≤ π → (7 + cos x) ^ k ≤ (8 : ℝ) ^ k := by
    intro x _ _
    have : 7 + cos x ≤ 8 := by linarith [cos_le_one x]
    have h0 : 0 ≤ 7 + cos x := by linarith [neg_one_le_cos x]
    exact pow_le_pow_left₀ h0 this k
  have hint :=
    integral_le_const_mul_length pi_pos.le (by fun_prop) hbound
  have hT := T_k_14_1_integral k
  have hmul : (2 : ℝ) ^ k / π * ((8 : ℝ) ^ k * π) = (16 : ℝ) ^ k := by
    have h28 : (2 : ℝ) ^ k * (8 : ℝ) ^ k = (16 : ℝ) ^ k := by
      rw [← mul_pow]; norm_num
    field_simp [hπ0]
    exact h28
  have : (T_k k 14 1 : ℝ) ≤ (2 : ℝ) ^ k / π * ((8 : ℝ) ^ k * π) := by
    rw [hT]
    have hpos : 0 ≤ (2 : ℝ) ^ k / π := by positivity
    have : ∫ x in (0 : ℝ)..π, (7 + cos x) ^ k ≤ (8 : ℝ) ^ k * π := by
      simpa [sub_zero] using hint
    nlinarith
  linarith

lemma T_k_17_16_le (k : ℕ) : (T_k k 17 16 : ℝ) ≤ (25 : ℝ) ^ k := by
  have hπ0 : π ≠ 0 := pi_ne_zero
  have hbound : ∀ x, 0 ≤ x → x ≤ π → (17 + 8 * cos x) ^ k ≤ (25 : ℝ) ^ k := by
    intro x _ _
    have : 17 + 8 * cos x ≤ 25 := by nlinarith [cos_le_one x]
    have h0 : 0 ≤ 17 + 8 * cos x := by nlinarith [neg_one_le_cos x]
    exact pow_le_pow_left₀ h0 this k
  have hint :=
    integral_le_const_mul_length pi_pos.le (by fun_prop) hbound
  have hT := T_k_17_16_integral k
  have : (T_k k 17 16 : ℝ) ≤ (1 / π) * ((25 : ℝ) ^ k * π) := by
    rw [hT]
    have : ∫ x in (0 : ℝ)..π, (17 + 8 * cos x) ^ k ≤ (25 : ℝ) ^ k * π := by
      simpa [sub_zero] using hint
    have : 0 ≤ 1 / π := by positivity
    nlinarith
  have : (1 / π) * ((25 : ℝ) ^ k * π) = (25 : ℝ) ^ k := by field_simp [hπ0]
  linarith

lemma centralBinom_le (k : ℕ) : ((2 * k).choose k : ℝ) ≤ (4 : ℝ) ^ k := by
  have hprod := prod_odd_div_even k
  have hcent : (k.centralBinom : ℝ) = ((2 * k).choose k : ℝ) := by
    simp [Nat.centralBinom]
  have hle : (∏ i ∈ range k, ((2 * (i : ℝ) + 1) / (2 * (i : ℝ) + 2))) ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => by positivity) ?_
    intro i _
    refine div_le_one_of_le₀ ?_ (by positivity)
    linarith
  have h4 : 0 < (4 : ℝ) ^ k := pow_pos (by norm_num) _
  have : ((2 * k).choose k : ℝ) / (4 : ℝ) ^ k ≤ 1 := by
    rw [← hcent, ← hprod]
    exact hle
  exact (div_le_one h4).mp this

lemma t_le_geom (k : ℕ) : t k ≤ (4290 * (k : ℝ) + 367) * ((25 : ℝ) / 49) ^ k := by
  simp only [t]
  have h3136 : (3136 : ℝ) ^ k > 0 := pow_pos (by norm_num) _
  have hC := centralBinom_le k
  have hT1 := T_k_14_1_le k
  have hT2 := T_k_17_16_le k
  have hnum : 0 ≤ 4290 * (k : ℝ) + 367 := by positivity
  have hC0 : 0 ≤ ((2 * k).choose k : ℝ) := by exact_mod_cast Nat.zero_le _
  have h1 : 0 ≤ (T_k k 14 1 : ℝ) := T_k_14_1_nonneg k
  have h2 : 0 ≤ (T_k k 17 16 : ℝ) := T_k_17_16_nonneg k
  have hprod : ((2 * k).choose k : ℝ) * (T_k k 14 1 : ℝ) * (T_k k 17 16 : ℝ) ≤
      (4 : ℝ) ^ k * (16 : ℝ) ^ k * (25 : ℝ) ^ k := by
    have : ((2 * k).choose k : ℝ) * (T_k k 14 1 : ℝ) ≤ (4 : ℝ) ^ k * (16 : ℝ) ^ k :=
      mul_le_mul hC hT1 h1 (by positivity)
    exact mul_le_mul this hT2 h2 (by positivity)
  have hpow : (4 : ℝ) ^ k * (16 : ℝ) ^ k * (25 : ℝ) ^ k / (3136 : ℝ) ^ k =
      ((25 : ℝ) / 49) ^ k := by
    have hnum' : (4 : ℝ) ^ k * (16 : ℝ) ^ k * (25 : ℝ) ^ k = (1600 : ℝ) ^ k := by
      rw [← mul_pow, ← mul_pow]; norm_num
    have : (1600 : ℝ) / 3136 = (25 : ℝ) / 49 := by norm_num
    rw [hnum', ← div_pow, this]
  have : (4290 * (k : ℝ) + 367) / (3136 : ℝ) ^ k *
        ((2 * k).choose k : ℝ) * (T_k k 14 1 : ℝ) * (T_k k 17 16 : ℝ) ≤
      (4290 * (k : ℝ) + 367) * ((25 : ℝ) / 49) ^ k := by
    calc
      (4290 * (k : ℝ) + 367) / (3136 : ℝ) ^ k *
          ((2 * k).choose k : ℝ) * (T_k k 14 1 : ℝ) * (T_k k 17 16 : ℝ)
        = (4290 * (k : ℝ) + 367) *
            (((2 * k).choose k : ℝ) * (T_k k 14 1 : ℝ) * (T_k k 17 16 : ℝ) /
              (3136 : ℝ) ^ k) := by
            field_simp [ne_of_gt h3136]
      _ ≤ (4290 * (k : ℝ) + 367) *
            ((4 : ℝ) ^ k * (16 : ℝ) ^ k * (25 : ℝ) ^ k / (3136 : ℝ) ^ k) := by
          apply mul_le_mul_of_nonneg_left _ hnum
          exact div_le_div_of_nonneg_right hprod (le_of_lt h3136)
      _ = (4290 * (k : ℝ) + 367) * ((25 : ℝ) / 49) ^ k := by rw [hpow]
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

lemma summable_t : Summable t := by
  have hr : ‖(25 : ℝ) / 49‖ < 1 := by
    rw [Real.norm_eq_abs]; norm_num
  have h1 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * ((25 : ℝ) / 49) ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one (k := 1) (r := (25 : ℝ) / 49) hr
  have h1' : Summable fun k : ℕ => (k : ℝ) * ((25 : ℝ) / 49) ^ k := by
    simpa using h1
  have h0 : Summable fun k : ℕ => ((25 : ℝ) / 49) ^ k :=
    summable_geometric_of_norm_lt_one hr
  have hsum : Summable fun k : ℕ => (4290 * (k : ℝ) + 367) * ((25 : ℝ) / 49) ^ k := by
    have := (h1'.mul_left (4290 : ℝ)).add (h0.mul_left (367 : ℝ))
    convert this using 1
    ext k
    ring
  exact Summable.of_nonneg_of_le t_nonneg t_le_geom hsum

lemma eight_div_3136 : (8 : ℝ) / 3136 = 1 / 392 := by norm_num

lemma intervalIntegral_mul (f g : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, f x) * (∫ y in a..b, g y) =
      ∫ x in a..b, ∫ y in a..b, f x * g y := by
  have h1 :
      (∫ x in a..b, f x) * (∫ y in a..b, g y) =
        ∫ x in a..b, f x * ∫ y in a..b, g y := by
    simpa [mul_comm] using
      (intervalIntegral.integral_const_mul (c := ∫ y in a..b, g y) (f := f)).symm
  rw [h1]
  refine intervalIntegral.integral_congr ?_
  intro x _
  simpa [mul_comm] using
    (intervalIntegral.integral_const_mul (c := f x) (f := g)).symm

lemma intervalIntegral_mul₃ (f g h : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, f x) * (∫ y in a..b, g y) * (∫ z in a..b, h z) =
      ∫ x in a..b, ∫ y in a..b, ∫ z in a..b, f x * g y * h z := by
  calc
    (∫ x in a..b, f x) * (∫ y in a..b, g y) * (∫ z in a..b, h z)
      = (∫ x in a..b, ∫ y in a..b, f x * g y) * (∫ z in a..b, h z) := by
        rw [intervalIntegral_mul f g a b]
    _ = ∫ x in a..b, (∫ y in a..b, f x * g y) * (∫ z in a..b, h z) := by
        simpa [mul_comm] using
          (intervalIntegral.integral_const_mul (c := ∫ z in a..b, h z)
            (f := fun x => ∫ y in a..b, f x * g y)).symm
    _ = ∫ x in a..b, ∫ y in a..b, ∫ z in a..b, f x * g y * h z := by
        refine intervalIntegral.integral_congr ?_
        intro x _
        simpa [mul_assoc] using
          (intervalIntegral_mul (fun y : ℝ => f x * g y) h a b)

lemma four_mul_two_pow (k : ℕ) : (4 : ℝ) ^ k * (2 : ℝ) ^ k = (8 : ℝ) ^ k := by
  rw [← mul_pow]; norm_num

lemma eight_mul_392_pow (k : ℕ) : (8 : ℝ) ^ k * (392 : ℝ) ^ k = (3136 : ℝ) ^ k := by
  have : (8 : ℝ) * 392 = 3136 := by norm_num
  rw [← mul_pow, this]

lemma t_prefactor (k : ℕ) :
    (4290 * (k : ℝ) + 367) / (3136 : ℝ) ^ k * ((4 : ℝ) ^ k * (2 : ℝ) ^ k / π ^ 3) =
      (1 / π ^ 3) * ((4290 * (k : ℝ) + 367) / (392 : ℝ) ^ k) := by
  have hπ3 : π ^ 3 ≠ 0 := pow_ne_zero 3 pi_ne_zero
  have h3136 : (3136 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h392 : (392 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [four_mul_two_pow]
  field_simp [hπ3, h3136, h392]
  exact eight_mul_392_pow k

lemma t_integrand_pow (k : ℕ) (θ u v : ℝ) :
    (4290 * (k : ℝ) + 367) / (392 : ℝ) ^ k *
        (cos θ ^ (2 * k) * (7 + cos u) ^ k * (17 + 8 * cos v) ^ k) =
      (4290 * (k : ℝ) + 367) *
        ((cos θ ^ 2 * (7 + cos u) * (17 + 8 * cos v)) / 392) ^ k := by
  have h392 : (392 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcos : cos θ ^ (2 * k) = (cos θ ^ 2) ^ k := pow_mul _ _ _
  rw [hcos, ← mul_pow, ← mul_pow, div_pow]
  field_simp [h392]

lemma t_eq_triple_integral (k : ℕ) :
    t k =
      (1 / π ^ 3) *
        ∫ θ in (0 : ℝ)..π,
          ∫ u in (0 : ℝ)..π,
            ∫ v in (0 : ℝ)..π,
              (4290 * (k : ℝ) + 367) *
                ((cos θ ^ 2 * (7 + cos u) * (17 + 8 * cos v)) / 392) ^ k := by
  have hπ : π ≠ 0 := pi_ne_zero
  have hπ3 : π ^ 3 ≠ 0 := pow_ne_zero 3 hπ
  have hC := centralBinom_integral k
  have hT1 := T_k_14_1_integral k
  have hT2 := T_k_17_16_integral k
  have hprod :
      ((2 * k).choose k : ℝ) * (T_k k 14 1 : ℝ) * (T_k k 17 16 : ℝ) =
        (4 : ℝ) ^ k * (2 : ℝ) ^ k / π ^ 3 *
          ((∫ θ in (0 : ℝ)..π, cos θ ^ (2 * k)) *
            (∫ u in (0 : ℝ)..π, (7 + cos u) ^ k) *
            (∫ v in (0 : ℝ)..π, (17 + 8 * cos v) ^ k)) := by
    rw [hC, hT1, hT2]
    field_simp [hπ, hπ3]
  have hiter :=
    intervalIntegral_mul₃
      (fun θ : ℝ => cos θ ^ (2 * k))
      (fun u : ℝ => (7 + cos u) ^ k)
      (fun v : ℝ => (17 + 8 * cos v) ^ k)
      (0 : ℝ) π
  simp only [t]
  -- `t` unfolds with a slightly different association of the product.
  have hassoc :
      (4290 * (k : ℝ) + 367) / (3136 : ℝ) ^ k *
          ((2 * k).choose k : ℝ) * (T_k k 14 1 : ℝ) * (T_k k 17 16 : ℝ) =
        (4290 * (k : ℝ) + 367) / (3136 : ℝ) ^ k *
          (((2 * k).choose k : ℝ) * (T_k k 14 1 : ℝ) * (T_k k 17 16 : ℝ)) := by
    ring
  rw [hassoc, hprod, hiter]
  -- Reassociate to apply `t_prefactor`.
  have hreassoc :
      (4290 * (k : ℝ) + 367) / (3136 : ℝ) ^ k *
          ((4 : ℝ) ^ k * (2 : ℝ) ^ k / π ^ 3 *
            ∫ θ in (0 : ℝ)..π,
              ∫ u in (0 : ℝ)..π,
                ∫ v in (0 : ℝ)..π,
                  cos θ ^ (2 * k) * (7 + cos u) ^ k * (17 + 8 * cos v) ^ k) =
        ((4290 * (k : ℝ) + 367) / (3136 : ℝ) ^ k * ((4 : ℝ) ^ k * (2 : ℝ) ^ k / π ^ 3)) *
          ∫ θ in (0 : ℝ)..π,
            ∫ u in (0 : ℝ)..π,
              ∫ v in (0 : ℝ)..π,
                cos θ ^ (2 * k) * (7 + cos u) ^ k * (17 + 8 * cos v) ^ k := by
    ring
  rw [hreassoc, t_prefactor k]
  -- pull `(4290k+367)/392^k` through the triple integral
  have hpull :
      (4290 * (k : ℝ) + 367) / (392 : ℝ) ^ k *
          ∫ θ in (0 : ℝ)..π,
            ∫ u in (0 : ℝ)..π,
              ∫ v in (0 : ℝ)..π,
                cos θ ^ (2 * k) * (7 + cos u) ^ k * (17 + 8 * cos v) ^ k =
        ∫ θ in (0 : ℝ)..π,
          ∫ u in (0 : ℝ)..π,
            ∫ v in (0 : ℝ)..π,
              (4290 * (k : ℝ) + 367) *
                ((cos θ ^ 2 * (7 + cos u) * (17 + 8 * cos v)) / 392) ^ k := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro θ _
    dsimp
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro u _
    dsimp
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro v _
    dsimp
    exact t_integrand_pow k θ u v
  rw [mul_assoc (1 / π ^ 3), hpull]

/-- The angular product appearing in the integral representation of `t`. -/
noncomputable def lam (θ u v : ℝ) : ℝ :=
  (cos θ ^ 2 * (7 + cos u) * (17 + 8 * cos v)) / 392

lemma lam_nonneg (θ u v : ℝ) : 0 ≤ lam θ u v := by
  have h1 : 0 ≤ cos θ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 7 + cos u := by linarith [neg_one_le_cos u]
  have h3 : 0 ≤ 17 + 8 * cos v := by nlinarith [neg_one_le_cos v]
  unfold lam
  positivity

lemma lam_lt_one (θ u v : ℝ) : lam θ u v < 1 := by
  have hcos : cos θ ^ 2 ≤ 1 := by
    have := abs_cos_le_one θ
    have : |cos θ| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    simpa [sq_abs] using this
  have hu : 7 + cos u ≤ 8 := by linarith [cos_le_one u]
  have hv : 17 + 8 * cos v ≤ 25 := by nlinarith [cos_le_one v]
  have h2 : 0 ≤ 7 + cos u := by linarith [neg_one_le_cos u]
  have h3 : 0 ≤ 17 + 8 * cos v := by nlinarith [neg_one_le_cos v]
  have hprod : cos θ ^ 2 * (7 + cos u) * (17 + 8 * cos v) ≤ 1 * 8 * 25 := by
    have : cos θ ^ 2 * (7 + cos u) ≤ 1 * 8 :=
      mul_le_mul hcos hu h2 (by norm_num)
    exact mul_le_mul this hv h3 (by norm_num)
  have : lam θ u v ≤ (200 : ℝ) / 392 := by
    unfold lam
    have : (8 : ℝ) * 25 = 200 := by norm_num
    nlinarith
  have : (200 : ℝ) / 392 < 1 := by norm_num
  linarith

lemma tsum_linear_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ, (4290 * (k : ℝ) + 367) * r ^ k) =
      (367 + 3923 * r) / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have h0 := tsum_geometric_of_lt_one hr0 hr1
  have h1 := tsum_coe_mul_geometric_of_norm_lt_one (r := r) hnorm
  have hs0 : Summable fun k : ℕ => r ^ k :=
    summable_geometric_of_lt_one hr0 hr1
  have hs1 : Summable fun k : ℕ => (k : ℝ) * r ^ k := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (k := 1) (r := r) hnorm)
  have hfun : (fun k : ℕ => (4290 * (k : ℝ) + 367) * r ^ k) =
      (fun k : ℕ => (4290 * ((k : ℝ) * r ^ k)) + (367 * r ^ k)) := by
    funext k; ring
  rw [hfun, (hs1.mul_left (4290 : ℝ)).tsum_add (hs0.mul_left (367 : ℝ)),
    tsum_mul_left, tsum_mul_left, h1, h0]
  have hne : 1 - r ≠ 0 := by linarith
  field_simp [hne]
  ring

lemma integral_Ioi_inv_one_add_sq_zero :
    ∫ t in Set.Ioi (0 : ℝ), (1 + t ^ 2)⁻¹ = π / 2 := by
  simpa using integral_Ioi_inv_one_add_sq (i := (0 : ℝ))

lemma integral_Ioi_inv_p_add_q_sq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∫ t in Set.Ioi (0 : ℝ), (p + q * t ^ 2)⁻¹ =
      (π / 2) / Real.sqrt (p * q) := by
  set c := Real.sqrt (p / q) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (div_pos hp hq)
  have hc2 : c ^ 2 = p / q := Real.sq_sqrt (div_nonneg hp.le hq.le)
  have hne_c : c ≠ 0 := hc0.ne'
  have hne_p : p ≠ 0 := hp.ne'
  have hne_q : q ≠ 0 := hq.ne'
  -- Change of variables `t = c * u`.
  have hsub :
      ∫ u in Set.Ioi (0 : ℝ), (p + q * (c * u) ^ 2)⁻¹ =
        c⁻¹ * ∫ t in Set.Ioi (0 : ℝ), (p + q * t ^ 2)⁻¹ := by
    simpa [smul_eq_mul, mul_zero] using
      (MeasureTheory.integral_comp_mul_left_Ioi
        (g := fun t : ℝ => (p + q * t ^ 2)⁻¹) (a := (0 : ℝ)) (b := c) hc0)
  have hsimp : ∀ u : ℝ, p + q * (c * u) ^ 2 = p * (1 + u ^ 2) := by
    intro u
    have : q * c ^ 2 = p := by
      rw [hc2]; field_simp [hne_q]
    calc
      p + q * (c * u) ^ 2 = p + q * (c ^ 2 * u ^ 2) := by ring
      _ = p + (q * c ^ 2) * u ^ 2 := by ring
      _ = p + p * u ^ 2 := by rw [this]
      _ = p * (1 + u ^ 2) := by ring
  have hrew :
      ∫ u in Set.Ioi (0 : ℝ), (p + q * (c * u) ^ 2)⁻¹ =
        p⁻¹ * ∫ u in Set.Ioi (0 : ℝ), (1 + u ^ 2)⁻¹ := by
    have : (fun u : ℝ => (p + q * (c * u) ^ 2)⁻¹) =
        (fun u : ℝ => p⁻¹ * (1 + u ^ 2)⁻¹) := by
      funext u
      rw [hsimp u, mul_inv]
    rw [this, MeasureTheory.integral_const_mul]
  rw [hrew, integral_Ioi_inv_one_add_sq_zero] at hsub
  -- `hsub : p⁻¹ * (π / 2) = c⁻¹ * I`
  have hI :
      ∫ t in Set.Ioi (0 : ℝ), (p + q * t ^ 2)⁻¹ = c * (p⁻¹ * (π / 2)) := by
    have := hsub
    field_simp [hne_c] at this ⊢
    linarith
  have hsqrt : c * p⁻¹ = 1 / Real.sqrt (p * q) := by
    have hcq : c = Real.sqrt p / Real.sqrt q := by
      rw [hc, Real.sqrt_div hp.le]
    rw [hcq, Real.sqrt_mul hp.le]
    have hsp : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    have hsq : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    field_simp [hsp, hsq, hne_p]
    exact Real.sq_sqrt hp.le
  have : c * (p⁻¹ * (π / 2)) = (π / 2) / Real.sqrt (p * q) := by
    calc
      c * (p⁻¹ * (π / 2)) = (c * p⁻¹) * (π / 2) := by ring
      _ = (1 / Real.sqrt (p * q)) * (π / 2) := by rw [hsqrt]
      _ = (π / 2) / Real.sqrt (p * q) := by field_simp
  exact hI.trans this

lemma one_add_tan_sq {θ : ℝ} (h : cos θ ≠ 0) :
    1 + tan θ ^ 2 = (cos θ ^ 2)⁻¹ := by
  rw [tan_eq_sin_div_cos, div_pow]
  have hc2 : cos θ ^ 2 ≠ 0 := pow_ne_zero 2 h
  field_simp [h, hc2]
  rw [add_comm, sin_sq_add_cos_sq]

lemma cos_sq_eq_inv_one_add_tan_sq {θ : ℝ} (h : cos θ ≠ 0) :
    cos θ ^ 2 = (1 + tan θ ^ 2)⁻¹ := by
  rw [one_add_tan_sq h, inv_inv]

lemma tan_sq_add_one_sub_A {A θ : ℝ} (hcos : cos θ ≠ 0) :
    tan θ ^ 2 + (1 - A) = (1 - A * cos θ ^ 2) / cos θ ^ 2 := by
  have hc2 : cos θ ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  rw [tan_eq_sin_div_cos, div_pow]
  field_simp [hcos, hc2]
  have hsc : sin θ ^ 2 + cos θ ^ 2 = 1 := sin_sq_add_cos_sq θ
  linarith

lemma one_div_one_sub_A_cos_sq {A θ : ℝ} (hcos : cos θ ≠ 0)
    (hden : 1 - A * cos θ ^ 2 ≠ 0) :
    (1 - A * cos θ ^ 2)⁻¹ =
      (1 + tan θ ^ 2) / (tan θ ^ 2 + (1 - A)) := by
  have hc2 : cos θ ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have hsum : tan θ ^ 2 + (1 - A) ≠ 0 := by
    intro h0
    have := tan_sq_add_one_sub_A (A := A) hcos
    rw [this, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hden h0
    · exact hc2 h0
  have hquot : 1 - A * cos θ ^ 2 =
      (tan θ ^ 2 + (1 - A)) / (1 + tan θ ^ 2) := by
    rw [tan_sq_add_one_sub_A hcos, one_add_tan_sq hcos]
    field_simp [hc2, hden]
  rw [hquot, inv_div]

lemma hasDerivAt_tan_of_lt_pi_div_two {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π / 2) :
    HasDerivAt tan (1 + tan θ ^ 2) θ := by
  have hmem : θ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [pi_div_two_pos], h1⟩
  have h := hasDerivAt_tan_of_mem_Ioo hmem
  have hcos : cos θ ≠ 0 := (cos_pos_of_mem_Ioo hmem).ne'
  have : 1 / cos θ ^ 2 = 1 + tan θ ^ 2 := by
    rw [one_add_tan_sq hcos, one_div]
  rwa [this] at h

lemma continuousOn_tan_Icc {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < π / 2) :
    ContinuousOn tan (Set.uIcc (0 : ℝ) b) := by
  rw [Set.uIcc_of_le hb0]
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hxlt : x < π / 2 := lt_of_le_of_lt hx.2 hb1
  have hmem : x ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [pi_div_two_pos, hx.1], hxlt⟩
  exact (hasDerivAt_tan_of_mem_Ioo hmem).continuousAt

lemma one_sub_A_cos_sq_pos {A θ : ℝ} (hA : A < 1) : 0 < 1 - A * cos θ ^ 2 := by
  have hc : 0 ≤ cos θ ^ 2 := sq_nonneg _
  have hcle : cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  by_cases hA0 : 0 ≤ A
  · have : A * cos θ ^ 2 ≤ A := by
      simpa using mul_le_mul_of_nonneg_left hcle hA0
    linarith
  · have hAneg : A < 0 := lt_of_not_ge hA0
    have : A * cos θ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hAneg.le hc
    linarith

lemma integral_one_div_one_sub_A_cos_sq_partial
    (A : ℝ) (hA : A < 1) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < π / 2) :
    ∫ θ in (0 : ℝ)..b, (1 - A * cos θ ^ 2)⁻¹ =
      ∫ t in (0 : ℝ)..tan b, (t ^ 2 + (1 - A))⁻¹ := by
  have h1A : 0 < 1 - A := sub_pos.mpr hA
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) b, HasDerivAt tan (1 + tan θ ^ 2) θ := by
    intro θ hθ
    rw [Set.uIcc_of_le hb0] at hθ
    exact hasDerivAt_tan_of_lt_pi_div_two hθ.1 (lt_of_le_of_lt hθ.2 hb1)
  have hcontf' : ContinuousOn (fun θ => 1 + tan θ ^ 2) (Set.uIcc (0 : ℝ) b) :=
    continuousOn_const.add ((continuousOn_tan_Icc hb0 hb1).pow 2)
  have hg : Continuous (fun t : ℝ => (t ^ 2 + (1 - A))⁻¹) := by
    refine (continuous_pow 2 |>.add continuous_const).inv₀ ?_
    intro t
    nlinarith [sq_nonneg t, h1A]
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv
      (f := tan) (f' := fun θ => 1 + tan θ ^ 2)
      (g := fun t : ℝ => (t ^ 2 + (1 - A))⁻¹)
      hderiv hcontf' hg
  have hcongr :
      ∫ θ in (0 : ℝ)..b,
          ((fun t : ℝ => (t ^ 2 + (1 - A))⁻¹) ∘ tan) θ * (1 + tan θ ^ 2) =
        ∫ θ in (0 : ℝ)..b, (1 - A * cos θ ^ 2)⁻¹ := by
    refine intervalIntegral.integral_congr ?_
    intro θ hθ
    dsimp
    have hθ' : θ ∈ Set.Icc 0 b := by
      rwa [Set.uIcc_of_le hb0] at hθ
    have hθlt : θ < π / 2 := lt_of_le_of_lt hθ'.2 hb1
    have hmem : θ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [pi_div_two_pos, hθ'.1], hθlt⟩
    have hcos : cos θ ≠ 0 := (cos_pos_of_mem_Ioo hmem).ne'
    have hden : 1 - A * cos θ ^ 2 ≠ 0 := (one_sub_A_cos_sq_pos (θ := θ) hA).ne'
    have hform := one_div_one_sub_A_cos_sq (A := A) (θ := θ) hcos hden
    have : (tan θ ^ 2 + (1 - A))⁻¹ * (1 + tan θ ^ 2) =
        (1 - A * cos θ ^ 2)⁻¹ := by
      rw [hform]
      field_simp
    simpa [Function.comp] using this
  simpa [tan_zero] using hcongr.symm.trans hsub

lemma integrableOn_Ioi_inv_p_add_sq {p : ℝ} (hp : 0 < p) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (p + t ^ 2)⁻¹) (Set.Ioi 0) := by
  have hcont : Continuous (fun t : ℝ => (p + t ^ 2)⁻¹) :=
    (continuous_const.add (continuous_pow 2)).inv₀ (fun t => by nlinarith [sq_nonneg t, hp])
  have h01 : MeasureTheory.IntegrableOn (fun t : ℝ => (p + t ^ 2)⁻¹) (Set.Ioc (0 : ℝ) 1) :=
    hcont.integrableOn_Ioc
  have h1inf : MeasureTheory.IntegrableOn (fun t : ℝ => (p + t ^ 2)⁻¹) (Set.Ioi (1 : ℝ)) := by
    have hint : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((-2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)
    refine hint.mono' hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
    have ht2 : 0 < t ^ 2 := pow_pos ht0 2
    have hle : (p + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ :=
      inv_anti₀ ht2 (by linarith [hp.le])
    have hrpow : (t ^ 2)⁻¹ = t ^ ((-2 : ℝ)) := by
      rw [show (t ^ 2) = (t ^ (2 : ℝ)) by norm_cast]
      exact (Real.rpow_neg ht0.le (2 : ℝ)).symm
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (add_nonneg hp.le (sq_nonneg t)))]
    rwa [hrpow] at hle
  have hunion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    ext t; constructor
    · intro ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · intro h
      rcases h with h | h
      · exact h.1
      · exact lt_trans (by norm_num : (0 : ℝ) < 1) h
  rw [hunion]
  exact h01.union h1inf

lemma continuous_inv_one_sub_A_cos_sq {A : ℝ} (hA : A < 1) :
    Continuous (fun θ : ℝ => (1 - A * cos θ ^ 2)⁻¹) :=
  (continuous_const.sub (continuous_const.mul (continuous_cos.pow 2))).inv₀
    (fun θ => (one_sub_A_cos_sq_pos (θ := θ) hA).ne')

lemma inv_one_sub_A_cos_sq_le {A θ : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    (1 - A * cos θ ^ 2)⁻¹ ≤ (1 - A)⁻¹ := by
  have h1A : 0 < 1 - A := sub_pos.mpr hA
  apply inv_anti₀ h1A
  have : A * cos θ ^ 2 ≤ A := by
    simpa using mul_le_mul_of_nonneg_left (Real.cos_sq_le_one θ) hA0
  linarith

lemma eventually_pos_of_nhdsWithin_pi_div_two :
    ∀ᶠ b in nhdsWithin (π / 2) (Set.Iio (π / 2)), (0 : ℝ) < b := by
  have : Set.Ioi (0 : ℝ) ∈ 𝓝 (π / 2) :=
    Ioi_mem_nhds (by positivity : (0 : ℝ) < π / 2)
  exact mem_of_superset (inter_mem_nhdsWithin _ this) (fun _ hx => hx.2)

lemma Ioo_mem_nhdsWithin_Iio_left {a x : ℝ} (h : a < x) :
    Set.Ioo a x ∈ nhdsWithin x (Set.Iio x) := by
  refine mem_nhdsWithin.mpr ?_
  refine ⟨Set.Ioo a (x + 1), isOpen_Ioo, ⟨h, by linarith⟩, ?_⟩
  intro y hy
  exact ⟨hy.1.1, hy.2⟩

lemma integral_one_div_one_sub_A_cos_sq_half
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    ∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos θ ^ 2)⁻¹ =
      (π / 2) / Real.sqrt (1 - A) := by
  have h1A : 0 < 1 - A := sub_pos.mpr hA
  have hf : Continuous (fun θ : ℝ => (1 - A * cos θ ^ 2)⁻¹) :=
    continuous_inv_one_sub_A_cos_sq hA
  have hgI : MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ 2 + (1 - A))⁻¹) (Set.Ioi 0) := by
    simpa [add_comm (1 - A)] using integrableOn_Ioi_inv_p_add_sq h1A
  let l : Filter ℝ := nhdsWithin (π / 2) (Set.Iio (π / 2))
  have hlimR :
      Filter.Tendsto (fun b : ℝ => ∫ t in (0 : ℝ)..tan b, (t ^ 2 + (1 - A))⁻¹) l
        (nhds (∫ t in Set.Ioi (0 : ℝ), (t ^ 2 + (1 - A))⁻¹)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hgI tendsto_tan_pi_div_two
  have hM : ∀ θ : ℝ, |(1 - A * cos θ ^ 2)⁻¹| ≤ (1 - A)⁻¹ := fun θ => by
    have : 0 ≤ (1 - A * cos θ ^ 2)⁻¹ :=
      inv_nonneg.mpr (one_sub_A_cos_sq_pos (θ := θ) hA).le
    rw [abs_of_nonneg this]
    exact inv_one_sub_A_cos_sq_le hA0 hA
  have hlimL :
      Filter.Tendsto (fun b : ℝ => ∫ θ in (0 : ℝ)..b, (1 - A * cos θ ^ 2)⁻¹) l
        (nhds (∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos θ ^ 2)⁻¹)) := by
    refine Metric.tendsto_nhds.mpr ?_
    intro ε hε
    have hpos : 0 < (1 - A)⁻¹ := inv_pos.mpr h1A
    let δ := ε / ((1 - A)⁻¹ + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hmem : Set.Ioo (π / 2 - δ) (π / 2) ∈ l :=
      Ioo_mem_nhdsWithin_Iio_left (sub_lt_self _ hδ)
    filter_upwards [hmem, eventually_pos_of_nhdsWithin_pi_div_two] with b hb hbpos
    have hb1 : b < π / 2 := hb.2
    have hble : b ≤ π / 2 := hb1.le
    have hsplit :=
      intervalIntegral.integral_add_adjacent_intervals
        (μ := MeasureTheory.volume)
        (hf.intervalIntegrable (0 : ℝ) b) (hf.intervalIntegrable b (π / 2))
    have hdiff :
        (∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos θ ^ 2)⁻¹) -
            ∫ θ in (0 : ℝ)..b, (1 - A * cos θ ^ 2)⁻¹ =
          ∫ θ in b..(π / 2), (1 - A * cos θ ^ 2)⁻¹ := by
      linarith [hsplit]
    have hlen : 0 ≤ π / 2 - b := sub_nonneg.mpr hble
    have habs :
        |∫ θ in b..(π / 2), (1 - A * cos θ ^ 2)⁻¹| ≤ (1 - A)⁻¹ * (π / 2 - b) := by
      have hle :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun θ : ℝ => (1 - A * cos θ ^ 2)⁻¹) (a := b) (b := π / 2)
          (C := (1 - A)⁻¹)
          (fun x _ => by
            rw [Real.norm_eq_abs]
            exact hM x)
      simpa [Real.norm_eq_abs, abs_of_nonneg hlen, mul_comm] using hle
    have hbclose : π / 2 - b < δ := by
      have : π / 2 - δ < b := hb.1
      linarith
    have : |(∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos θ ^ 2)⁻¹) -
        ∫ θ in (0 : ℝ)..b, (1 - A * cos θ ^ 2)⁻¹| < ε := by
      rw [hdiff]
      refine lt_of_le_of_lt habs ?_
      have : (1 - A)⁻¹ * (π / 2 - b) < (1 - A)⁻¹ * δ :=
        mul_lt_mul_of_pos_left hbclose hpos
      refine this.trans ?_
      dsimp [δ]
      have : (1 - A)⁻¹ * (ε / ((1 - A)⁻¹ + 1)) < ε := by
        rw [mul_div_assoc']
        exact (div_lt_iff₀ (by positivity)).mpr (by nlinarith [hpos, hε])
      exact this
    have habs' := this
    rw [abs_sub_comm] at habs'
    simpa [dist_eq_norm, Real.norm_eq_abs] using habs'
  have heq : ∀ᶠ b in l,
      ∫ θ in (0 : ℝ)..b, (1 - A * cos θ ^ 2)⁻¹ =
        ∫ t in (0 : ℝ)..tan b, (t ^ 2 + (1 - A))⁻¹ := by
    filter_upwards [self_mem_nhdsWithin, eventually_pos_of_nhdsWithin_pi_div_two] with b hb hbpos
    exact integral_one_div_one_sub_A_cos_sq_partial A hA b hbpos.le hb
  have hlimL' :
      Filter.Tendsto (fun b : ℝ => ∫ t in (0 : ℝ)..tan b, (t ^ 2 + (1 - A))⁻¹) l
        (nhds (∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos θ ^ 2)⁻¹)) :=
    (Filter.tendsto_congr' heq).1 hlimL
  have hval : ∫ t in Set.Ioi (0 : ℝ), (t ^ 2 + (1 - A))⁻¹ =
      (π / 2) / Real.sqrt (1 - A) := by
    simpa [add_comm (1 - A), mul_one] using
      integral_Ioi_inv_p_add_q_sq h1A (by norm_num : (0 : ℝ) < 1)
  have heq_lim := tendsto_nhds_unique hlimL' hlimR
  rw [heq_lim, hval]

lemma integral_one_div_one_sub_A_cos_sq
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    ∫ θ in (0 : ℝ)..π, (1 - A * cos θ ^ 2)⁻¹ =
      π / Real.sqrt (1 - A) := by
  have hf : Continuous (fun θ : ℝ => (1 - A * cos θ ^ 2)⁻¹) :=
    continuous_inv_one_sub_A_cos_sq hA
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (hf.intervalIntegrable (0 : ℝ) (π / 2)) (hf.intervalIntegrable (π / 2) π)
  have hsub :
      ∫ θ in (π / 2)..π, (1 - A * cos θ ^ 2)⁻¹ =
        ∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos θ ^ 2)⁻¹ := by
    have h1 :=
      intervalIntegral.integral_comp_sub_left
        (fun θ : ℝ => (1 - A * cos θ ^ 2)⁻¹) π
        (a := (0 : ℝ)) (b := π / 2)
    -- h1 : ∫_0^{π/2} f(π-x) = ∫_{π-π/2}^{π-0} f
    have h1' :
        ∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos (π - θ) ^ 2)⁻¹ =
          ∫ θ in (π / 2)..π, (1 - A * cos θ ^ 2)⁻¹ := by
      convert h1 using 2
      · ring
      · ring
    have hcongr :
        ∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos (π - θ) ^ 2)⁻¹ =
          ∫ θ in (0 : ℝ)..(π / 2), (1 - A * cos θ ^ 2)⁻¹ := by
      refine intervalIntegral.integral_congr ?_
      intro θ _
      dsimp
      rw [cos_pi_sub, neg_sq]
    exact (hcongr.symm.trans h1').symm
  rw [← hsplit, hsub, integral_one_div_one_sub_A_cos_sq_half hA0 hA]
  have hsqrt : Real.sqrt (1 - A) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hA)).ne'
  field_simp [hsqrt]
  ring

lemma hasDerivAt_inv_one_sub_A_cos_sq {A θ : ℝ} (hA : A < 1) :
    HasDerivAt (fun a : ℝ => (1 - a * cos θ ^ 2)⁻¹)
      ((cos θ ^ 2) * (1 - A * cos θ ^ 2)⁻¹ ^ 2) A := by
  have hden : 1 - A * cos θ ^ 2 ≠ 0 := (one_sub_A_cos_sq_pos (θ := θ) hA).ne'
  have hlin : HasDerivAt (fun a : ℝ => 1 - a * cos θ ^ 2) (-cos θ ^ 2) A := by
    simpa using
      (hasDerivAt_const A (1 : ℝ) |>.sub ((hasDerivAt_id A).mul_const (cos θ ^ 2)))
  have h := hlin.inv hden
  simpa [neg_neg, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using h

lemma integral_cos_sq_zero :
    ∫ θ in (0 : ℝ)..π, cos θ ^ 2 = π / 2 := by
  have h := integral_cos_pow_two_mul 1
  have hcent : ((1 : ℕ).centralBinom : ℝ) = 2 := by
    simp [Nat.centralBinom]
  have : (4 : ℝ) ^ (1 : ℕ) = 4 := by norm_num
  simpa [hcent, this] using h

lemma rpow_three_halves_one : (1 : ℝ) ^ ((3 : ℝ) / 2) = 1 := by
  simp

lemma rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  have h2 : (3 : ℝ) / 2 = 1 + 1 / 2 := by ring
  rw [h2, Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma hasDerivAt_pi_div_sqrt_one_sub
    {A : ℝ} (hA : A < 1) :
    HasDerivAt (fun a : ℝ => π / Real.sqrt (1 - a))
      (π / (2 * (1 - A) ^ ((3 : ℝ) / 2))) A := by
  have hlin : HasDerivAt (fun a : ℝ => 1 - a) (-1) A := by
    simpa using (hasDerivAt_const A (1 : ℝ)).sub (hasDerivAt_id A)
  have hsqrt : HasDerivAt (fun a : ℝ => Real.sqrt (1 - a))
      ((1 / (2 * Real.sqrt (1 - A))) * (-1)) A :=
    (Real.hasDerivAt_sqrt (sub_pos.mpr hA).ne').comp A hlin
  have hinv := hsqrt.inv ((Real.sqrt_pos.mpr (sub_pos.mpr hA)).ne')
  have hmul := hinv.const_mul π
  have hsA : Real.sqrt (1 - A) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hA)).ne'
  have hrpow := rpow_three_halves (sub_pos.mpr hA)
  convert hmul using 1
  rw [hrpow]
  have h1A : 1 - A ≠ 0 := (sub_pos.mpr hA).ne'
  field_simp [hsA, h1A]
  exact Real.sq_sqrt (sub_pos.mpr hA).le

lemma integral_cos_sq_div_one_sub_A_cos_sq_sq
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    ∫ θ in (0 : ℝ)..π, cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2 =
      π / (2 * (1 - A) ^ ((3 : ℝ) / 2)) := by
  by_cases hAz : A = 0
  · subst hAz
    have hcongr :
        ∫ θ in (0 : ℝ)..π, cos θ ^ 2 * (1 - (0 : ℝ) * cos θ ^ 2)⁻¹ ^ 2 =
          ∫ θ in (0 : ℝ)..π, cos θ ^ 2 := by
      refine intervalIntegral.integral_congr ?_
      intro θ _
      simp
    rw [hcongr, integral_cos_sq_zero, sub_zero, rpow_three_halves_one]
    ring
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
    -- stay inside `{a | 0 < a < 1}` so `integral_one_div_one_sub_A_cos_sq` applies
    let s : Set ℝ := Set.Ioo (A / 2) ((A + 1) / 2)
    have hs : s ∈ 𝓝 A := by
      refine Ioo_mem_nhds ?_ ?_
      · linarith
      · linarith
    have hsA : ∀ a ∈ s, a < 1 := by
      intro a ha
      linarith [ha.2]
    have hsA0 : ∀ a ∈ s, 0 ≤ a := by
      intro a ha
      linarith [ha.1, hApos]
    have hF_meas : ∀ᶠ a in 𝓝 A,
        MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (1 - a * cos θ ^ 2)⁻¹)
          (MeasureTheory.volume.restrict (Set.uIoc 0 π)) := by
      filter_upwards [hs] with a ha
      have : Continuous (fun θ : ℝ => (1 - a * cos θ ^ 2)⁻¹) :=
        continuous_inv_one_sub_A_cos_sq (hsA a ha)
      exact this.aestronglyMeasurable.restrict
    have hF_int : IntervalIntegrable (fun θ : ℝ => (1 - A * cos θ ^ 2)⁻¹)
        MeasureTheory.volume 0 π :=
      (continuous_inv_one_sub_A_cos_sq hA).intervalIntegrable _ _
    have hF'cont : Continuous
        (fun θ : ℝ => cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2) :=
      (continuous_cos.pow 2).mul
        (((continuous_inv_one_sub_A_cos_sq hA).pow 2))
    have hF'_meas :
        MeasureTheory.AEStronglyMeasurable
          (fun θ : ℝ => cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2)
          (MeasureTheory.volume.restrict (Set.uIoc 0 π)) :=
      hF'cont.aestronglyMeasurable.restrict
    let bound : ℝ → ℝ := fun _ => (1 - (A + 1) / 2)⁻¹ ^ 2
    have hbound : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc 0 π →
        ∀ a ∈ s, ‖cos t ^ 2 * (1 - a * cos t ^ 2)⁻¹ ^ 2‖ ≤ bound t := by
      refine MeasureTheory.ae_of_all _ ?_
      intro t _ht a ha
      have ha1 : a < 1 := hsA a ha
      have ha0 : 0 ≤ a := hsA0 a ha
      have hpos : 0 < 1 - a * cos t ^ 2 := one_sub_A_cos_sq_pos (θ := t) ha1
      have hcos : cos t ^ 2 ≤ 1 := Real.cos_sq_le_one t
      have hineq : (1 - a * cos t ^ 2)⁻¹ ≤ (1 - (A + 1) / 2)⁻¹ := by
        have : 1 - (A + 1) / 2 ≤ 1 - a * cos t ^ 2 := by
          have : a * cos t ^ 2 ≤ (A + 1) / 2 :=
            (mul_le_of_le_one_right ha0 hcos).trans ha.2.le
          linarith
        exact inv_anti₀ (by linarith) this
      have hnn : 0 ≤ cos t ^ 2 * (1 - a * cos t ^ 2)⁻¹ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have : cos t ^ 2 * (1 - a * cos t ^ 2)⁻¹ ^ 2 ≤
          (1 - a * cos t ^ 2)⁻¹ ^ 2 :=
        mul_le_of_le_one_left (sq_nonneg _) hcos
      refine this.trans ?_
      exact pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hineq 2
    have bound_int : IntervalIntegrable bound MeasureTheory.volume 0 π :=
      Continuous.intervalIntegrable continuous_const _ _
    have hdiff : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc 0 π → ∀ a ∈ s,
        HasDerivAt (fun x : ℝ => (1 - x * cos t ^ 2)⁻¹)
          (cos t ^ 2 * (1 - a * cos t ^ 2)⁻¹ ^ 2) a := by
      refine MeasureTheory.ae_of_all _ ?_
      intro t _ht a ha
      exact hasDerivAt_inv_one_sub_A_cos_sq (hsA a ha)
    have hder :=
      intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := π)
        (F := fun a θ => (1 - a * cos θ ^ 2)⁻¹)
        (F' := fun a θ => cos θ ^ 2 * (1 - a * cos θ ^ 2)⁻¹ ^ 2)
        (bound := bound) (x₀ := A) (s := s)
        hs hF_meas hF_int hF'_meas hbound bound_int hdiff
    have hclosed := hasDerivAt_pi_div_sqrt_one_sub hA
    have hfun :
        (fun a : ℝ => ∫ θ in (0 : ℝ)..π, (1 - a * cos θ ^ 2)⁻¹) =ᶠ[𝓝 A]
          fun a => π / Real.sqrt (1 - a) := by
      filter_upwards [hs] with a ha
      exact integral_one_div_one_sub_A_cos_sq (hsA0 a ha) (hsA a ha)
    have hder' :
        HasDerivAt (fun a : ℝ => π / Real.sqrt (1 - a))
          (∫ θ in (0 : ℝ)..π, cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2) A :=
      hder.2.congr_of_eventuallyEq hfun.symm
    exact HasDerivAt.unique hder' hclosed

lemma one_div_sq_eq_one_div_add_A_cos_sq {A θ : ℝ} :
    (1 - A * cos θ ^ 2)⁻¹ ^ 2 =
      (1 - A * cos θ ^ 2)⁻¹ + A * cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2 := by
  by_cases h : 1 - A * cos θ ^ 2 = 0
  · simp [h]
  · field_simp [h]
    ring

lemma integral_one_div_one_sub_A_cos_sq_sq
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    ∫ θ in (0 : ℝ)..π, (1 - A * cos θ ^ 2)⁻¹ ^ 2 =
      π * (2 - A) / (2 * (1 - A) ^ ((3 : ℝ) / 2)) := by
  have hf : Continuous (fun θ : ℝ => (1 - A * cos θ ^ 2)⁻¹) :=
    continuous_inv_one_sub_A_cos_sq hA
  have hg : Continuous (fun θ : ℝ => A * (cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2)) :=
    continuous_const.mul ((continuous_cos.pow 2).mul (hf.pow 2))
  have hcongr :
      ∫ θ in (0 : ℝ)..π, (1 - A * cos θ ^ 2)⁻¹ ^ 2 =
        ∫ θ in (0 : ℝ)..π,
          ((1 - A * cos θ ^ 2)⁻¹ +
            A * (cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2)) := by
    refine intervalIntegral.integral_congr ?_
    intro θ _
    simpa [mul_assoc] using one_div_sq_eq_one_div_add_A_cos_sq (A := A) (θ := θ)
  rw [hcongr, intervalIntegral.integral_add
      (hf.intervalIntegrable (0 : ℝ) π) (hg.intervalIntegrable (0 : ℝ) π)]
  have hmul :
      ∫ θ in (0 : ℝ)..π, A * (cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2) =
        A * ∫ θ in (0 : ℝ)..π, cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2 :=
    intervalIntegral.integral_const_mul A _
  rw [hmul, integral_one_div_one_sub_A_cos_sq hA0 hA,
    integral_cos_sq_div_one_sub_A_cos_sq_sq hA0 hA]
  have h1A : 0 < 1 - A := sub_pos.mpr hA
  have hs : Real.sqrt (1 - A) ≠ 0 := (Real.sqrt_pos.mpr h1A).ne'
  have hr := rpow_three_halves h1A
  rw [hr]
  field_simp [hs, h1A.ne']
  ring

lemma integral_magic_theta
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    ∫ θ in (0 : ℝ)..π,
        (367 + 3923 * A * cos θ ^ 2) * (1 - A * cos θ ^ 2)⁻¹ ^ 2 =
      π * (367 + 1778 * A) / (1 - A) ^ ((3 : ℝ) / 2) := by
  have hf : Continuous (fun θ : ℝ => (1 - A * cos θ ^ 2)⁻¹ ^ 2) :=
    (continuous_inv_one_sub_A_cos_sq hA).pow 2
  have hg : Continuous
      (fun θ : ℝ => (3923 * A) * (cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2)) :=
    continuous_const.mul ((continuous_cos.pow 2).mul hf)
  have hcongr :
      ∫ θ in (0 : ℝ)..π,
          (367 + 3923 * A * cos θ ^ 2) * (1 - A * cos θ ^ 2)⁻¹ ^ 2 =
        ∫ θ in (0 : ℝ)..π,
          (367 * (1 - A * cos θ ^ 2)⁻¹ ^ 2 +
            (3923 * A) * (cos θ ^ 2 * (1 - A * cos θ ^ 2)⁻¹ ^ 2)) := by
    refine intervalIntegral.integral_congr ?_
    intro θ _; ring
  rw [hcongr, intervalIntegral.integral_add
      ((continuous_const.mul hf).intervalIntegrable (0 : ℝ) π)
      (hg.intervalIntegrable (0 : ℝ) π),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_one_div_one_sub_A_cos_sq_sq hA0 hA,
    integral_cos_sq_div_one_sub_A_cos_sq_sq hA0 hA]
  have h1A : 0 < 1 - A := sub_pos.mpr hA
  have hs : Real.sqrt (1 - A) ≠ 0 := (Real.sqrt_pos.mpr h1A).ne'
  have hr := rpow_three_halves h1A
  rw [hr]
  field_simp [hs, h1A.ne']
  ring

lemma A_of_uv_nonneg (u v : ℝ) :
    0 ≤ (7 + cos u) * (17 + 8 * cos v) / 392 := by
  have h1 : 0 ≤ 7 + cos u := by linarith [neg_one_le_cos u]
  have h2 : 0 ≤ 17 + 8 * cos v := by nlinarith [neg_one_le_cos v]
  positivity

lemma A_of_uv_lt_one (u v : ℝ) :
    (7 + cos u) * (17 + 8 * cos v) / 392 < 1 := by
  have hu : 7 + cos u ≤ 8 := by linarith [cos_le_one u]
  have hv : 17 + 8 * cos v ≤ 25 := by nlinarith [cos_le_one v]
  have h1 : 0 ≤ 7 + cos u := by linarith [neg_one_le_cos u]
  have h2 : 0 ≤ 17 + 8 * cos v := by nlinarith [neg_one_le_cos v]
  have hprod : (7 + cos u) * (17 + 8 * cos v) ≤ 8 * 25 :=
    mul_le_mul hu hv h2 (by norm_num)
  have : (7 + cos u) * (17 + 8 * cos v) / 392 ≤ (200 : ℝ) / 392 := by
    have : (8 : ℝ) * 25 = 200 := by norm_num
    nlinarith
  have : (200 : ℝ) / 392 < 1 := by norm_num
  linarith

lemma lam_le_r (θ u v : ℝ) : lam θ u v ≤ (200 : ℝ) / 392 := by
  have hcos : cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have hu : 7 + cos u ≤ 8 := by linarith [cos_le_one u]
  have hv : 17 + 8 * cos v ≤ 25 := by nlinarith [cos_le_one v]
  have h2 : 0 ≤ 7 + cos u := by linarith [neg_one_le_cos u]
  have h3 : 0 ≤ 17 + 8 * cos v := by nlinarith [neg_one_le_cos v]
  have hprod : cos θ ^ 2 * (7 + cos u) * (17 + 8 * cos v) ≤ 1 * 8 * 25 := by
    have : cos θ ^ 2 * (7 + cos u) ≤ 1 * 8 :=
      mul_le_mul hcos hu h2 (by norm_num)
    exact mul_le_mul this hv h3 (by norm_num)
  unfold lam
  have : (8 : ℝ) * 25 = 200 := by norm_num
  nlinarith

lemma r200 : (200 : ℝ) / 392 < 1 := by norm_num

lemma summable_geom_bound :
    Summable fun k : ℕ => (4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k := by
  have hr : ‖(200 : ℝ) / 392‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 200 / 392)]
    exact r200
  have h1 : Summable fun k : ℕ => (k : ℝ) * ((200 : ℝ) / 392) ^ k := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (k := 1) (r := (200 : ℝ) / 392) hr)
  have h0 : Summable fun k : ℕ => ((200 : ℝ) / 392) ^ k :=
    summable_geometric_of_norm_lt_one hr
  have := (h1.mul_left (4290 : ℝ)).add (h0.mul_left (367 : ℝ))
  convert this using 1
  ext k; ring

lemma term_factor_nonneg (k : ℕ) : 0 ≤ 4290 * (k : ℝ) + 367 := by
  positivity

lemma continuous_lam_in_v (θ u : ℝ) : Continuous (fun v : ℝ => lam θ u v) := by
  unfold lam
  exact ((continuous_const.mul continuous_const).mul
    (continuous_const.add (continuous_const.mul continuous_cos))).div_const _

lemma continuous_lam_pow (k : ℕ) (θ u : ℝ) :
    Continuous (fun v : ℝ => (4290 * (k : ℝ) + 367) * lam θ u v ^ k) :=
  continuous_const.mul ((continuous_lam_in_v θ u).pow k)

lemma interval_eq_Ioc (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..π, f x = ∫ x in Set.Ioc (0 : ℝ) π, f x :=
  intervalIntegral.integral_of_le pi_pos.le

/-- Interchange `∑` and `∫_0^π` for a nonnegative family dominated by a summable sequence. -/
lemma tsum_interval_of_bound
    (g : ℕ → ℝ → ℝ) (b : ℕ → ℝ)
    (hcont : ∀ k, Continuous (g k))
    (hnn : ∀ k x, 0 ≤ g k x)
    (hbd : ∀ k x, g k x ≤ b k)
    (hsum : Summable b) (hb0 : ∀ k, 0 ≤ b k) :
    (∑' k : ℕ, ∫ x in (0 : ℝ)..π, g k x) =
      ∫ x in (0 : ℝ)..π, ∑' k : ℕ, g k x := by
  have hIoc : ∀ k,
      ∫ x in (0 : ℝ)..π, g k x = ∫ x in Set.Ioc (0 : ℝ) π, g k x :=
    fun k => interval_eq_Ioc (g k)
  simp_rw [hIoc]
  have hint : ∀ k, MeasureTheory.Integrable (g k)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) π)) :=
    fun k => (hcont k).integrableOn_Ioc.integrable
  have hsum' : Summable fun k : ℕ =>
      ∫ x in Set.Ioc (0 : ℝ) π, ‖g k x‖ := by
    refine Summable.of_nonneg_of_le
      (fun _ => MeasureTheory.integral_nonneg fun _ => norm_nonneg _) ?_
      (hsum.mul_right π)
    intro k
    have : ∫ x in Set.Ioc (0 : ℝ) π, ‖g k x‖ ≤ (b k) * π := by
      have hbd' : ∀ x ∈ Set.Ioc (0 : ℝ) π, ‖g k x‖ ≤ b k := by
        intro x _
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn k x)]
        exact hbd k x
      have hle :=
        MeasureTheory.setIntegral_mono_on (hint k).norm
          (continuous_const.integrableOn_Ioc) measurableSet_Ioc hbd'
      have hvol : ∫ x in Set.Ioc (0 : ℝ) π, b k = b k * π := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul]
        have hvolπ : MeasureTheory.volume.real (Set.Ioc (0 : ℝ) π) = π := by
          simp [pi_pos.le]
        rw [hvolπ, mul_comm]
      exact hle.trans_eq hvol
    exact this
  have := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum'
  rw [this, ← interval_eq_Ioc]

lemma integrand_nonneg (k : ℕ) (θ u v : ℝ) :
    0 ≤ (4290 * (k : ℝ) + 367) * lam θ u v ^ k :=
  mul_nonneg (term_factor_nonneg k) (pow_nonneg (lam_nonneg θ u v) k)

lemma integrand_le_bound (k : ℕ) (θ u v : ℝ) :
    (4290 * (k : ℝ) + 367) * lam θ u v ^ k ≤
      (4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k :=
  mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (lam_nonneg θ u v) (lam_le_r θ u v) k)
    (term_factor_nonneg k)

lemma bound_nonneg (k : ℕ) :
    0 ≤ (4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k :=
  mul_nonneg (term_factor_nonneg k) (pow_nonneg (by norm_num) k)

lemma continuous_integrand_v (k : ℕ) (θ u : ℝ) :
    Continuous (fun v : ℝ => (4290 * (k : ℝ) + 367) * lam θ u v ^ k) :=
  continuous_lam_pow k θ u

lemma continuous_lam : Continuous (fun p : ℝ × ℝ × ℝ => lam p.1 p.2.1 p.2.2) := by
  unfold lam
  fun_prop

lemma continuous_integrand_uncurry_v (k : ℕ) (θ : ℝ) :
    Continuous (fun p : ℝ × ℝ => (4290 * (k : ℝ) + 367) * lam θ p.1 p.2 ^ k) :=
  continuous_const.mul
    ((continuous_lam.comp
      (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))).pow k)

lemma continuous_inner_v (k : ℕ) (θ : ℝ) :
    Continuous (fun u : ℝ =>
      ∫ v in (0 : ℝ)..π, (4290 * (k : ℝ) + 367) * lam θ u v ^ k) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_integrand_uncurry_v k θ) 0 π

lemma continuous_integrand_uncurry_u (k : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      ∫ v in (0 : ℝ)..π, (4290 * (k : ℝ) + 367) * lam p.1 p.2 v ^ k) := by
  have hf : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      (4290 * (k : ℝ) + 367) * lam q.1.1 q.1.2 q.2 ^ k) :=
    continuous_const.mul
      ((continuous_lam.comp
        ((continuous_fst.comp continuous_fst).prodMk
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd))).pow k)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 π

lemma continuous_inner_u (k : ℕ) :
    Continuous (fun θ : ℝ =>
      ∫ u in (0 : ℝ)..π, ∫ v in (0 : ℝ)..π,
        (4290 * (k : ℝ) + 367) * lam θ u v ^ k) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_integrand_uncurry_u k) 0 π

lemma tsum_triple_integral_lam :
    (∑' k : ℕ,
        ∫ θ in (0 : ℝ)..π,
          ∫ u in (0 : ℝ)..π,
            ∫ v in (0 : ℝ)..π,
              (4290 * (k : ℝ) + 367) * lam θ u v ^ k) =
      ∫ θ in (0 : ℝ)..π,
        ∫ u in (0 : ℝ)..π,
          ∫ v in (0 : ℝ)..π,
            ∑' k : ℕ, (4290 * (k : ℝ) + 367) * lam θ u v ^ k := by
  have hinner : ∀ (θ u : ℝ),
      (∑' k : ℕ, ∫ v in (0 : ℝ)..π,
          (4290 * (k : ℝ) + 367) * lam θ u v ^ k) =
        ∫ v in (0 : ℝ)..π,
          ∑' k : ℕ, (4290 * (k : ℝ) + 367) * lam θ u v ^ k := by
    intro θ u
    exact tsum_interval_of_bound
      (fun k v => (4290 * (k : ℝ) + 367) * lam θ u v ^ k)
      (fun k => (4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k)
      (fun k => continuous_integrand_v k θ u)
      (fun k v => integrand_nonneg k θ u v)
      (fun k v => integrand_le_bound k θ u v)
      summable_geom_bound bound_nonneg
  have hinter_le : ∀ (k : ℕ) (θ u : ℝ),
      ∫ v in (0 : ℝ)..π, (4290 * (k : ℝ) + 367) * lam θ u v ^ k ≤
        ((4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k) * π := by
    intro k θ u
    have := integral_le_const_mul_length (a := (0 : ℝ)) (b := π) pi_pos.le
      (continuous_integrand_v k θ u)
      (fun v _ _ => integrand_le_bound k θ u v)
    simpa [sub_zero] using this
  have hmid : ∀ θ : ℝ,
      (∑' k : ℕ, ∫ u in (0 : ℝ)..π, ∫ v in (0 : ℝ)..π,
          (4290 * (k : ℝ) + 367) * lam θ u v ^ k) =
        ∫ u in (0 : ℝ)..π, ∫ v in (0 : ℝ)..π,
          ∑' k : ℕ, (4290 * (k : ℝ) + 367) * lam θ u v ^ k := by
    intro θ
    have h1 := tsum_interval_of_bound
      (fun k u => ∫ v in (0 : ℝ)..π,
          (4290 * (k : ℝ) + 367) * lam θ u v ^ k)
      (fun k => ((4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k) * π)
      (fun k => continuous_inner_v k θ)
      (fun k u => intervalIntegral.integral_nonneg pi_pos.le
        (fun v _ => integrand_nonneg k θ u v))
      (fun k u => hinter_le k θ u)
      (summable_geom_bound.mul_right π)
      (fun k => mul_nonneg (bound_nonneg k) pi_pos.le)
    rw [h1]
    refine intervalIntegral.integral_congr ?_
    intro u _; exact hinner θ u
  have hdouble_le : ∀ (k : ℕ) (θ : ℝ),
      ∫ u in (0 : ℝ)..π, ∫ v in (0 : ℝ)..π,
          (4290 * (k : ℝ) + 367) * lam θ u v ^ k ≤
        ((4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k) * π * π := by
    intro k θ
    have h1 :
        ∫ u in (0 : ℝ)..π, ∫ v in (0 : ℝ)..π,
            (4290 * (k : ℝ) + 367) * lam θ u v ^ k ≤
          ∫ u in (0 : ℝ)..π,
            ((4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k) * π := by
      refine intervalIntegral.integral_mono_on pi_pos.le ?_ ?_ ?_
      · exact (continuous_inner_v k θ).intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro u _; exact hinter_le k θ u
    have h2 :
        ∫ u in (0 : ℝ)..π,
            ((4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k) * π =
          ((4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k) * π * π := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm π]
    exact h1.trans_eq h2
  have houter := tsum_interval_of_bound
    (fun k θ => ∫ u in (0 : ℝ)..π, ∫ v in (0 : ℝ)..π,
        (4290 * (k : ℝ) + 367) * lam θ u v ^ k)
    (fun k => ((4290 * (k : ℝ) + 367) * ((200 : ℝ) / 392) ^ k) * π * π)
    (fun k => continuous_inner_u k)
    (fun k θ => intervalIntegral.integral_nonneg pi_pos.le
      (fun u _ => intervalIntegral.integral_nonneg pi_pos.le
        (fun v _ => integrand_nonneg k θ u v)))
    (fun k θ => hdouble_le k θ)
    ((summable_geom_bound.mul_right π).mul_right π)
    (fun k => mul_nonneg (mul_nonneg (bound_nonneg k) pi_pos.le) pi_pos.le)
  rw [houter]
  refine intervalIntegral.integral_congr ?_
  intro θ _; exact hmid θ

lemma tsum_eq_triple_of_closed :
    (∑' k : ℕ, t k) =
      (1 / π ^ 3) *
        ∫ θ in (0 : ℝ)..π,
          ∫ u in (0 : ℝ)..π,
            ∫ v in (0 : ℝ)..π,
              (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 := by
  have hfun : t = fun k : ℕ =>
      (1 / π ^ 3) *
        ∫ θ in (0 : ℝ)..π,
          ∫ u in (0 : ℝ)..π,
            ∫ v in (0 : ℝ)..π,
              (4290 * (k : ℝ) + 367) * lam θ u v ^ k := by
    funext k; exact t_eq_triple_integral k
  rw [hfun, tsum_mul_left, tsum_triple_integral_lam]
  refine congrArg _ ?_
  refine intervalIntegral.integral_congr ?_
  intro θ _
  refine intervalIntegral.integral_congr ?_
  intro u _
  refine intervalIntegral.integral_congr ?_
  intro v _
  exact tsum_linear_geometric (lam_nonneg θ u v) (lam_lt_one θ u v)

set_option maxHeartbeats 800000

lemma one_sub_lam_ne_zero (θ u v : ℝ) : 1 - lam θ u v ≠ 0 :=
  (sub_pos.mpr (lam_lt_one θ u v)).ne'

lemma continuous_closed_integrand :
    Continuous fun p : ℝ × ℝ × ℝ =>
      (367 + 3923 * lam p.1 p.2.1 p.2.2) / (1 - lam p.1 p.2.1 p.2.2) ^ 2 := by
  have hden : ∀ p : ℝ × ℝ × ℝ, 1 - lam p.1 p.2.1 p.2.2 ≠ 0 := fun p =>
    one_sub_lam_ne_zero _ _ _
  unfold lam
  fun_prop (disch := intro p; exact pow_ne_zero 2 (hden p))

/-- Swap two nested integrals over `[0, π]` of a jointly continuous integrand. -/
lemma intervalIntegral_swap_of_continuous {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    ∫ x in (0 : ℝ)..π, ∫ y in (0 : ℝ)..π, f x y =
      ∫ y in (0 : ℝ)..π, ∫ x in (0 : ℝ)..π, f x y := by
  have hIoc : ∀ g : ℝ → ℝ,
      ∫ t in (0 : ℝ)..π, g t = ∫ t in Set.Ioc (0 : ℝ) π, g t :=
    fun g => intervalIntegral.integral_of_le pi_pos.le
  simp_rw [hIoc]
  have hInt : MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) π)).prod
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) π))) := by
    rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    have hK : IsCompact (Set.Icc (0 : ℝ) π ×ˢ Set.Icc (0 : ℝ) π) :=
      isCompact_Icc.prod isCompact_Icc
    have hOn : MeasureTheory.IntegrableOn (Function.uncurry f)
        (Set.Icc (0 : ℝ) π ×ˢ Set.Icc (0 : ℝ) π) :=
      hf.continuousOn.integrableOn_compact hK
    exact hOn.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  simpa using MeasureTheory.integral_integral_swap hInt

lemma continuous_closed_uncurry_uv (θ : ℝ) :
    Continuous fun p : ℝ × ℝ =>
      (367 + 3923 * lam θ p.1 p.2) / (1 - lam θ p.1 p.2) ^ 2 := by
  have hden : ∀ p : ℝ × ℝ, 1 - lam θ p.1 p.2 ≠ 0 := fun p =>
    one_sub_lam_ne_zero _ _ _
  unfold lam
  fun_prop (disch := intro p; exact pow_ne_zero 2 (hden p))

lemma continuous_closed_uncurry_θv (u : ℝ) :
    Continuous fun p : ℝ × ℝ =>
      (367 + 3923 * lam p.1 u p.2) / (1 - lam p.1 u p.2) ^ 2 := by
  have hden : ∀ p : ℝ × ℝ, 1 - lam p.1 u p.2 ≠ 0 := fun p =>
    one_sub_lam_ne_zero _ _ _
  unfold lam
  fun_prop (disch := intro p; exact pow_ne_zero 2 (hden p))

lemma continuous_closed_uncurry_θ_of_inner :
    Continuous fun p : ℝ × ℝ =>
      ∫ v in (0 : ℝ)..π,
        (367 + 3923 * lam p.1 p.2 v) / (1 - lam p.1 p.2 v) ^ 2 := by
  have hf : Continuous fun q : (ℝ × ℝ) × ℝ =>
      (367 + 3923 * lam q.1.1 q.1.2 q.2) / (1 - lam q.1.1 q.1.2 q.2) ^ 2 := by
    have hden : ∀ q : (ℝ × ℝ) × ℝ, 1 - lam q.1.1 q.1.2 q.2 ≠ 0 := fun q =>
      one_sub_lam_ne_zero _ _ _
    unfold lam
    fun_prop (disch := intro q; exact pow_ne_zero 2 (hden q))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 π

lemma triple_to_double :
    ∫ θ in (0 : ℝ)..π,
        ∫ u in (0 : ℝ)..π,
          ∫ v in (0 : ℝ)..π,
            (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 =
      π *
        ∫ u in (0 : ℝ)..π,
          ∫ v in (0 : ℝ)..π,
            (367 + 1778 * ((7 + cos u) * (17 + 8 * cos v) / 392)) /
              (1 - (7 + cos u) * (17 + 8 * cos v) / 392) ^ ((3 : ℝ) / 2) := by
  -- pull the θ-integral inside and apply `integral_magic_theta`
  have hswap :
      ∫ θ in (0 : ℝ)..π,
          ∫ u in (0 : ℝ)..π,
            ∫ v in (0 : ℝ)..π,
              (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 =
        ∫ u in (0 : ℝ)..π,
          ∫ v in (0 : ℝ)..π,
            ∫ θ in (0 : ℝ)..π,
              (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 := by
    have h1 :
        ∫ θ in (0 : ℝ)..π,
            ∫ u in (0 : ℝ)..π,
              ∫ v in (0 : ℝ)..π,
                (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 =
          ∫ u in (0 : ℝ)..π,
            ∫ θ in (0 : ℝ)..π,
              ∫ v in (0 : ℝ)..π,
                (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 :=
      intervalIntegral_swap_of_continuous continuous_closed_uncurry_θ_of_inner
    rw [h1]
    refine intervalIntegral.integral_congr ?_
    intro u _
    exact intervalIntegral_swap_of_continuous (continuous_closed_uncurry_θv u)
  rw [hswap]
  -- evaluate the inner θ-integral pointwise, then pull out the constant `π`
  have hpoint : ∀ u v : ℝ,
      ∫ θ in (0 : ℝ)..π,
          (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 =
        π * ((367 + 1778 * ((7 + cos u) * (17 + 8 * cos v) / 392)) /
          (1 - (7 + cos u) * (17 + 8 * cos v) / 392) ^ ((3 : ℝ) / 2)) := by
    intro u v
    have hA0 := A_of_uv_nonneg u v
    have hA := A_of_uv_lt_one u v
    have hθ :
        ∫ θ in (0 : ℝ)..π,
            (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 =
          ∫ θ in (0 : ℝ)..π,
            (367 + 3923 * ((7 + cos u) * (17 + 8 * cos v) / 392) * cos θ ^ 2) *
              (1 - ((7 + cos u) * (17 + 8 * cos v) / 392) * cos θ ^ 2)⁻¹ ^ 2 := by
      refine intervalIntegral.integral_congr ?_
      intro θ _
      unfold lam
      field_simp
      try ring
    rw [hθ, integral_magic_theta hA0 hA]
    ring
  have hcongr :
      ∫ u in (0 : ℝ)..π,
          ∫ v in (0 : ℝ)..π,
            ∫ θ in (0 : ℝ)..π,
              (367 + 3923 * lam θ u v) / (1 - lam θ u v) ^ 2 =
        ∫ u in (0 : ℝ)..π,
          ∫ v in (0 : ℝ)..π,
            π * ((367 + 1778 * ((7 + cos u) * (17 + 8 * cos v) / 392)) /
              (1 - (7 + cos u) * (17 + 8 * cos v) / 392) ^ ((3 : ℝ) / 2)) := by
    refine intervalIntegral.integral_congr ?_
    intro u _
    refine intervalIntegral.integral_congr ?_
    intro v _
    exact hpoint u v
  rw [hcongr]
  have hinner : ∀ u : ℝ,
      ∫ v in (0 : ℝ)..π,
          π * ((367 + 1778 * ((7 + cos u) * (17 + 8 * cos v) / 392)) /
            (1 - (7 + cos u) * (17 + 8 * cos v) / 392) ^ ((3 : ℝ) / 2)) =
        π * ∫ v in (0 : ℝ)..π,
          (367 + 1778 * ((7 + cos u) * (17 + 8 * cos v) / 392)) /
            (1 - (7 + cos u) * (17 + 8 * cos v) / 392) ^ ((3 : ℝ) / 2) :=
    fun u => intervalIntegral.integral_const_mul π _
  simp_rw [hinner, intervalIntegral.integral_const_mul]

/-- The parameter `A(u,v)` appearing in the remaining double integral. -/
noncomputable def Auv (u v : ℝ) : ℝ :=
  (7 + cos u) * (17 + 8 * cos v) / 392

lemma Auv_eq (u v : ℝ) : Auv u v = (7 + cos u) * (17 + 8 * cos v) / 392 := rfl

lemma Auv_nonneg (u v : ℝ) : 0 ≤ Auv u v := A_of_uv_nonneg u v

lemma Auv_lt_one (u v : ℝ) : Auv u v < 1 := A_of_uv_lt_one u v

lemma Auv_lt_one' (u v : ℝ) : 0 < 1 - Auv u v :=
  sub_pos.mpr (Auv_lt_one u v)

/-- Algebraic splitting of the remaining integrand. -/
lemma integrand_A_split {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    (367 + 1778 * A) / (1 - A) ^ ((3 : ℝ) / 2) =
      2145 * (1 - A) ^ (-((3 : ℝ) / 2)) - 1778 * (1 - A) ^ (-((1 : ℝ) / 2)) := by
  have h1 : 0 < 1 - A := sub_pos.mpr hA
  have hpos : 0 < (1 - A) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos h1 _
  have hne : (1 - A) ^ ((3 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos h1 _).ne'
  have hhalf : (1 - A) ^ ((3 : ℝ) / 2) = (1 - A) ^ ((1 : ℝ) / 2) * (1 - A) := by
    have := Real.rpow_add h1 ((1 : ℝ) / 2) (1 : ℝ)
    rw [show (1 : ℝ) / 2 + 1 = (3 : ℝ) / 2 by norm_num] at this
    rw [this, Real.rpow_one]
  -- (1-A)^{-3/2} = 1 / (1-A)^{3/2}, (1-A)^{-1/2} = 1 / (1-A)^{1/2}
  have hinv3 : (1 - A) ^ (-((3 : ℝ) / 2)) = ((1 - A) ^ ((3 : ℝ) / 2))⁻¹ :=
    Real.rpow_neg h1.le _
  have hinv1 : (1 - A) ^ (-((1 : ℝ) / 2)) = ((1 - A) ^ ((1 : ℝ) / 2))⁻¹ :=
    Real.rpow_neg h1.le _
  rw [hinv3, hinv1]
  have : 2145 * ((1 - A) ^ ((3 : ℝ) / 2))⁻¹ - 1778 * ((1 - A) ^ ((1 : ℝ) / 2))⁻¹ =
      (2145 - 1778 * (1 - A)) / (1 - A) ^ ((3 : ℝ) / 2) := by
    field_simp [hne, hpos.ne']
    rw [hhalf]
    ring
  rw [this]
  have : 2145 - 1778 * (1 - A) = 367 + 1778 * A := by ring
  rw [this]

/-- Half-angle form of `7 + cos (2a)`. -/
lemma seven_add_cos_two (a : ℝ) : 7 + cos (2 * a) = 8 - 2 * sin a ^ 2 := by
  have h : cos a ^ 2 = 1 - sin a ^ 2 := by
    linarith [sin_sq_add_cos_sq a]
  rw [cos_two_mul, h]
  ring

/-- Half-angle form of `17 + 8 cos (2b)`. -/
lemma seventeen_add_eight_cos_two (b : ℝ) :
    17 + 8 * cos (2 * b) = 25 - 16 * sin b ^ 2 := by
  have h : cos b ^ 2 = 1 - sin b ^ 2 := by
    linarith [sin_sq_add_cos_sq b]
  rw [cos_two_mul, h]
  ring

/-- The quadratic form appearing after the half-angle substitution. -/
noncomputable def DeltaAB (a b : ℝ) : ℝ :=
  96 + 25 * sin a ^ 2 + 64 * sin b ^ 2 - 16 * sin a ^ 2 * sin b ^ 2

lemma DeltaAB_pos (a b : ℝ) : 0 < DeltaAB a b := by
  have hs : 0 ≤ sin a ^ 2 := sq_nonneg _
  have ht : 0 ≤ sin b ^ 2 := sq_nonneg _
  have hs1 : sin a ^ 2 ≤ 1 := Real.sin_sq_le_one a
  have ht1 : sin b ^ 2 ≤ 1 := Real.sin_sq_le_one b
  have h16 : 16 * sin a ^ 2 * sin b ^ 2 ≤ 16 * sin a ^ 2 := by
    nlinarith
  -- DeltaAB ≥ 96 + 25 sin²a + 64 sin²b - 16 sin²a = 96 + 9 sin²a + 64 sin²b > 0
  unfold DeltaAB
  nlinarith

lemma one_sub_Auv_two :
    ∀ a b : ℝ,
      1 - Auv (2 * a) (2 * b) = DeltaAB a b / 196 := by
  intro a b
  unfold Auv DeltaAB
  rw [seven_add_cos_two, seventeen_add_eight_cos_two]
  have h196 : (196 : ℝ) ≠ 0 := by norm_num
  have h392 : (392 : ℝ) ≠ 0 := by norm_num
  field_simp [h196, h392]
  ring

lemma Auv_two_formula (a b : ℝ) :
    Auv (2 * a) (2 * b) = (8 - 2 * sin a ^ 2) * (25 - 16 * sin b ^ 2) / 392 := by
  unfold Auv
  rw [seven_add_cos_two, seventeen_add_eight_cos_two]

lemma continuous_Auv : Continuous fun p : ℝ × ℝ => Auv p.1 p.2 := by
  unfold Auv
  fun_prop

lemma continuous_remaining_integrand :
    Continuous fun p : ℝ × ℝ =>
      (367 + 1778 * Auv p.1 p.2) / (1 - Auv p.1 p.2) ^ ((3 : ℝ) / 2) := by
  have hpos : ∀ p : ℝ × ℝ, 0 < 1 - Auv p.1 p.2 := fun p => Auv_lt_one' _ _
  refine Continuous.div ?_ ?_ ?_
  · exact continuous_const.add (continuous_const.mul continuous_Auv)
  · exact (continuous_const.sub continuous_Auv).rpow_const
      (fun p => Or.inl (hpos p).ne')
  · intro p
    exact (Real.rpow_pos_of_pos (hpos p) _).ne'

lemma remaining_scale_first :
    ∫ u in (0 : ℝ)..π,
        ∫ v in (0 : ℝ)..π,
          (367 + 1778 * Auv u v) / (1 - Auv u v) ^ ((3 : ℝ) / 2) =
      (2 : ℝ) * ∫ a in (0 : ℝ)..(π / 2),
        ∫ v in (0 : ℝ)..π,
          (367 + 1778 * Auv (2 * a) v) / (1 - Auv (2 * a) v) ^ ((3 : ℝ) / 2) := by
  have hmul :=
    intervalIntegral.smul_integral_comp_mul_left
      (f := fun u : ℝ =>
        ∫ v in (0 : ℝ)..π,
          (367 + 1778 * Auv u v) / (1 - Auv u v) ^ ((3 : ℝ) / 2))
      (a := (0 : ℝ)) (b := π / 2) (c := (2 : ℝ))
  have : (2 : ℝ) * (π / 2) = π := by ring
  simpa [smul_eq_mul, mul_zero, this] using hmul.symm

lemma remaining_scale_second (a : ℝ) :
    ∫ v in (0 : ℝ)..π,
        (367 + 1778 * Auv (2 * a) v) / (1 - Auv (2 * a) v) ^ ((3 : ℝ) / 2) =
      (2 : ℝ) * ∫ b in (0 : ℝ)..(π / 2),
        (367 + 1778 * Auv (2 * a) (2 * b)) /
          (1 - Auv (2 * a) (2 * b)) ^ ((3 : ℝ) / 2) := by
  have hmul :=
    intervalIntegral.smul_integral_comp_mul_left
      (f := fun v : ℝ =>
        (367 + 1778 * Auv (2 * a) v) / (1 - Auv (2 * a) v) ^ ((3 : ℝ) / 2))
      (a := (0 : ℝ)) (b := π / 2) (c := (2 : ℝ))
  have : (2 : ℝ) * (π / 2) = π := by ring
  simpa [smul_eq_mul, mul_zero, this] using hmul.symm

lemma remaining_to_half_square :
    ∫ u in (0 : ℝ)..π,
        ∫ v in (0 : ℝ)..π,
          (367 + 1778 * Auv u v) / (1 - Auv u v) ^ ((3 : ℝ) / 2) =
      (4 : ℝ) * ∫ a in (0 : ℝ)..(π / 2),
        ∫ b in (0 : ℝ)..(π / 2),
          (367 + 1778 * Auv (2 * a) (2 * b)) /
            (1 - Auv (2 * a) (2 * b)) ^ ((3 : ℝ) / 2) := by
  rw [remaining_scale_first]
  have hinner : ∀ a : ℝ,
      ∫ v in (0 : ℝ)..π,
          (367 + 1778 * Auv (2 * a) v) / (1 - Auv (2 * a) v) ^ ((3 : ℝ) / 2) =
        (2 : ℝ) * ∫ b in (0 : ℝ)..(π / 2),
          (367 + 1778 * Auv (2 * a) (2 * b)) /
            (1 - Auv (2 * a) (2 * b)) ^ ((3 : ℝ) / 2) :=
    remaining_scale_second
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma remaining_point_eq_Delta (a b : ℝ) :
    (367 + 1778 * Auv (2 * a) (2 * b)) /
        (1 - Auv (2 * a) (2 * b)) ^ ((3 : ℝ) / 2) =
      2145 * (196 : ℝ) ^ ((3 : ℝ) / 2) * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
        1778 * (196 : ℝ) ^ ((1 : ℝ) / 2) * (DeltaAB a b) ^ (-((1 : ℝ) / 2)) := by
  have hA0 := Auv_nonneg (2 * a) (2 * b)
  have hA := Auv_lt_one (2 * a) (2 * b)
  rw [integrand_A_split hA0 hA, one_sub_Auv_two]
  have hD : 0 < DeltaAB a b := DeltaAB_pos a b
  have h196 : (0 : ℝ) < 196 := by norm_num
  have hquot : ∀ s : ℝ,
      (DeltaAB a b / 196) ^ (-s) = 196 ^ s * (DeltaAB a b) ^ (-s) := by
    intro s
    have hx : 0 ≤ DeltaAB a b := hD.le
    have hy : 0 ≤ (196 : ℝ) := h196.le
    calc
      (DeltaAB a b / 196) ^ (-s)
          = (DeltaAB a b ^ (-s)) / (196 ^ (-s)) := by
              rw [Real.div_rpow hx hy, Real.rpow_neg hx, Real.rpow_neg hy]
      _ = (DeltaAB a b ^ (-s)) / (196 ^ s)⁻¹ := by
              rw [Real.rpow_neg hy]
      _ = (DeltaAB a b ^ (-s)) * (196 ^ s) := by
              rw [div_inv_eq_mul]
      _ = 196 ^ s * (DeltaAB a b) ^ (-s) := by
              ring
  have hquot1 := hquot ((1 : ℝ) / 2)
  have hquot3 := hquot ((3 : ℝ) / 2)
  rw [hquot1, hquot3]
  ring

lemma rpow_196_half : (196 : ℝ) ^ ((1 : ℝ) / 2) = 14 := by
  have h196 : (196 : ℝ) = (14 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [← Real.sqrt_eq_rpow, h196, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 14)]

lemma rpow_196_three_halves : (196 : ℝ) ^ ((3 : ℝ) / 2) = 2744 := by
  have h1 : (196 : ℝ) ^ ((3 : ℝ) / 2) = 196 * (196 : ℝ) ^ ((1 : ℝ) / 2) := by
    have hpos : (0 : ℝ) < 196 := by norm_num
    have := Real.rpow_add hpos (1 : ℝ) ((1 : ℝ) / 2)
    rw [Real.rpow_one] at this
    have hsum : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
    rwa [hsum] at this
  rw [h1, rpow_196_half]
  norm_num

lemma remaining_point_scaled (a b : ℝ) :
    (367 + 1778 * Auv (2 * a) (2 * b)) /
        (1 - Auv (2 * a) (2 * b)) ^ ((3 : ℝ) / 2) =
      196 * (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
        127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) := by
  rw [remaining_point_eq_Delta, rpow_196_three_halves, rpow_196_half]
  ring

lemma continuous_DeltaAB : Continuous fun p : ℝ × ℝ => DeltaAB p.1 p.2 := by
  unfold DeltaAB
  fun_prop

lemma Delta_rpow_ne_zero (a b : ℝ) (s : ℝ) :
    (DeltaAB a b) ^ s ≠ 0 :=
  (Real.rpow_pos_of_pos (DeltaAB_pos a b) s).ne'

lemma continuous_Delta_combo :
    Continuous fun p : ℝ × ℝ =>
      30030 * (DeltaAB p.1 p.2) ^ (-((3 : ℝ) / 2)) -
        127 * (DeltaAB p.1 p.2) ^ (-((1 : ℝ) / 2)) := by
  have hpos : ∀ p : ℝ × ℝ, 0 < DeltaAB p.1 p.2 := fun p => DeltaAB_pos _ _
  refine Continuous.sub ?_ ?_
  · exact continuous_const.mul
      ((continuous_DeltaAB.rpow_const (fun p => Or.inl (hpos p).ne')))
  · exact continuous_const.mul
      ((continuous_DeltaAB.rpow_const (fun p => Or.inl (hpos p).ne')))

lemma remaining_half_as_Delta :
    ∫ a in (0 : ℝ)..(π / 2),
        ∫ b in (0 : ℝ)..(π / 2),
          (367 + 1778 * Auv (2 * a) (2 * b)) /
            (1 - Auv (2 * a) (2 * b)) ^ ((3 : ℝ) / 2) =
      196 * ∫ a in (0 : ℝ)..(π / 2),
        ∫ b in (0 : ℝ)..(π / 2),
          (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
            127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) := by
  have hpoint : ∀ a b : ℝ,
      (367 + 1778 * Auv (2 * a) (2 * b)) /
          (1 - Auv (2 * a) (2 * b)) ^ ((3 : ℝ) / 2) =
        196 * (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
          127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) :=
    remaining_point_scaled
  have hcongr :
      ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            (367 + 1778 * Auv (2 * a) (2 * b)) /
              (1 - Auv (2 * a) (2 * b)) ^ ((3 : ℝ) / 2) =
        ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            196 * (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
              127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) := by
    refine intervalIntegral.integral_congr ?_
    intro a _
    refine intervalIntegral.integral_congr ?_
    intro b _
    exact hpoint a b
  rw [hcongr]
  have hinner : ∀ a : ℝ,
      ∫ b in (0 : ℝ)..(π / 2),
          196 * (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
            127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) =
        196 * ∫ b in (0 : ℝ)..(π / 2),
          (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
            127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) :=
    fun a => intervalIntegral.integral_const_mul 196 _
  simp_rw [hinner, intervalIntegral.integral_const_mul]

lemma integral_sin_pow_two_mul_half (n : ℕ) :
    ∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * n) =
      (π / 2) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) := by
  have hf : Continuous (fun x : ℝ => sin x ^ (2 * n)) := continuous_sin.pow (2 * n)
  have hsplit :
      ∫ x in (0 : ℝ)..π, sin x ^ (2 * n) =
        (∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * n)) +
          ∫ x in (π / 2)..π, sin x ^ (2 * n) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (0 : ℝ) (π / 2))
      (hf.intervalIntegrable (π / 2) π)).symm
  have hrefl :
      ∫ x in (π / 2)..π, sin x ^ (2 * n) =
        ∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * n) := by
    have hcomp :=
      intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => sin x ^ (2 * n)) (d := π) (a := π / 2) (b := π)
    -- ∫_{π/2}^{π} f(π - x) dx = ∫_{π/2}^{0} f(u) (-du) after the library identity:
    -- integral_comp_sub_left : ∫_a^b f (d - x) = ∫_{d-b}^{d-a} f
    -- so ∫_{π/2}^{π} sin(π-x)^{2n} dx = ∫_{0}^{π/2} sin^{2n}
    have hπ0 : π - π = (0 : ℝ) := sub_self π
    have hπh : π - π / 2 = π / 2 := by ring
    simpa [sin_pi_sub, hπ0, hπh] using hcomp
  have hsym :
      ∫ x in (0 : ℝ)..π, sin x ^ (2 * n) =
        2 * ∫ x in (0 : ℝ)..(π / 2), sin x ^ (2 * n) := by
    rw [hsplit, hrefl]; ring
  have hfull := integral_sin_pow_two_mul n
  rw [hfull] at hsym
  linarith

/-- `Δ = P(b) + Q(b) sin² a`. -/
lemma DeltaAB_decomp (a b : ℝ) :
    DeltaAB a b =
      (96 + 64 * sin b ^ 2) + (25 - 16 * sin b ^ 2) * sin a ^ 2 := by
  unfold DeltaAB; ring

noncomputable def Psin (b : ℝ) : ℝ := 96 + 64 * sin b ^ 2
noncomputable def Qsin (b : ℝ) : ℝ := 25 - 16 * sin b ^ 2
noncomputable def Rsin (b : ℝ) : ℝ := Psin b + Qsin b

lemma Psin_pos (b : ℝ) : 0 < Psin b := by
  unfold Psin
  have : 0 ≤ sin b ^ 2 := sq_nonneg _
  nlinarith

lemma Qsin_pos (b : ℝ) : 0 < Qsin b := by
  unfold Qsin
  have h : sin b ^ 2 ≤ 1 := Real.sin_sq_le_one b
  nlinarith

lemma Rsin_pos (b : ℝ) : 0 < Rsin b := by
  unfold Rsin; linarith [Psin_pos b, Qsin_pos b]

lemma Qsin_div_Psin_lt_one (b : ℝ) : Qsin b / Psin b < 1 := by
  have hP := Psin_pos b
  have hQ := Qsin_pos b
  rw [div_lt_one hP]
  unfold Psin Qsin
  have : 0 ≤ sin b ^ 2 := sq_nonneg _
  nlinarith

lemma Qsin_div_Psin_nonneg (b : ℝ) : 0 ≤ Qsin b / Psin b := by
  exact div_nonneg (Qsin_pos b).le (Psin_pos b).le

lemma Qsin_div_Psin_le_25_div_96 (b : ℝ) : Qsin b / Psin b ≤ (25 : ℝ) / 96 := by
  have hP := Psin_pos b
  have hs : 0 ≤ sin b ^ 2 := sq_nonneg _
  have hs1 : sin b ^ 2 ≤ 1 := Real.sin_sq_le_one b
  -- (25-16s)/(96+64s) is decreasing in s, max at s=0 is 25/96
  rw [div_le_div_iff₀ hP (by norm_num : (0 : ℝ) < 96)]
  unfold Psin Qsin
  nlinarith

lemma twentyfive_div_96_lt_one : (25 : ℝ) / 96 < 1 := by norm_num

/-- `Γ(1/2) = √π`. -/
lemma Gamma_one_half : Real.Gamma (1 / 2) = Real.sqrt π :=
  Real.Gamma_one_half_eq

/-- `Γ(3/2) = √π / 2`. -/
lemma Gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
  have h := Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have harg : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
  rw [harg] at h
  rw [h, Gamma_one_half]
  ring

/-- `(1/2)_n = (2n)! / (4^n n!)`. -/
lemma ascPochhammer_one_half (n : ℕ) :
    (ascPochhammer ℝ n).eval (1 / 2 : ℝ) =
      ((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * n.factorial) := by
  induction n with
  | zero =>
    simp [ascPochhammer_zero]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih]
    have hfact2 : ((2 * (n + 1)).factorial : ℝ) =
        (2 * n + 2 : ℝ) * (2 * n + 1) * (2 * n).factorial := by
      have h1 := Nat.factorial_succ (2 * n + 1)
      have h2 := Nat.factorial_succ (2 * n)
      have : 2 * n + 1 + 1 = 2 * n + 2 := by ring
      rw [this] at h1
      have h2n : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [h2n]
      push_cast [h1, h2]
      ring
    have hfactn : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * n.factorial := by
      exact_mod_cast Nat.factorial_succ n
    have h4 : (4 : ℝ) ^ (n + 1) = 4 * (4 : ℝ) ^ n := pow_succ' _ _
    have hn0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h4n : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2n0 : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (2 * n).factorial_ne_zero
    have hn1 : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    -- `(1/2 + n) * ((2n)! / (4^n n!)) = (2n+2)! / (4^{n+1} (n+1)!)`
    have htarget :
        ((1 : ℝ) / 2 + n) * (((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * n.factorial)) =
          ((2 * (n + 1)).factorial : ℝ) / ((4 : ℝ) ^ (n + 1) * (n + 1).factorial) := by
      have hL :
          ((1 : ℝ) / 2 + n) * (((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * n.factorial)) =
            ((2 * n + 1 : ℝ) / 2) * (((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * n.factorial)) := by
        ring
      rw [hL, hfact2, hfactn, h4]
      field_simp [hn0, h4n, h2n0, hn1]
      ring
    simpa [add_comm, mul_comm] using htarget

/-- `(2)_n = (n+1)!`. -/
lemma ascPochhammer_two (n : ℕ) :
    (ascPochhammer ℝ n).eval (2 : ℝ) = ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => simp [ascPochhammer_zero]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih]
    have : ((n + 1 + 1).factorial : ℝ) = (n + 2 : ℝ) * (n + 1).factorial := by
      exact_mod_cast Nat.factorial_succ (n + 1)
    have h2 : (2 : ℝ) + n = n + 2 := by ring
    rw [h2, this]
    ring

/-- Central binomial in Pochhammer form: `C(2n,n)/4^n = (1/2)_n / n!`. -/
lemma centralBinom_eq_pochhammer (n : ℕ) :
    (n.centralBinom : ℝ) / (4 : ℝ) ^ n =
      (ascPochhammer ℝ n).eval (1 / 2 : ℝ) / n.factorial := by
  rw [ascPochhammer_one_half, Nat.centralBinom]
  have hn0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4n : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hle : n ≤ 2 * n := Nat.le_mul_of_pos_left _ (by decide)
  have hch0 := Nat.choose_mul_factorial_mul_factorial hle
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at hch0
  have hch : ((2 * n).choose n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
      ((2 * n).factorial : ℝ) := by exact_mod_cast hch0
  have hL : ((2 * n).choose n : ℝ) / (4 : ℝ) ^ n =
      ((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * n.factorial * n.factorial) := by
    have := hch
    field_simp [hn0, h4n] at this ⊢
    linarith
  rw [hL]
  field_simp [hn0]

/-- `(-α)_k / k!` binomial coefficient for the expansion of `(1+X)^{-α}`. -/
lemma neg_ascPochhammer_succ (α : ℝ) (k : ℕ) :
    (ascPochhammer ℝ (k + 1)).eval (-α) =
      (-α + k) * (ascPochhammer ℝ k).eval (-α) := by
  rw [ascPochhammer_succ_eval]
  ring

/-- Bound on the cross term appearing in `DeltaAB / 96`. -/
lemma XAB_lt_one (a b : ℝ) :
    (25 : ℝ) / 96 * sin a ^ 2 + (2 : ℝ) / 3 * sin b ^ 2
      - (1 : ℝ) / 6 * sin a ^ 2 * sin b ^ 2 < 1 := by
  have hs : 0 ≤ sin a ^ 2 := sq_nonneg _
  have ht : 0 ≤ sin b ^ 2 := sq_nonneg _
  have hs1 : sin a ^ 2 ≤ 1 := Real.sin_sq_le_one a
  have ht1 : sin b ^ 2 ≤ 1 := Real.sin_sq_le_one b
  -- X = (2/3) t + (25/96 - t/6) s ≤ 2/3 + 3/32 = 73/96 < 1
  have hcoef : (25 : ℝ) / 96 - sin b ^ 2 / 6 ≤ (25 : ℝ) / 96 := by
    nlinarith
  nlinarith

lemma XAB_nonneg (a b : ℝ) :
    0 ≤ (25 : ℝ) / 96 * sin a ^ 2 + (2 : ℝ) / 3 * sin b ^ 2
      - (1 : ℝ) / 6 * sin a ^ 2 * sin b ^ 2 := by
  have hs : 0 ≤ sin a ^ 2 := sq_nonneg _
  have ht : 0 ≤ sin b ^ 2 := sq_nonneg _
  have ht1 : sin b ^ 2 ≤ 1 := Real.sin_sq_le_one b
  have hlin : (2 : ℝ) / 3 - sin a ^ 2 / 6 ≥ (2 : ℝ) / 3 - 1 / 6 := by
    have : sin a ^ 2 / 6 ≤ (1 : ℝ) / 6 := by nlinarith [Real.sin_sq_le_one a]
    linarith
  have : (2 : ℝ) / 3 - 1 / 6 = (1 : ℝ) / 2 := by norm_num
  nlinarith

lemma DeltaAB_eq_96_mul (a b : ℝ) :
    DeltaAB a b = 96 * (1 +
      ((25 : ℝ) / 96 * sin a ^ 2 + (2 : ℝ) / 3 * sin b ^ 2
        - (1 : ℝ) / 6 * sin a ^ 2 * sin b ^ 2)) := by
  unfold DeltaAB
  ring

/-- `Ring.choose (-1/2) n = (-1)^n C(2n,n) / 4^n`. -/
lemma ring_choose_neg_one_half (n : ℕ) :
    Ring.choose (-(1 / 2 : ℝ)) n =
      ((-1 : ℝ) ^ n) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n := by
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdesc := Ring.descPochhammer_eq_factorial_smul_choose (R := ℝ) (-(1 / 2 : ℝ)) n
  have hpoch : (descPochhammer ℤ n).smeval (-(1 / 2 : ℝ)) =
      ((-1 : ℝ) ^ n) * ((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * n.factorial) := by
    have hrel : (descPochhammer ℤ n).smeval (-(1 / 2 : ℝ)) =
        (ascPochhammer ℝ n).eval ((1 : ℝ) / 2 - n) := by
      rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer]
      have : -(1 / 2 : ℝ) - n + 1 = (1 : ℝ) / 2 - n := by ring
      rw [this, Polynomial.ascPochhammer_smeval_eq_eval]
    rw [hrel]
    have hneg : (ascPochhammer ℝ n).eval ((1 : ℝ) / 2 - n) =
        (-1 : ℝ) ^ n * (descPochhammer ℝ n).eval ((n : ℝ) - 1 / 2) := by
      have : ((1 : ℝ) / 2 - n) = -((n : ℝ) - 1 / 2) := by ring
      rw [this, ascPochhammer_eval_neg_eq_descPochhammer]
    rw [hneg]
    have hrev : (descPochhammer ℝ n).eval ((n : ℝ) - 1 / 2) =
        (ascPochhammer ℝ n).eval (1 / 2) := by
      rw [descPochhammer_eval_eq_ascPochhammer]
      have : ((n : ℝ) - 1 / 2) - n + 1 = (1 : ℝ) / 2 := by ring
      rw [this]
    rw [hrev, ascPochhammer_one_half]
    ring
  have hsmul : (n.factorial : ℝ) * Ring.choose (-(1 / 2 : ℝ)) n =
      (descPochhammer ℤ n).smeval (-(1 / 2 : ℝ)) := by
    simpa [nsmul_eq_mul] using hdesc.symm
  have hcb : (n.centralBinom : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
      ((2 * n).factorial : ℝ) := by
    have hle : n ≤ 2 * n := Nat.le_mul_of_pos_left _ (by decide)
    have hch := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : 2 * n - n = n := by omega
    rw [hsub] at hch
    have : (n.centralBinom : ℕ) = (2 * n).choose n := rfl
    exact_mod_cast (by simpa [this] using hch)
  have hmul :
      (n.factorial : ℝ) *
          (((-1 : ℝ) ^ n) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n) =
        ((-1 : ℝ) ^ n) * ((2 * n).factorial : ℝ) / ((4 : ℝ) ^ n * n.factorial) := by
    have hnn : (n.factorial : ℝ) * (n.factorial : ℝ) ≠ 0 := mul_ne_zero hfac hfac
    field_simp [hfac, h4, hnn]
    nlinarith [hcb]
  have hLR : (n.factorial : ℝ) * Ring.choose (-(1 / 2 : ℝ)) n =
      (n.factorial : ℝ) *
        (((-1 : ℝ) ^ n) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n) := by
    rw [hsmul, hpoch, hmul]
  exact (mul_right_inj' hfac).mp hLR

/-- `(3/2)_n = (2n+1) (1/2)_n`. -/
lemma ascPochhammer_three_halves (n : ℕ) :
    (ascPochhammer ℝ n).eval (3 / 2 : ℝ) =
      (2 * n + 1 : ℝ) * (ascPochhammer ℝ n).eval (1 / 2 : ℝ) := by
  induction n with
  | zero => simp [ascPochhammer_zero]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]
    push_cast
    ring

/-- `Ring.choose (-3/2) n = (-1)^n (2n+1) C(2n,n) / 4^n`. -/
lemma ring_choose_neg_three_halves (n : ℕ) :
    Ring.choose (-((3 : ℝ) / 2)) n =
      ((-1 : ℝ) ^ n) * (2 * n + 1 : ℝ) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n := by
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdesc := Ring.descPochhammer_eq_factorial_smul_choose (R := ℝ) (-((3 : ℝ) / 2)) n
  have hpoch : (descPochhammer ℤ n).smeval (-((3 : ℝ) / 2)) =
      ((-1 : ℝ) ^ n) * (2 * n + 1 : ℝ) * ((2 * n).factorial : ℝ) /
        ((4 : ℝ) ^ n * n.factorial) := by
    have hrel : (descPochhammer ℤ n).smeval (-((3 : ℝ) / 2)) =
        (ascPochhammer ℝ n).eval (-((3 : ℝ) / 2) - n + 1) := by
      rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
        Polynomial.ascPochhammer_smeval_eq_eval]
    have harg : -((3 : ℝ) / 2) - (n : ℝ) + 1 = -(((1 : ℝ) / 2) + n) := by ring
    rw [hrel, harg]
    have hneg : (ascPochhammer ℝ n).eval (-(((1 : ℝ) / 2) + (n : ℝ))) =
        (-1 : ℝ) ^ n * (descPochhammer ℝ n).eval (((1 : ℝ) / 2) + (n : ℝ)) := by
      rw [ascPochhammer_eval_neg_eq_descPochhammer]
    have hrev : (descPochhammer ℝ n).eval (((1 : ℝ) / 2) + n) =
        (ascPochhammer ℝ n).eval (3 / 2) := by
      rw [descPochhammer_eval_eq_ascPochhammer]
      have : (((1 : ℝ) / 2) + n) - n + 1 = (3 : ℝ) / 2 := by ring
      rw [this]
    rw [hneg, hrev, ascPochhammer_three_halves, ascPochhammer_one_half]
    ring
  have hsmul : (n.factorial : ℝ) * Ring.choose (-((3 : ℝ) / 2)) n =
      (descPochhammer ℤ n).smeval (-((3 : ℝ) / 2)) := by
    simpa [nsmul_eq_mul] using hdesc.symm
  have hcb : (n.centralBinom : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
      ((2 * n).factorial : ℝ) := by
    have hle : n ≤ 2 * n := Nat.le_mul_of_pos_left _ (by decide)
    have hch := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : 2 * n - n = n := by omega
    rw [hsub] at hch
    have : (n.centralBinom : ℕ) = (2 * n).choose n := rfl
    exact_mod_cast (by simpa [this] using hch)
  have hmul :
      (n.factorial : ℝ) *
          (((-1 : ℝ) ^ n) * (2 * n + 1 : ℝ) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n) =
        ((-1 : ℝ) ^ n) * (2 * n + 1 : ℝ) * ((2 * n).factorial : ℝ) /
          ((4 : ℝ) ^ n * n.factorial) := by
    field_simp [hfac, h4]
    nlinarith [hcb]
  have hLR : (n.factorial : ℝ) * Ring.choose (-((3 : ℝ) / 2)) n =
      (n.factorial : ℝ) *
        (((-1 : ℝ) ^ n) * (2 * n + 1 : ℝ) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n) := by
    rw [hsmul, hpoch, hmul]
  exact (mul_right_inj' hfac).mp hLR

/-- Pointwise binomial series for `(1 + x)^a` when `|x| < 1`. -/
lemma one_add_rpow_eq_tsum {a x : ℝ} (hx : |x| < 1) :
    (1 + x) ^ a = ∑' n : ℕ, Ring.choose a n * x ^ n := by
  have h := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)
  have hy : x ∈ EMetric.ball (0 : ℝ) 1 := by
    rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm]
    exact ENNReal.coe_lt_one_iff.mpr (by exact_mod_cast hx)
  have hsum := h.sum hy
  simp only [zero_add] at hsum
  refine hsum.trans ?_
  have hterm : ∀ n : ℕ, x ^ n * Ring.choose a n = Ring.choose a n * x ^ n :=
    fun n => mul_comm _ _
  simp [FormalMultilinearSeries.sum, binomialSeries, hterm]

lemma XAB_lt_one_abs (a b : ℝ) :
    |(25 : ℝ) / 96 * sin a ^ 2 + (2 : ℝ) / 3 * sin b ^ 2
      - (1 : ℝ) / 6 * sin a ^ 2 * sin b ^ 2| < 1 := by
  have hnn := XAB_nonneg a b
  have hlt := XAB_lt_one a b
  rw [abs_of_nonneg hnn]
  exact hlt

/-- The cross-term appearing in `DeltaAB / 96`. -/
noncomputable def XAB (a b : ℝ) : ℝ :=
  (25 : ℝ) / 96 * sin a ^ 2 + (2 : ℝ) / 3 * sin b ^ 2
    - (1 : ℝ) / 6 * sin a ^ 2 * sin b ^ 2

lemma XAB_eq (a b : ℝ) :
    XAB a b =
      (25 : ℝ) / 96 * sin a ^ 2 + (2 : ℝ) / 3 * sin b ^ 2
        - (1 : ℝ) / 6 * sin a ^ 2 * sin b ^ 2 := rfl

lemma XAB_nonneg' (a b : ℝ) : 0 ≤ XAB a b := XAB_nonneg a b

lemma XAB_lt_one' (a b : ℝ) : XAB a b < 1 := XAB_lt_one a b

lemma one_add_XAB_pos (a b : ℝ) : 0 < 1 + XAB a b :=
  add_pos_of_pos_of_nonneg (by norm_num) (XAB_nonneg a b)

lemma DeltaAB_eq_96_mul_XAB (a b : ℝ) :
    DeltaAB a b = 96 * (1 + XAB a b) :=
  DeltaAB_eq_96_mul a b

lemma rpow_mul_pos {x y s : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x * y) ^ s = x ^ s * y ^ s :=
  Real.mul_rpow hx.le hy.le

lemma Delta_rpow (a b : ℝ) (s : ℝ) :
    (DeltaAB a b) ^ s = (96 : ℝ) ^ s * (1 + XAB a b) ^ s := by
  rw [DeltaAB_eq_96_mul_XAB, rpow_mul_pos (by norm_num) (one_add_XAB_pos a b)]

lemma rpow_96_half : (96 : ℝ) ^ ((1 : ℝ) / 2) = 4 * Real.sqrt 6 := by
  have h : (96 : ℝ) = 16 * 6 := by norm_num
  have h16 : (16 : ℝ) ^ ((1 : ℝ) / 2) = 4 := by
    have : (16 : ℝ) = (4 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [this, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by norm_num)]
  have h6 : (6 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 6 :=
    (Real.sqrt_eq_rpow 6).symm
  rw [h, rpow_mul_pos (by norm_num) (by norm_num), h16, h6]

lemma rpow_96_three_halves : (96 : ℝ) ^ ((3 : ℝ) / 2) = 384 * Real.sqrt 6 := by
  have hpos : (0 : ℝ) < 96 := by norm_num
  have := Real.rpow_add hpos (1 : ℝ) ((1 : ℝ) / 2)
  have hsum : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [hsum, Real.rpow_one] at this
  rw [this, rpow_96_half]
  ring

lemma rpow_neg_96 (s : ℝ) : (96 : ℝ) ^ (-s) = 1 / (96 : ℝ) ^ s := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 96) s, one_div]

lemma combo_as_XAB (a b : ℝ) :
    30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
      127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2)) =
    (1 / (4 * Real.sqrt 6)) *
      (30030 / 96 * (1 + XAB a b) ^ (-((3 : ℝ) / 2)) -
        127 * (1 + XAB a b) ^ (-((1 : ℝ) / 2))) := by
  rw [Delta_rpow a b (-((3 : ℝ) / 2)), Delta_rpow a b (-((1 : ℝ) / 2))]
  rw [rpow_neg_96 ((3 : ℝ) / 2), rpow_neg_96 ((1 : ℝ) / 2),
    rpow_96_three_halves, rpow_96_half]
  have hs6 : Real.sqrt 6 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs6]
  ring

/-- `Δ = 169 - 9 cos²a - 48 cos²b - 16 cos²a cos²b`. -/
lemma DeltaAB_eq_169 (a b : ℝ) :
    DeltaAB a b =
      169 - 9 * cos a ^ 2 - 48 * cos b ^ 2 - 16 * cos a ^ 2 * cos b ^ 2 := by
  unfold DeltaAB
  have ha : sin a ^ 2 = 1 - cos a ^ 2 := by linarith [sin_sq_add_cos_sq a]
  have hb : sin b ^ 2 = 1 - cos b ^ 2 := by linarith [sin_sq_add_cos_sq b]
  rw [ha, hb]
  ring

noncomputable def YAB (a b : ℝ) : ℝ :=
  (9 * cos a ^ 2 + 48 * cos b ^ 2 + 16 * cos a ^ 2 * cos b ^ 2) / 169

lemma YAB_nonneg (a b : ℝ) : 0 ≤ YAB a b := by
  unfold YAB
  have h9 : 0 ≤ 9 * cos a ^ 2 := by positivity
  have h48 : 0 ≤ 48 * cos b ^ 2 := by positivity
  have h16 : 0 ≤ 16 * cos a ^ 2 * cos b ^ 2 := by positivity
  have : 0 ≤ 9 * cos a ^ 2 + 48 * cos b ^ 2 + 16 * cos a ^ 2 * cos b ^ 2 := by nlinarith
  positivity

lemma YAB_lt_one (a b : ℝ) : YAB a b < 1 := by
  unfold YAB
  have ha : cos a ^ 2 ≤ 1 := Real.cos_sq_le_one a
  have hb : cos b ^ 2 ≤ 1 := Real.cos_sq_le_one b
  have hnum : 9 * cos a ^ 2 + 48 * cos b ^ 2 + 16 * cos a ^ 2 * cos b ^ 2 ≤ 73 := by
    nlinarith [mul_le_mul ha hb (sq_nonneg _) (by positivity : (0 : ℝ) ≤ 1)]
  have : (9 * cos a ^ 2 + 48 * cos b ^ 2 + 16 * cos a ^ 2 * cos b ^ 2) / 169 ≤
      (73 : ℝ) / 169 := (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 169)).mpr hnum
  linarith

lemma YAB_abs_lt_one (a b : ℝ) : |YAB a b| < 1 := by
  rw [abs_of_nonneg (YAB_nonneg a b)]
  exact YAB_lt_one a b

lemma DeltaAB_eq_169_mul (a b : ℝ) :
    DeltaAB a b = 169 * (1 - YAB a b) := by
  rw [DeltaAB_eq_169]
  unfold YAB
  ring

lemma one_sub_YAB_pos (a b : ℝ) : 0 < 1 - YAB a b :=
  sub_pos.mpr (YAB_lt_one a b)

lemma Delta_rpow_169 (a b : ℝ) (s : ℝ) :
    (DeltaAB a b) ^ s = (169 : ℝ) ^ s * (1 - YAB a b) ^ s := by
  rw [DeltaAB_eq_169_mul, rpow_mul_pos (by norm_num) (one_sub_YAB_pos a b)]

lemma rpow_169_half : (169 : ℝ) ^ ((1 : ℝ) / 2) = 13 := by
  have : (169 : ℝ) = (13 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [this, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by norm_num)]

lemma rpow_169_three_halves : (169 : ℝ) ^ ((3 : ℝ) / 2) = 2197 := by
  have hpos : (0 : ℝ) < 169 := by norm_num
  have := Real.rpow_add hpos (1 : ℝ) ((1 : ℝ) / 2)
  have hsum : (1 : ℝ) + 1 / 2 = 3 / 2 := by norm_num
  rw [hsum, Real.rpow_one] at this
  rw [this, rpow_169_half]
  norm_num

lemma rpow_neg_169 (s : ℝ) : (169 : ℝ) ^ (-s) = 1 / (169 : ℝ) ^ s := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 169) s, one_div]

lemma combo_as_YAB (a b : ℝ) :
    30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
      127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2)) =
    (1 / (13 : ℝ)) *
      (30030 / 169 * (1 - YAB a b) ^ (-((3 : ℝ) / 2)) -
        127 * (1 - YAB a b) ^ (-((1 : ℝ) / 2))) := by
  rw [Delta_rpow_169 a b (-((3 : ℝ) / 2)), Delta_rpow_169 a b (-((1 : ℝ) / 2))]
  rw [rpow_neg_169 ((3 : ℝ) / 2), rpow_neg_169 ((1 : ℝ) / 2),
    rpow_169_three_halves, rpow_169_half]
  norm_num
  ring

/-- Even powers of cosine on `[0, π/2]`. -/
lemma integral_cos_pow_two_mul_half (n : ℕ) :
    ∫ x in (0 : ℝ)..(π / 2), cos x ^ (2 * n) =
      (π / 2) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) := by
  have hfull := integral_cos_pow_two_mul n
  have hcont : Continuous (fun x : ℝ => cos x ^ (2 * n)) := continuous_cos.pow (2 * n)
  have h01 : IntervalIntegrable (fun x : ℝ => cos x ^ (2 * n))
      MeasureTheory.volume (0 : ℝ) (π / 2) :=
    hcont.intervalIntegrable _ _
  have h12 : IntervalIntegrable (fun x : ℝ => cos x ^ (2 * n))
      MeasureTheory.volume (π / 2) π :=
    hcont.intervalIntegrable _ _
  have hshift :
      ∫ x in (π / 2)..π, cos x ^ (2 * n) =
        ∫ t in (0 : ℝ)..(π / 2), cos t ^ (2 * n) := by
    have hcomp :=
      intervalIntegral.integral_comp_sub_left
        (f := fun x : ℝ => cos x ^ (2 * n)) (a := (0 : ℝ)) (b := π / 2) (d := π)
    have hlim : π - π / 2 = π / 2 := by ring
    have hlim0 : π - (0 : ℝ) = π := by ring
    have : ∫ t in (0 : ℝ)..(π / 2), cos (π - t) ^ (2 * n) =
        ∫ x in (π / 2)..π, cos x ^ (2 * n) := by
      simpa [hlim, hlim0] using hcomp
    have hcongr :
        ∫ t in (0 : ℝ)..(π / 2), cos (π - t) ^ (2 * n) =
          ∫ t in (0 : ℝ)..(π / 2), cos t ^ (2 * n) := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      have heven : Even (2 * n) := even_two_mul n
      simp [cos_pi_sub, heven.neg_pow]
    exact (this.symm.trans hcongr)
  have hsum :
      ∫ x in (0 : ℝ)..π, cos x ^ (2 * n) =
        2 * ∫ x in (0 : ℝ)..(π / 2), cos x ^ (2 * n) := by
    have := intervalIntegral.integral_add_adjacent_intervals h01 h12
    rw [hshift] at this
    linarith
  have : 2 * ∫ x in (0 : ℝ)..(π / 2), cos x ^ (2 * n) =
      π * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) := by
    rw [← hfull, hsum]
  linarith

lemma abs_neg_YAB_lt_one (a b : ℝ) : |(-YAB a b)| < 1 := by
  simpa [abs_neg] using YAB_abs_lt_one a b

lemma one_sub_YAB_rpow_neg_half (a b : ℝ) :
    (1 - YAB a b) ^ (-((1 : ℝ) / 2)) =
      ∑' n : ℕ, Ring.choose (-((1 : ℝ) / 2)) n * (-YAB a b) ^ n :=
  one_add_rpow_eq_tsum (abs_neg_YAB_lt_one a b)

lemma one_sub_YAB_rpow_neg_three_halves (a b : ℝ) :
    (1 - YAB a b) ^ (-((3 : ℝ) / 2)) =
      ∑' n : ℕ, Ring.choose (-((3 : ℝ) / 2)) n * (-YAB a b) ^ n :=
  one_add_rpow_eq_tsum (abs_neg_YAB_lt_one a b)

lemma YAB_le_73_div_169 (a b : ℝ) : YAB a b ≤ (73 : ℝ) / 169 := by
  unfold YAB
  have ha : cos a ^ 2 ≤ 1 := Real.cos_sq_le_one a
  have hb : cos b ^ 2 ≤ 1 := Real.cos_sq_le_one b
  have hnum : 9 * cos a ^ 2 + 48 * cos b ^ 2 + 16 * cos a ^ 2 * cos b ^ 2 ≤ 73 := by
    nlinarith [mul_le_mul ha hb (sq_nonneg _) (by positivity : (0 : ℝ) ≤ 1)]
  exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 169)).mpr hnum

lemma combo_series_coeff (n : ℕ) (y : ℝ) :
    (1 / (13 : ℝ)) *
        (30030 / 169 * (Ring.choose (-((3 : ℝ) / 2)) n * (-y) ^ n) -
          127 * (Ring.choose (-((1 : ℝ) / 2)) n * (-y) ^ n)) =
      ((4620 * (n : ℝ) + 659) / 169) *
        ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * y ^ n := by
  rw [ring_choose_neg_three_halves, ring_choose_neg_one_half, neg_pow, neg_pow]
  have h4 : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsgn : ((-1 : ℝ) ^ (n * 2)) = 1 := by
    rw [mul_comm, pow_mul, neg_one_sq, one_pow]
  field_simp [h4]
  ring_nf
  rw [hsgn]
  ring

lemma centralBinom_div_four_pow_le_one (n : ℕ) :
    (n.centralBinom : ℝ) / (4 : ℝ) ^ n ≤ 1 := by
  have h := centralBinom_le n
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := pow_pos (by norm_num) _
  exact (div_le_one h4).mpr h

lemma summable_geom_73 : Summable fun n : ℕ => ((73 : ℝ) / 169) ^ n :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma summable_n_geom_73 : Summable fun n : ℕ => (n : ℝ) * ((73 : ℝ) / 169) ^ n := by
  have hr : ‖(73 : ℝ) / 169‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    norm_num
  simpa using
    (summable_pow_mul_geometric_of_norm_lt_one (k := 1) (r := (73 : ℝ) / 169) hr)

lemma abs_choose_neg_half_mul (n : ℕ) (y : ℝ) :
    |Ring.choose (-((1 : ℝ) / 2)) n * (-y) ^ n| =
      ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * |y| ^ n := by
  rw [ring_choose_neg_one_half, neg_pow]
  have hnn : 0 ≤ (n.centralBinom : ℝ) := by exact_mod_cast Nat.zero_le _
  have h4 : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
  simp [abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg hnn, abs_of_pos h4]

lemma abs_choose_neg_three_halves_mul (n : ℕ) (y : ℝ) :
    |Ring.choose (-((3 : ℝ) / 2)) n * (-y) ^ n| =
      (2 * n + 1 : ℝ) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n * |y| ^ n := by
  have hnn : 0 ≤ (n.centralBinom : ℝ) := by exact_mod_cast Nat.zero_le _
  have h4 : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
  have hn1 : 0 ≤ (2 * n + 1 : ℝ) := by positivity
  rw [ring_choose_neg_three_halves, neg_pow]
  simp [abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg hnn, abs_of_pos h4,
    abs_of_nonneg hn1]

lemma summable_choose_neg_half (a b : ℝ) :
    Summable fun n : ℕ => Ring.choose (-((1 : ℝ) / 2)) n * (-YAB a b) ^ n := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ summable_geom_73
  intro n
  have habs : |YAB a b| ≤ (73 : ℝ) / 169 := by
    rw [abs_of_nonneg (YAB_nonneg a b)]
    exact YAB_le_73_div_169 a b
  rw [Real.norm_eq_abs, abs_choose_neg_half_mul]
  have hle1 := centralBinom_div_four_pow_le_one n
  have hle2 : |YAB a b| ^ n ≤ ((73 : ℝ) / 169) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) habs n
  exact (mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) n) hle1).trans hle2

lemma summable_two_n_add_one_geom :
    Summable fun n : ℕ => (2 * (n : ℝ) + 1) * ((73 : ℝ) / 169) ^ n := by
  have h := (summable_n_geom_73.mul_left (2 : ℝ)).add (summable_geom_73.mul_left (1 : ℝ))
  refine h.congr ?_
  intro n
  ring

lemma summable_choose_neg_three_halves (a b : ℝ) :
    Summable fun n : ℕ => Ring.choose (-((3 : ℝ) / 2)) n * (-YAB a b) ^ n := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ summable_two_n_add_one_geom
  intro n
  have habs : |YAB a b| ≤ (73 : ℝ) / 169 := by
    rw [abs_of_nonneg (YAB_nonneg a b)]
    exact YAB_le_73_div_169 a b
  rw [Real.norm_eq_abs, abs_choose_neg_three_halves_mul]
  have hle1 := centralBinom_div_four_pow_le_one n
  have hle2 : |YAB a b| ^ n ≤ ((73 : ℝ) / 169) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) habs n
  have hpos : 0 ≤ (2 * n + 1 : ℝ) := by positivity
  have hC : 0 ≤ (n.centralBinom : ℝ) := by exact_mod_cast Nat.zero_le _
  have h4 : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
  have : (2 * n + 1 : ℝ) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n * |YAB a b| ^ n ≤
      (2 * n + 1 : ℝ) * ((73 : ℝ) / 169) ^ n := by
    have hfrac : (n.centralBinom : ℝ) / (4 : ℝ) ^ n * |YAB a b| ^ n ≤
        ((73 : ℝ) / 169) ^ n :=
      (mul_le_of_le_one_left (pow_nonneg (abs_nonneg _) n) hle1).trans hle2
    have hrew : (2 * n + 1 : ℝ) * (n.centralBinom : ℝ) / (4 : ℝ) ^ n * |YAB a b| ^ n =
        (2 * n + 1 : ℝ) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n * |YAB a b| ^ n) := by
      field_simp [h4.ne']
    rw [hrew]
    exact mul_le_mul_of_nonneg_left hfrac hpos
  exact this

lemma combo_as_series (a b : ℝ) :
    30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
      127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2)) =
      ∑' n : ℕ,
        ((4620 * (n : ℝ) + 659) / 169) *
          ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n := by
  rw [combo_as_YAB, one_sub_YAB_rpow_neg_three_halves, one_sub_YAB_rpow_neg_half]
  set f : ℕ → ℝ := fun n => Ring.choose (-((3 : ℝ) / 2)) n * (-YAB a b) ^ n
  set g : ℕ → ℝ := fun n => Ring.choose (-((1 : ℝ) / 2)) n * (-YAB a b) ^ n
  have hf : Summable f := summable_choose_neg_three_halves a b
  have hg : Summable g := summable_choose_neg_half a b
  have hs3 : Summable fun n : ℕ => (30030 / 169 : ℝ) * f n := hf.mul_left _
  have hs1 : Summable fun n : ℕ => (127 : ℝ) * g n := hg.mul_left _
  have hdiff :
      ∑' n, ((30030 / 169 : ℝ) * f n - (127 : ℝ) * g n) =
        (30030 / 169 : ℝ) * ∑' n, f n - (127 : ℝ) * ∑' n, g n := by
    have := hs3.tsum_sub hs1
    simpa [tsum_mul_left] using this
  have hlin :
      (1 / (13 : ℝ)) * ((30030 / 169 : ℝ) * ∑' n, f n - (127 : ℝ) * ∑' n, g n) =
        ∑' n : ℕ, (1 / (13 : ℝ)) * ((30030 / 169 : ℝ) * f n - (127 : ℝ) * g n) := by
    rw [← hdiff, ← tsum_mul_left]
  rw [hlin]
  refine tsum_congr fun n => ?_
  simpa [f, g] using combo_series_coeff n (YAB a b)

lemma series_term_nonneg (n : ℕ) (a b : ℝ) :
    0 ≤ ((4620 * (n : ℝ) + 659) / 169) *
      ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n := by
  have h1 : 0 ≤ (4620 * (n : ℝ) + 659) / 169 := by positivity
  have h2 : 0 ≤ (n.centralBinom : ℝ) / (4 : ℝ) ^ n := by positivity
  have h3 : 0 ≤ (YAB a b) ^ n := pow_nonneg (YAB_nonneg a b) n
  positivity

lemma series_term_le (n : ℕ) (a b : ℝ) :
    ((4620 * (n : ℝ) + 659) / 169) *
      ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n ≤
      ((4620 * (n : ℝ) + 659) / 169) * ((73 : ℝ) / 169) ^ n := by
  have hcoeff : 0 ≤ (4620 * (n : ℝ) + 659) / 169 := by positivity
  have hY : (YAB a b) ^ n ≤ ((73 : ℝ) / 169) ^ n :=
    pow_le_pow_left₀ (YAB_nonneg a b) (YAB_le_73_div_169 a b) n
  have hC := centralBinom_div_four_pow_le_one n
  have hmid : ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n ≤
      ((73 : ℝ) / 169) ^ n :=
    (mul_le_of_le_one_left (pow_nonneg (YAB_nonneg a b) n) hC).trans hY
  have := mul_le_mul_of_nonneg_left hmid hcoeff
  convert this using 1
  ring

lemma summable_series_bound :
    Summable fun n : ℕ => ((4620 * (n : ℝ) + 659) / 169) * ((73 : ℝ) / 169) ^ n := by
  have h := (summable_n_geom_73.mul_left (4620 : ℝ)).add (summable_geom_73.mul_left (659 : ℝ))
  have : Summable fun n : ℕ => (4620 * (n : ℝ) + 659) * ((73 : ℝ) / 169) ^ n := by
    refine h.congr fun n => ?_
    ring
  convert this.mul_right ((169 : ℝ)⁻¹) using 1
  ext n
  field_simp

lemma continuous_series_term (n : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      ((4620 * (n : ℝ) + 659) / 169) *
        ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB p.1 p.2) ^ n := by
  unfold YAB
  fun_prop

/-- Interchange `∑` and `∫_0^{π/2}` for a nonnegative dominated family. -/
lemma tsum_interval_half_of_bound
    (g : ℕ → ℝ → ℝ) (b : ℕ → ℝ)
    (hcont : ∀ k, Continuous (g k))
    (hnn : ∀ k x, 0 ≤ g k x)
    (hbd : ∀ k x, g k x ≤ b k)
    (hsum : Summable b) :
    (∑' k : ℕ, ∫ x in (0 : ℝ)..(π / 2), g k x) =
      ∫ x in (0 : ℝ)..(π / 2), ∑' k : ℕ, g k x := by
  have hIoc : ∀ k,
      ∫ x in (0 : ℝ)..(π / 2), g k x =
        ∫ x in Set.Ioc (0 : ℝ) (π / 2), g k x :=
    fun k => intervalIntegral.integral_of_le (div_nonneg pi_pos.le (by norm_num))
  simp_rw [hIoc]
  have hint : ∀ k, MeasureTheory.Integrable (g k)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) (π / 2))) :=
    fun k => (hcont k).integrableOn_Ioc.integrable
  have hsum' : Summable fun k : ℕ =>
      ∫ x in Set.Ioc (0 : ℝ) (π / 2), ‖g k x‖ := by
    refine Summable.of_nonneg_of_le
      (fun _ => MeasureTheory.integral_nonneg fun _ => norm_nonneg _) ?_
      (hsum.mul_right (π / 2))
    intro k
    have hbd' : ∀ x ∈ Set.Ioc (0 : ℝ) (π / 2), ‖g k x‖ ≤ b k := by
      intro x _
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn k x)]
      exact hbd k x
    have hle :=
      MeasureTheory.setIntegral_mono_on (hint k).norm
        (continuous_const.integrableOn_Ioc) measurableSet_Ioc hbd'
    have hvol : ∫ x in Set.Ioc (0 : ℝ) (π / 2), b k = b k * (π / 2) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
      have : MeasureTheory.volume.real (Set.Ioc (0 : ℝ) (π / 2)) = π / 2 := by
        simp [div_nonneg pi_pos.le (by norm_num : (0 : ℝ) ≤ 2)]
      rw [this, mul_comm]
    exact hle.trans_eq hvol
  have := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum'
  rw [this]
  exact (intervalIntegral.integral_of_le (div_nonneg pi_pos.le (by norm_num))).symm

lemma continuous_inner_series_term (n : ℕ) (a : ℝ) :
    Continuous fun b : ℝ =>
      ((4620 * (n : ℝ) + 659) / 169) *
        ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n := by
  unfold YAB
  fun_prop

lemma tsum_inner_b (a : ℝ) :
    ∫ b in (0 : ℝ)..(π / 2),
        ∑' n : ℕ,
          ((4620 * (n : ℝ) + 659) / 169) *
            ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n =
      ∑' n : ℕ,
        ∫ b in (0 : ℝ)..(π / 2),
          ((4620 * (n : ℝ) + 659) / 169) *
            ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n :=
  (tsum_interval_half_of_bound
    (fun n b => ((4620 * (n : ℝ) + 659) / 169) *
      ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n)
    (fun n => ((4620 * (n : ℝ) + 659) / 169) * ((73 : ℝ) / 169) ^ n)
    (fun n => continuous_inner_series_term n a)
    (fun n b => series_term_nonneg n a b)
    (fun n b => series_term_le n a b)
    summable_series_bound).symm

lemma combo_inner_eq_tsum (a : ℝ) :
    ∫ b in (0 : ℝ)..(π / 2),
        (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
          127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) =
      ∑' n : ℕ,
        ∫ b in (0 : ℝ)..(π / 2),
          ((4620 * (n : ℝ) + 659) / 169) *
            ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n := by
  have hcongr :
      ∫ b in (0 : ℝ)..(π / 2),
          (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
            127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) =
        ∫ b in (0 : ℝ)..(π / 2),
          ∑' n : ℕ,
            ((4620 * (n : ℝ) + 659) / 169) *
              ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n := by
    refine intervalIntegral.integral_congr ?_
    intro b _
    exact combo_as_series a b
  rw [hcongr, tsum_inner_b]

lemma continuous_integrated_term (n : ℕ) :
    Continuous fun a : ℝ =>
      ∫ b in (0 : ℝ)..(π / 2),
        ((4620 * (n : ℝ) + 659) / 169) *
          ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_series_term n) 0 (π / 2)

lemma integrated_term_nonneg (n : ℕ) (a : ℝ) :
    0 ≤ ∫ b in (0 : ℝ)..(π / 2),
      ((4620 * (n : ℝ) + 659) / 169) *
        ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n :=
  intervalIntegral.integral_nonneg (div_nonneg pi_pos.le (by norm_num))
    fun b _ => series_term_nonneg n a b

lemma integrated_term_le (n : ℕ) (a : ℝ) :
    ∫ b in (0 : ℝ)..(π / 2),
        ((4620 * (n : ℝ) + 659) / 169) *
          ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n ≤
      ((4620 * (n : ℝ) + 659) / 169) * ((73 : ℝ) / 169) ^ n * (π / 2) := by
  have h01 : IntervalIntegrable
      (fun b : ℝ =>
        ((4620 * (n : ℝ) + 659) / 169) *
          ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n)
      MeasureTheory.volume (0 : ℝ) (π / 2) :=
    (continuous_inner_series_term n a).intervalIntegrable _ _
  have hconstI : IntervalIntegrable
      (fun _ : ℝ => ((4620 * (n : ℝ) + 659) / 169) * ((73 : ℝ) / 169) ^ n)
      MeasureTheory.volume (0 : ℝ) (π / 2) :=
    continuous_const.intervalIntegrable _ _
  have hmono :=
    intervalIntegral.integral_mono_on
      (div_nonneg pi_pos.le (by norm_num))
      h01 hconstI
      (fun b _ => series_term_le n a b)
  have hconst :
      ∫ _b in (0 : ℝ)..(π / 2),
          ((4620 * (n : ℝ) + 659) / 169) * ((73 : ℝ) / 169) ^ n =
        ((4620 * (n : ℝ) + 659) / 169) * ((73 : ℝ) / 169) ^ n * (π / 2) := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
    ring
  exact hmono.trans_eq hconst

lemma tsum_outer_a :
    ∫ a in (0 : ℝ)..(π / 2),
        ∑' n : ℕ,
          ∫ b in (0 : ℝ)..(π / 2),
            ((4620 * (n : ℝ) + 659) / 169) *
              ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n =
      ∑' n : ℕ,
        ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            ((4620 * (n : ℝ) + 659) / 169) *
              ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n :=
  (tsum_interval_half_of_bound
    (fun n a =>
      ∫ b in (0 : ℝ)..(π / 2),
        ((4620 * (n : ℝ) + 659) / 169) *
          ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n)
    (fun n => ((4620 * (n : ℝ) + 659) / 169) * ((73 : ℝ) / 169) ^ n * (π / 2))
    continuous_integrated_term
    integrated_term_nonneg
    integrated_term_le
    (summable_series_bound.mul_right (π / 2))).symm

lemma combo_integral_eq_tsum :
    ∫ a in (0 : ℝ)..(π / 2),
        ∫ b in (0 : ℝ)..(π / 2),
          (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
            127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) =
      ∑' n : ℕ,
        ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            ((4620 * (n : ℝ) + 659) / 169) *
              ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n := by
  have hinner :
      ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
              127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) =
        ∫ a in (0 : ℝ)..(π / 2),
          ∑' n : ℕ,
            ∫ b in (0 : ℝ)..(π / 2),
              ((4620 * (n : ℝ) + 659) / 169) *
                ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n := by
    refine intervalIntegral.integral_congr ?_
    intro a _
    exact combo_inner_eq_tsum a
  rw [hinner, tsum_outer_a]

lemma series_coeff_nonneg (n : ℕ) :
    0 ≤ ((4620 * (n : ℝ) + 659) / 169) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) := by
  positivity

lemma integral_series_term_eq (n : ℕ) :
    ∫ a in (0 : ℝ)..(π / 2),
        ∫ b in (0 : ℝ)..(π / 2),
          ((4620 * (n : ℝ) + 659) / 169) *
            ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n =
      ((4620 * (n : ℝ) + 659) / 169) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) *
        ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2), (YAB a b) ^ n := by
  have hconst :
      ∀ a : ℝ,
        ∫ b in (0 : ℝ)..(π / 2),
            ((4620 * (n : ℝ) + 659) / 169) *
              ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) * (YAB a b) ^ n =
          ((4620 * (n : ℝ) + 659) / 169) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) *
            ∫ b in (0 : ℝ)..(π / 2), (YAB a b) ^ n := by
    intro a
    simpa [mul_assoc] using
      (intervalIntegral.integral_const_mul
        (((4620 * (n : ℝ) + 659) / 169) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n))
        (fun b : ℝ => (YAB a b) ^ n))
  simp_rw [hconst]
  simpa [mul_assoc] using
    (intervalIntegral.integral_const_mul
      (((4620 * (n : ℝ) + 659) / 169) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n))
      (fun a : ℝ => ∫ b in (0 : ℝ)..(π / 2), (YAB a b) ^ n))

/-- Three-term splitting of `YAB`. -/
lemma YAB_add3 (a b : ℝ) :
    YAB a b =
      (9 / 169) * cos a ^ 2 + (48 / 169) * cos b ^ 2 +
        (16 / 169) * (cos a ^ 2 * cos b ^ 2) := by
  unfold YAB
  ring

lemma YAB_pow_sum (n : ℕ) (a b : ℝ) :
    (YAB a b) ^ n =
      ∑ k ∈ range (n + 1),
        ∑ j ∈ range (k + 1),
          (n.choose k : ℝ) * (k.choose j : ℝ) *
            ((9 : ℝ) / 169 * cos a ^ 2) ^ j *
              ((48 : ℝ) / 169 * cos b ^ 2) ^ (k - j) *
                ((16 : ℝ) / 169 * (cos a ^ 2 * cos b ^ 2)) ^ (n - k) := by
  rw [YAB_add3, add_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [add_pow]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  ring

lemma integral_cos_pow_mul_cos_pow (p q : ℕ) :
    ∫ a in (0 : ℝ)..(π / 2),
        ∫ b in (0 : ℝ)..(π / 2),
          (cos a) ^ (2 * p) * (cos b) ^ (2 * q) =
      (π / 2) * ((p.centralBinom : ℝ) / (4 : ℝ) ^ p) *
        ((π / 2) * ((q.centralBinom : ℝ) / (4 : ℝ) ^ q)) := by
  have ha :
      ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            (cos a) ^ (2 * p) * (cos b) ^ (2 * q) =
        ∫ a in (0 : ℝ)..(π / 2),
          (cos a) ^ (2 * p) * ∫ b in (0 : ℝ)..(π / 2), (cos b) ^ (2 * q) := by
    refine intervalIntegral.integral_congr ?_
    intro a _
    simpa [mul_comm] using
      (intervalIntegral.integral_const_mul ((cos a) ^ (2 * p))
        (fun b : ℝ => (cos b) ^ (2 * q))).symm
  rw [ha, intervalIntegral.integral_mul_const, integral_cos_pow_two_mul_half p,
    integral_cos_pow_two_mul_half q]

/-- The remaining half-square integral after clearing the constant `196`. -/
lemma half_square_combo_eval :
    ∫ a in (0 : ℝ)..(π / 2),
        ∫ b in (0 : ℝ)..(π / 2),
          (30030 * (DeltaAB a b) ^ (-((3 : ℝ) / 2)) -
            127 * (DeltaAB a b) ^ (-((1 : ℝ) / 2))) =
      55 * π / 8 := by
  rw [combo_integral_eq_tsum]
  simp_rw [integral_series_term_eq]
  sorry

lemma sq_pow_mul (x : ℝ) (p q : ℕ) :
    (x ^ 2) ^ p * (x ^ 2) ^ q = x ^ (2 * (p + q)) := by
  rw [← pow_add, ← pow_mul]

lemma YAB_term_as_cos (n k j : ℕ) (a b : ℝ) :
    ((9 : ℝ) / 169 * cos a ^ 2) ^ j *
      ((48 : ℝ) / 169 * cos b ^ 2) ^ (k - j) *
        ((16 : ℝ) / 169 * (cos a ^ 2 * cos b ^ 2)) ^ (n - k) =
      ((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k) *
        cos a ^ (2 * (j + (n - k))) * cos b ^ (2 * ((k - j) + (n - k))) := by
  simp only [mul_pow]
  trans
    ((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k) *
      ((cos a ^ 2) ^ j * (cos a ^ 2) ^ (n - k)) *
        ((cos b ^ 2) ^ (k - j) * (cos b ^ 2) ^ (n - k))
  · ring
  · rw [sq_pow_mul (cos a) j (n - k), sq_pow_mul (cos b) (k - j) (n - k)]

lemma integral_YAB_term (n k j : ℕ) :
    ∫ a in (0 : ℝ)..(π / 2),
        ∫ b in (0 : ℝ)..(π / 2),
          ((9 : ℝ) / 169 * cos a ^ 2) ^ j *
            ((48 : ℝ) / 169 * cos b ^ 2) ^ (k - j) *
              ((16 : ℝ) / 169 * (cos a ^ 2 * cos b ^ 2)) ^ (n - k) =
      ((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k) *
        ((π / 2) * (((j + (n - k)).centralBinom : ℝ) / (4 : ℝ) ^ (j + (n - k))) *
          ((π / 2) * ((((k - j) + (n - k)).centralBinom : ℝ) /
            (4 : ℝ) ^ ((k - j) + (n - k))))) := by
  have hcongr :
      ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            ((9 : ℝ) / 169 * cos a ^ 2) ^ j *
              ((48 : ℝ) / 169 * cos b ^ 2) ^ (k - j) *
                ((16 : ℝ) / 169 * (cos a ^ 2 * cos b ^ 2)) ^ (n - k) =
        ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            ((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k) *
              cos a ^ (2 * (j + (n - k))) * cos b ^ (2 * ((k - j) + (n - k))) := by
    refine intervalIntegral.integral_congr ?_
    intro a _
    refine intervalIntegral.integral_congr ?_
    intro b _
    exact YAB_term_as_cos n k j a b
  rw [hcongr]
  have hpull :
      ∫ a in (0 : ℝ)..(π / 2),
          ∫ b in (0 : ℝ)..(π / 2),
            ((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k) *
              cos a ^ (2 * (j + (n - k))) * cos b ^ (2 * ((k - j) + (n - k))) =
        ((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k) *
          ∫ a in (0 : ℝ)..(π / 2),
            ∫ b in (0 : ℝ)..(π / 2),
              cos a ^ (2 * (j + (n - k))) * cos b ^ (2 * ((k - j) + (n - k))) := by
    have hconst (a : ℝ) :
        ∫ b in (0 : ℝ)..(π / 2),
            ((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k) *
              cos a ^ (2 * (j + (n - k))) * cos b ^ (2 * ((k - j) + (n - k))) =
          ((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k) *
            ∫ b in (0 : ℝ)..(π / 2),
              cos a ^ (2 * (j + (n - k))) * cos b ^ (2 * ((k - j) + (n - k))) := by
      simpa [mul_assoc] using
        (intervalIntegral.integral_const_mul
          (((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k))
          (fun b : ℝ => cos a ^ (2 * (j + (n - k))) * cos b ^ (2 * ((k - j) + (n - k)))))
    simp_rw [hconst]
    simpa [mul_assoc] using
      (intervalIntegral.integral_const_mul
        (((9 : ℝ) / 169) ^ j * ((48 : ℝ) / 169) ^ (k - j) * ((16 : ℝ) / 169) ^ (n - k))
        (fun a : ℝ =>
          ∫ b in (0 : ℝ)..(π / 2),
            cos a ^ (2 * (j + (n - k))) * cos b ^ (2 * ((k - j) + (n - k)))))
  rw [hpull, integral_cos_pow_mul_cos_pow]

lemma centralBinom_div_four_succ (n : ℕ) :
    ((n + 1).centralBinom : ℝ) / (4 : ℝ) ^ (n + 1) =
      ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) *
        ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) := by
  have h := prod_odd_div_even (n + 1)
  rw [prod_range_succ, prod_odd_div_even n] at h
  have : (2 : ℝ) * n + 2 = 2 * ((n : ℝ) + 1) := by ring
  simpa [this] using h.symm

lemma integral_sin_pow_diff (n : ℕ) :
    ∫ x in (0 : ℝ)..(π / 2), (sin x ^ (2 * n) - sin x ^ (2 * (n + 1))) =
      (π / 2) * ((n.centralBinom : ℝ) / (4 : ℝ) ^ n) *
        (1 / (2 * ((n : ℝ) + 1))) := by
  have h1 : Continuous (fun x : ℝ => sin x ^ (2 * n)) := continuous_sin.pow _
  have h2 : Continuous (fun x : ℝ => sin x ^ (2 * (n + 1))) := continuous_sin.pow _
  rw [intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    integral_sin_pow_two_mul_half n, integral_sin_pow_two_mul_half (n + 1),
    centralBinom_div_four_succ]
  have hn : (n : ℝ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp [hn]
  ring

lemma ring_choose_neg_half_mul (n : ℕ) (r : ℝ) :
    Ring.choose (-((1 : ℝ) / 2)) n * (-((4 : ℝ) * r)) ^ n =
      (n.centralBinom : ℝ) * r ^ n := by
  rw [ring_choose_neg_one_half]
  have h4 : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hneg : (-((4 : ℝ) * r)) ^ n = (-1 : ℝ) ^ n * (4 : ℝ) ^ n * r ^ n := by
    have : -((4 : ℝ) * r) = (-1 : ℝ) * 4 * r := by ring
    rw [this, mul_assoc, mul_pow, mul_pow]
    ring
  rw [hneg]
  have hsgn : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  field_simp [h4]
  try simp [hsgn]
  try ring

lemma centralBinom_generating {r : ℝ} (hr : |4 * r| < 1) :
    (1 - 4 * r) ^ (-((1 : ℝ) / 2)) =
      ∑' n : ℕ, (n.centralBinom : ℝ) * r ^ n := by
  have hx : |(-((4 : ℝ) * r))| < 1 := by simpa [abs_neg] using hr
  have h := one_add_rpow_eq_tsum (a := -((1 : ℝ) / 2)) hx
  have h1 : (1 : ℝ) + -((4 : ℝ) * r) = 1 - 4 * r := by ring
  rw [← h1, h]
  exact tsum_congr fun n => ring_choose_neg_half_mul n r

lemma double_integral_eval :
    ∫ u in (0 : ℝ)..π,
        ∫ v in (0 : ℝ)..π,
          (367 + 1778 * ((7 + cos u) * (17 + 8 * cos v) / 392)) /
            (1 - (7 + cos u) * (17 + 8 * cos v) / 392) ^ ((3 : ℝ) / 2) =
      5390 * π := by
  have hrew : ∀ u v : ℝ,
      (367 + 1778 * ((7 + cos u) * (17 + 8 * cos v) / 392)) /
          (1 - (7 + cos u) * (17 + 8 * cos v) / 392) ^ ((3 : ℝ) / 2) =
        (367 + 1778 * Auv u v) / (1 - Auv u v) ^ ((3 : ℝ) / 2) := by
    intro u v; unfold Auv; rfl
  simp_rw [hrew, remaining_to_half_square, remaining_half_as_Delta, half_square_combo_eval]
  ring

/--
Conjecture 2 (i): We have $\sum_{k \ge 0} t(k) = 5390/\pi$.

Denote (4290k+367)/3136^k*C(2k,k)*T_k(14,1)*T_k(17,16) by t(k).
(i) We have Sum_{k>=0}t(k) = 5390/Pi.
-/
theorem oeis_a336981_conjecture_2_i :
  (∑' (k : ℕ), t k) = 5390 / Real.pi := by
  rw [tsum_eq_triple_of_closed, triple_to_double, double_integral_eval]
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp [hπ]
  try ring


