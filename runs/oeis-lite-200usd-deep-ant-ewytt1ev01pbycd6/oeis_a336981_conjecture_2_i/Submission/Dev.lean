import Mathlib
open Nat Finset
open scoped BigOperators

noncomputable def T_k (k : ℕ) (b c : ℤ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) (fun i : ℕ =>
    ((k.choose i * (k - i).choose i : ℕ) : ℚ) *
    ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i))

/-- Summand of the binomial expansion of `(b+d)^k`. -/
private def gsum (k b d j : ℕ) : ℚ := ((k.choose j : ℕ):ℚ) * ((b:ℚ)^j * (d:ℚ)^(k-j))

private lemma gsum_nonneg (k b d j : ℕ) : 0 ≤ gsum k b d j := by
  unfold gsum; positivity

-- Tight bound: T_k k b c ≤ (b+d)^k  when 4c ≤ d^2 (all naturals).
lemma T_k_le (k b c d : ℕ) (hcd : 4 * c ≤ d ^ 2) :
    T_k k (b:ℤ) (c:ℤ) ≤ (((b + d : ℕ)) : ℚ) ^ k := by
  -- RHS as a binomial sum
  have hrhs : (((b + d : ℕ)) : ℚ) ^ k = ∑ j ∈ range (k+1), gsum k b d j := by
    have hbd : (((b + d : ℕ)) : ℚ) = (b:ℚ) + (d:ℚ) := by push_cast; ring
    rw [hbd, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    unfold gsum
    ring
  rw [hrhs, T_k]
  -- termwise bound: each T_k-summand ≤ gsum (k - 2*i)
  have step1 : ∀ i ∈ range (k/2+1),
      ((k.choose i * (k - i).choose i : ℕ) : ℚ) * ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i)
        ≤ gsum k b d (k - 2*i) := by
    intro i hi
    simp only [mem_range] at hi
    have hik : 2 * i ≤ k := by omega
    -- choose_mul identity: C(k,i)C(k-i,i) = C(k,2i) C(2i,i)
    have hcm : k.choose i * (k - i).choose i = k.choose (2*i) * (2*i).choose i := by
      have h := Nat.choose_mul (n := k) (k := 2*i) (s := i) (by omega)
      have h2i : 2 * i - i = i := by omega
      rw [h2i] at h
      omega
    -- C(2i,i) ≤ 4^i
    have hcb : ((2*i).choose i : ℕ) ≤ 4 ^ i := by
      have := Nat.choose_le_two_pow (2*i) i
      calc (2*i).choose i ≤ 2 ^ (2*i) := this
        _ = 4 ^ i := by rw [pow_mul]; norm_num
    -- k - 2*i has the right binomial coefficient and powers
    have hjk : k - (k - 2*i) = 2 * i := by omega
    have hchoose : k.choose (k - 2*i) = k.choose (2*i) := Nat.choose_symm hik
    -- reduce to: C(2i,i) * c^i ≤ d^(2i)
    have hnat : (2*i).choose i * c^i ≤ d^(2*i) := by
      calc (2*i).choose i * c^i ≤ 4^i * c^i := mul_le_mul_right' hcb (c^i)
        _ = (4*c)^i := by rw [mul_pow]
        _ ≤ (d^2)^i := Nat.pow_le_pow_left hcd i
        _ = d^(2*i) := by rw [← pow_mul, Nat.mul_comm]
    have key : ((2*i).choose i : ℚ) * (c:ℚ)^i ≤ (d:ℚ)^(2*i) := by
      calc ((2*i).choose i : ℚ) * (c:ℚ)^i = (((2*i).choose i * c^i : ℕ):ℚ) := by push_cast; ring
        _ ≤ ((d^(2*i):ℕ):ℚ) := by exact_mod_cast hnat
        _ = (d:ℚ)^(2*i) := by push_cast; ring
    -- combine
    unfold gsum
    rw [hcm, hjk, hchoose]
    have hcast : ((k.choose (2*i) * (2*i).choose i : ℕ) : ℚ)
        = (k.choose (2*i) : ℚ) * ((2*i).choose i : ℚ) := by push_cast; ring
    rw [hcast]
    calc (k.choose (2*i) : ℚ) * ((2*i).choose i : ℚ) * ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i)
        = (k.choose (2*i) : ℚ) * (b:ℚ)^(k-2*i) * (((2*i).choose i : ℚ) * (c:ℚ)^i) := by ring
      _ ≤ (k.choose (2*i) : ℚ) * (b:ℚ)^(k-2*i) * ((d:ℚ)^(2*i)) := by
          apply mul_le_mul_of_nonneg_left key (by positivity)
      _ = (k.choose (2*i) : ℚ) * ((b:ℚ)^(k-2*i) * (d:ℚ)^(2*i)) := by ring
  -- Now sum the termwise bound and reindex
  calc ∑ i ∈ range (k/2+1),
        ((k.choose i * (k - i).choose i : ℕ) : ℚ) * ((b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i)
      ≤ ∑ i ∈ range (k/2+1), gsum k b d (k - 2*i) := Finset.sum_le_sum step1
    _ = ∑ j ∈ (range (k/2+1)).image (fun i => k - 2*i), gsum k b d j := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        have hx' := Finset.mem_range.mp hx
        have hy' := Finset.mem_range.mp hy
        simp only at hxy
        omega
    _ ≤ ∑ j ∈ range (k+1), gsum k b d j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_image, mem_range] at hj ⊢
          obtain ⟨i, hi, rfl⟩ := hj
          omega
        · intro j _ _
          exact gsum_nonneg k b d j

#check @T_k_le

lemma T_k_nonneg (k : ℕ) (b c : ℤ) (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ T_k k b c := by
  unfold T_k
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact_mod_cast Nat.zero_le _
  · apply mul_nonneg <;> apply pow_nonneg
    · exact_mod_cast hb
    · exact_mod_cast hc

lemma centralBinom_le (k : ℕ) : (Nat.choose (2*k) k : ℕ) ≤ 4 ^ k := by
  have hmem : k ∈ range (2*k+1) := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (f := fun j => (2*k).choose j)
    (fun j _ => Nat.zero_le _) hmem
  rw [Nat.sum_range_choose (2*k)] at h
  calc (2*k).choose k ≤ 2 ^ (2*k) := h
    _ = 4 ^ k := by rw [pow_mul]; norm_num

-- Copy of the `t` from Spec.lean (for verifying summability of the actual summand).
noncomputable def t (k : ℕ) : ℝ :=
  let T1k : ℝ := T_k k 14 1
  let T2k : ℝ := T_k k 17 16
  let k_r : ℝ := k
  let central_binomial : ℝ := (Nat.choose (2 * k) k : ℝ)
  let term_factor : ℝ := 4290 * k_r + 367
  let power_factor : ℝ := (3136 : ℝ) ^ k
  term_factor / power_factor * central_binomial * T1k * T2k

lemma t_nonneg (k : ℕ) : 0 ≤ t k := by
  have h1 : (0:ℝ) ≤ ((T_k k 14 1 : ℚ) : ℝ) := by
    exact_mod_cast T_k_nonneg k 14 1 (by norm_num) (by norm_num)
  have h2 : (0:ℝ) ≤ ((T_k k 17 16 : ℚ) : ℝ) := by
    exact_mod_cast T_k_nonneg k 17 16 (by norm_num) (by norm_num)
  unfold t
  simp only
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  · positivity
  · positivity
  · exact h1
  · exact h2

lemma t_le_bound (k : ℕ) : t k ≤ (4290 * (k:ℝ) + 367) * (25/49:ℝ)^k := by
  have hCB : (Nat.choose (2*k) k : ℝ) ≤ (4:ℝ)^k := by exact_mod_cast centralBinom_le k
  have hT1 : ((T_k k 14 1 : ℚ):ℝ) ≤ (16:ℝ)^k := by
    have := T_k_le k 14 1 2 (by norm_num)
    have h16 : ((14 + 2 : ℕ):ℚ) = 16 := by norm_num
    rw [h16] at this
    calc ((T_k k 14 1 : ℚ):ℝ) ≤ ((16^k : ℚ):ℝ) := by exact_mod_cast this
      _ = (16:ℝ)^k := by push_cast; ring
  have hT2 : ((T_k k 17 16 : ℚ):ℝ) ≤ (25:ℝ)^k := by
    have := T_k_le k 17 16 8 (by norm_num)
    have h25 : ((17 + 8 : ℕ):ℚ) = 25 := by norm_num
    rw [h25] at this
    calc ((T_k k 17 16 : ℚ):ℝ) ≤ ((25^k : ℚ):ℝ) := by exact_mod_cast this
      _ = (25:ℝ)^k := by push_cast; ring
  have hT1n : (0:ℝ) ≤ ((T_k k 14 1:ℚ):ℝ) := by
    exact_mod_cast T_k_nonneg k 14 1 (by norm_num) (by norm_num)
  have hT2n : (0:ℝ) ≤ ((T_k k 17 16:ℚ):ℝ) := by
    exact_mod_cast T_k_nonneg k 17 16 (by norm_num) (by norm_num)
  have hCBn : (0:ℝ) ≤ (Nat.choose (2*k) k : ℝ) := by positivity
  have hA : (0:ℝ) ≤ (4290*(k:ℝ)+367)/(3136:ℝ)^k := by positivity
  unfold t
  simp only
  have hpow : (4:ℝ)^k * (16:ℝ)^k * (25:ℝ)^k / (3136:ℝ)^k = (25/49:ℝ)^k := by
    rw [← mul_pow, ← mul_pow, ← div_pow]
    norm_num
  calc (4290*(k:ℝ)+367)/(3136:ℝ)^k * (Nat.choose (2*k) k:ℝ)
          * ((T_k k 14 1:ℚ):ℝ) * ((T_k k 17 16:ℚ):ℝ)
      ≤ (4290*(k:ℝ)+367)/(3136:ℝ)^k * (4:ℝ)^k * (16:ℝ)^k * (25:ℝ)^k := by
        gcongr
    _ = (4290*(k:ℝ)+367) * (25/49:ℝ)^k := by rw [← hpow]; ring

lemma bound_summable :
    Summable (fun k : ℕ => (4290 * (k:ℝ) + 367) * (25/49:ℝ)^k) := by
  have hr : ‖(25/49 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
  have s1 : Summable (fun k : ℕ => (k:ℝ)^1 * (25/49:ℝ)^k) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have s0 : Summable (fun k : ℕ => ((25/49:ℝ))^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hcomb := (s1.mul_left 4290).add (s0.mul_left 367)
  apply hcomb.congr
  intro k
  simp only [pow_one]
  ring

theorem t_summable : Summable t :=
  Summable.of_nonneg_of_le t_nonneg t_le_bound bound_summable

#check @t_summable

#print axioms t_summable
