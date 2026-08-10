import FormalConjectures.Util.ProblemImports

open Nat Finset Real Filter Topology

/--
A386660: $a(n) = \sum_{k=1}^n \binom{n}{k} \pmod{2^k}$.
-/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sum fun k => (n.choose k) % (2 ^ k)

noncomputable section

/-- The term sequence `t j = C(n,j) k^j (n-k)^(n-j)`. -/
def tt (n k j : ℕ) : ℕ := n.choose j * k ^ j * (n - k) ^ (n - j)

/-- Sum of all terms is `n^n`. -/
lemma tt_sum (n k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ Finset.range (n + 1), tt n k j = n ^ n := by
  have h := add_pow k (n - k) n
  rw [Nat.add_sub_cancel' hk] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  unfold tt
  simp only [Nat.cast_id]
  ring

/-- The recurrence identity. -/
lemma tt_rec (n k j : ℕ) (hj : j + 1 ≤ n) :
    tt n k (j + 1) * ((j + 1) * (n - k)) = tt n k j * ((n - j) * k) := by
  unfold tt
  have hpow_k : k ^ (j + 1) = k ^ j * k := by ring
  have hnj : n - j = (n - (j + 1)) + 1 := by omega
  have hpow_nk : (n - k) ^ (n - j) = (n - k) ^ (n - (j + 1)) * (n - k) := by
    rw [hnj]; ring
  have hchoose : n.choose (j + 1) * (j + 1) = n.choose j * (n - j) :=
    Nat.choose_succ_right_eq n j
  rw [hpow_k, hpow_nk]
  -- LHS: choose n (j+1) * (k^j*k) * (n-k)^(n-(j+1)) * ((j+1)*(n-k))
  -- RHS: choose n j * k^j * ((n-k)^(n-(j+1))*(n-k)) * ((n-j)*k)
  -- rearrange
  calc n.choose (j + 1) * (k ^ j * k) * (n - k) ^ (n - (j + 1)) * ((j + 1) * (n - k))
      = (n.choose (j + 1) * (j + 1)) * (k ^ j * k * (n - k) ^ (n - (j + 1)) * (n - k)) := by ring
    _ = (n.choose j * (n - j)) * (k ^ j * k * (n - k) ^ (n - (j + 1)) * (n - k)) := by rw [hchoose]
    _ = n.choose j * k ^ j * ((n - k) ^ (n - (j + 1)) * (n - k)) * ((n - j) * k) := by ring

/-- Step up: below the mode, terms increase. -/
lemma tt_step_up (n k j : ℕ) (hk : 0 < k) (hkn : k < n) (hjk : j + 1 ≤ k) :
    tt n k j ≤ tt n k (j + 1) := by
  have hjn : j + 1 ≤ n := by omega
  have hle : (j + 1) * (n - k) ≤ (n - j) * k := by
    zify [hkn.le, (by omega : j ≤ n)]
    nlinarith [hjk, hkn, (by omega : j ≤ n)]
  have key := tt_rec n k j hjn
  have hpos : 0 < (j + 1) * (n - k) := by
    apply Nat.mul_pos <;> omega
  have h1 : tt n k j * ((j + 1) * (n - k)) ≤ tt n k (j + 1) * ((j + 1) * (n - k)) := by
    rw [key]
    exact mul_le_mul_left' hle (tt n k j)
  exact Nat.le_of_mul_le_mul_right h1 hpos

/-- Step down: above the mode, terms decrease. -/
lemma tt_step_down (n k j : ℕ) (hk : 0 < k) (hkn : k < n) (hkj : k ≤ j) (hjn : j + 1 ≤ n) :
    tt n k (j + 1) ≤ tt n k j := by
  have hle : (n - j) * k ≤ (j + 1) * (n - k) := by
    zify [hkn.le, (by omega : j ≤ n)]
    nlinarith [hkj, hkn, (by omega : j ≤ n)]
  have key := tt_rec n k j hjn
  have hpos : 0 < (j + 1) * (n - k) := by
    apply Nat.mul_pos <;> omega
  have h1 : tt n k (j + 1) * ((j + 1) * (n - k)) ≤ tt n k j * ((j + 1) * (n - k)) := by
    rw [key]
    exact mul_le_mul_left' hle (tt n k j)
  exact Nat.le_of_mul_le_mul_right h1 hpos

/-- The mode is at `j = k`: all terms are bounded by `tt n k k`. -/
lemma tt_le_mode (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    ∀ j, j ≤ n → tt n k j ≤ tt n k k := by
  -- first: increasing up to k
  have up : ∀ i, i ≤ k → tt n k (k - i) ≤ tt n k k := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 : tt n k (k - (m + 1)) ≤ tt n k (k - (m + 1) + 1) :=
        tt_step_up n k (k - (m + 1)) hk hkn (by omega)
      have heq : k - (m + 1) + 1 = k - m := by omega
      rw [heq] at h1
      exact h1.trans (ih (by omega))
  have down : ∀ i, k + i ≤ n → tt n k (k + i) ≤ tt n k k := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h1 : tt n k (k + m + 1) ≤ tt n k (k + m) :=
        tt_step_down n k (k + m) hk hkn (by omega) (by omega)
      have : tt n k (k + (m + 1)) ≤ tt n k (k + m) := by
        rw [show k + (m + 1) = k + m + 1 by ring]; exact h1
      exact this.trans (ih (by omega))
  intro j hj
  rcases le_or_gt j k with h | h
  · have := up (k - j) (by omega)
    rwa [show k - (k - j) = j by omega] at this
  · have := down (j - k) (by omega)
    rwa [show k + (j - k) = j by omega] at this

/-- Upper bound: `C(n,k) * k^k * (n-k)^(n-k) ≤ n^n`. -/
lemma tt_mode_le (n k : ℕ) (hk : k ≤ n) : tt n k k ≤ n ^ n := by
  rw [← tt_sum n k hk]
  apply Finset.single_le_sum (f := tt n k)
  · intro i _; exact Nat.zero_le _
  · exact Finset.mem_range.mpr (by omega)

/-- Lower bound: `n^n ≤ (n+1) * (C(n,k) * k^k * (n-k)^(n-k))`. -/
lemma le_tt_mode (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    n ^ n ≤ (n + 1) * tt n k k := by
  rw [← tt_sum n k hkn.le]
  calc ∑ j ∈ Finset.range (n + 1), tt n k j
      ≤ ∑ _j ∈ Finset.range (n + 1), tt n k k := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact tt_le_mode n k hk hkn i (by omega)
    _ = (n + 1) * tt n k k := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

open Real in
lemma exp_mul_log (a : ℝ) (ha : 0 < a) (m : ℕ) :
    Real.exp ((m : ℝ) * Real.log a) = a ^ m := by
  rw [← Real.log_pow]
  exact Real.exp_log (pow_pos ha m)

open Real in
/-- The entropy exponential identity. -/
lemma entropy_exp (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ)))
      = (n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have hMpos : 0 < n - k := by omega
  have hM : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast hMpos
  have hMe : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hkn.le]
  have harg : (n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ))
      = (n : ℝ) * Real.log n - (k : ℝ) * Real.log k
        - ((n - k : ℕ) : ℝ) * Real.log ((n - k : ℕ) : ℝ) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    have e1 : Real.log ((k : ℝ) / (n : ℝ)) = Real.log k - Real.log n :=
      Real.log_div (ne_of_gt hK) (ne_of_gt hN)
    have e2 : (1 : ℝ) - (k : ℝ) / (n : ℝ) = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
      rw [hMe]; field_simp
    have e3 : Real.log (((n - k : ℕ) : ℝ) / (n : ℝ))
        = Real.log ((n - k : ℕ) : ℝ) - Real.log n :=
      Real.log_div (ne_of_gt hM) (ne_of_gt hN)
    rw [e2, e1, e3, hMe]
    field_simp
    ring
  rw [harg, Real.exp_sub, Real.exp_sub, exp_mul_log _ hN, exp_mul_log _ hK, exp_mul_log _ hM,
    div_div]

open Real in
lemma choose_le_entropy (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (n.choose k : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ))) := by
  rw [entropy_exp n k hk hkn]
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hmr : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - k)
  have hden : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) :=
    mul_pos (pow_pos hkr k) (pow_pos hmr _)
  rw [le_div_iff₀ hden]
  have hnat : tt n k k ≤ n ^ n := tt_mode_le n k hkn.le
  have hc := (Nat.cast_le (α := ℝ)).mpr hnat
  unfold tt at hc
  push_cast at hc
  rw [← mul_assoc]
  exact hc

open Real in
lemma entropy_le_choose (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / (n : ℝ))) / ((n : ℝ) + 1)
      ≤ (n.choose k : ℝ) := by
  rw [entropy_exp n k hk hkn]
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hmr : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - k)
  have hden : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) :=
    mul_pos (pow_pos hkr k) (pow_pos hmr _)
  rw [div_div, div_le_iff₀ (by positivity)]
  have hnat : n ^ n ≤ (n + 1) * tt n k k := le_tt_mode n k hk hkn
  have hc := (Nat.cast_le (α := ℝ)).mpr hnat
  unfold tt at hc
  push_cast at hc
  exact hc.trans_eq (by ring)

open Real in
lemma exists_xstar : ∃ x : ℝ, 1 / 2 < x ∧ x < 1 ∧ Real.binEntropy x = x * Real.log 2 := by
  set g : ℝ → ℝ := fun x => Real.binEntropy x - x * Real.log 2 with hg
  have hcont : Continuous g := by
    apply Continuous.sub Real.binEntropy_continuous
    exact continuous_id.mul continuous_const
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg1 : g 1 = -Real.log 2 := by simp [hg]
  have hghalf : g (1 / 2) = Real.log 2 / 2 := by
    have : (1 : ℝ) / 2 = 2⁻¹ := by norm_num
    rw [hg]
    simp only
    rw [this, Real.binEntropy_two_inv]
    ring
  have hmem : (0 : ℝ) ∈ Set.Icc (g 1) (g (1 / 2)) := by
    rw [hg1, hghalf]
    constructor
    · linarith
    · linarith
  have hsub := intermediate_value_Icc' (by norm_num : (1:ℝ)/2 ≤ 1) hcont.continuousOn
  obtain ⟨x, hxmem, hx0⟩ := hsub hmem
  refine ⟨x, ?_, ?_, ?_⟩
  · rcases lt_or_eq_of_le hxmem.1 with h | h
    · exact h
    · exfalso; rw [← h] at hx0; rw [hghalf] at hx0; linarith
  · rcases lt_or_eq_of_le hxmem.2 with h | h
    · exact h
    · exfalso; rw [h] at hx0; rw [hg1] at hx0; linarith
  · have : Real.binEntropy x - x * Real.log 2 = 0 := hx0
    linarith

open Real

/-- The critical point `x*`. -/
noncomputable def xs : ℝ := exists_xstar.choose

lemma xs_half : 1 / 2 < xs := exists_xstar.choose_spec.1
lemma xs_one : xs < 1 := exists_xstar.choose_spec.2.1
lemma xs_ent : Real.binEntropy xs = xs * Real.log 2 := exists_xstar.choose_spec.2.2
lemma xs_pos : 0 < xs := by have := xs_half; linarith

/-- The limit exponent `c = x* * log 2`. -/
noncomputable def cc : ℝ := xs * Real.log 2

lemma cc_pos : 0 < cc := by
  rw [cc]; exact mul_pos xs_pos (Real.log_pos (by norm_num))

lemma ent_xs : Real.binEntropy xs = cc := by rw [cc]; exact xs_ent

lemma log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- For `y ∈ [x*, 1]`, the entropy is `≤ c`. -/
lemma ent_le_cc {y : ℝ} (h1 : xs ≤ y) (h2 : y ≤ 1) : Real.binEntropy y ≤ cc := by
  have hxmem : xs ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    constructor
    · have := xs_half; norm_num; linarith
    · exact xs_one.le
  have hymem : y ∈ Set.Icc (2⁻¹ : ℝ) 1 := ⟨le_trans hxmem.1 h1, h2⟩
  have := (Real.binEntropy_strictAntiOn).antitoneOn hxmem hymem h1
  rw [ent_xs] at this
  exact this

/-- For `y ∈ (x*, 1]`, we have `binEntropy y < y * log 2`. -/
lemma ent_lt {y : ℝ} (h1 : xs < y) (h2 : y ≤ 1) : Real.binEntropy y < y * Real.log 2 := by
  have hxmem : xs ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
    constructor
    · have := xs_half; norm_num; linarith
    · exact xs_one.le
  have hymem : y ∈ Set.Icc (2⁻¹ : ℝ) 1 := ⟨le_trans hxmem.1 h1.le, h2⟩
  have hlt := (Real.binEntropy_strictAntiOn) hxmem hymem h1
  rw [xs_ent] at hlt
  have : xs * Real.log 2 < y * Real.log 2 :=
    mul_lt_mul_of_pos_right h1 log2_pos
  linarith


/-- Each summand is bounded by `exp (n * c)`. -/
lemma term_bound (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((n.choose k % 2 ^ k : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * cc) := by
  have hn1 : 1 ≤ n := le_trans hk1 hkn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  by_cases hcase : (k : ℝ) ≤ xs * n
  · -- small k: term < 2^k ≤ exp (n c)
    have hmod : n.choose k % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
    have h1 : ((n.choose k % 2 ^ k : ℕ) : ℝ) < (2 : ℝ) ^ k := by
      calc ((n.choose k % 2 ^ k : ℕ) : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hmod
        _ = (2 : ℝ) ^ k := by push_cast; ring
    have h2 : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) :=
      (exp_mul_log 2 (by norm_num) k).symm
    have h3 : (k : ℝ) * Real.log 2 ≤ (n : ℝ) * cc := by
      have := mul_le_mul_of_nonneg_right hcase log2_pos.le
      rw [cc]; nlinarith [this]
    refine le_of_lt ?_
    calc ((n.choose k % 2 ^ k : ℕ) : ℝ) < (2 : ℝ) ^ k := h1
      _ = Real.exp ((k : ℝ) * Real.log 2) := h2
      _ ≤ Real.exp ((n : ℝ) * cc) := Real.exp_le_exp.mpr h3
  · push_neg at hcase
    by_cases hkeqn : k = n
    · subst hkeqn
      rw [Nat.choose_self]
      have h2k : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
      rw [Nat.mod_eq_of_lt h2k]
      have : (0 : ℝ) ≤ (k : ℝ) * cc := mul_nonneg (by positivity) cc_pos.le
      calc ((1 : ℕ) : ℝ) = Real.exp 0 := by rw [Real.exp_zero]; norm_num
        _ ≤ Real.exp ((k : ℝ) * cc) := Real.exp_le_exp.mpr this
    · have hklt : k < n := lt_of_le_of_ne hkn hkeqn
      have h1 : ((n.choose k % 2 ^ k : ℕ) : ℝ) ≤ (n.choose k : ℝ) := by
        exact_mod_cast Nat.mod_le _ _
      have h2 : (n.choose k : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / n)) :=
        choose_le_entropy n k (by omega) hklt
      have hqbig : xs ≤ (k : ℝ) / n := by
        rw [le_div_iff₀ hnpos]; linarith [hcase]
      have hqle : (k : ℝ) / n ≤ 1 := by rw [div_le_one hnpos]; exact_mod_cast hkn
      have h3 : Real.binEntropy ((k : ℝ) / n) ≤ cc := ent_le_cc hqbig hqle
      have h4 : (n : ℝ) * Real.binEntropy ((k : ℝ) / n) ≤ (n : ℝ) * cc :=
        mul_le_mul_of_nonneg_left h3 hnpos.le
      calc ((n.choose k % 2 ^ k : ℕ) : ℝ) ≤ (n.choose k : ℝ) := h1
        _ ≤ Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / n)) := h2
        _ ≤ Real.exp ((n : ℝ) * cc) := Real.exp_le_exp.mpr h4

lemma a_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ a n := by
  unfold a
  have hmem : n ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hn, le_refl _⟩
  have h := Finset.single_le_sum (f := fun k => n.choose k % 2 ^ k)
    (fun i _ => Nat.zero_le _) hmem
  simp only [Nat.choose_self, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (show n ≠ 0 by omega))] at h
  exact h

lemma a_upper (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) ≤ (n : ℝ) * Real.exp ((n : ℝ) * cc) := by
  unfold a
  rw [Nat.cast_sum]
  have hbound : ∀ k ∈ Finset.Icc 1 n,
      ((n.choose k % 2 ^ k : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * cc) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact term_bound n k hk.1 hk.2
  calc ∑ k ∈ Finset.Icc 1 n, ((n.choose k % 2 ^ k : ℕ) : ℝ)
      ≤ ∑ _k ∈ Finset.Icc 1 n, Real.exp ((n : ℝ) * cc) := Finset.sum_le_sum hbound
    _ = ((Finset.Icc 1 n).card : ℝ) * Real.exp ((n : ℝ) * cc) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (n : ℝ) * Real.exp ((n : ℝ) * cc) := by
        rw [Nat.card_Icc]; norm_num

/-- The chosen index near `x* n`. -/
noncomputable def kk (n : ℕ) : ℕ := ⌊xs * (n : ℝ)⌋₊ + 1

lemma kk_ge_one (n : ℕ) : 1 ≤ kk n := by unfold kk; omega

lemma xs_mul_lt_kk (n : ℕ) : xs * (n : ℝ) < (kk n : ℝ) := by
  unfold kk
  push_cast
  exact Nat.lt_floor_add_one _

lemma kk_le_xs_mul_add_one (n : ℕ) : (kk n : ℝ) ≤ xs * (n : ℝ) + 1 := by
  unfold kk
  push_cast
  have : (⌊xs * (n : ℝ)⌋₊ : ℝ) ≤ xs * (n : ℝ) :=
    Nat.floor_le (mul_nonneg xs_pos.le (Nat.cast_nonneg n))
  linarith

/-- Lower bound for `a n` in terms of the entropy exponential. -/
lemma a_lower (n : ℕ) (hn : 1 ≤ n) (hkn : kk n < n) :
    Real.exp ((n : ℝ) * Real.binEntropy ((kk n : ℝ) / n)) / ((n : ℝ) + 1) ≤ (a n : ℝ) := by
  set k := kk n with hkdef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk1 : 1 ≤ k := kk_ge_one n
  have hk0 : 0 < k := hk1
  -- xs < k / n
  have hqbig : xs < (k : ℝ) / n := by
    rw [lt_div_iff₀ hnpos]
    exact xs_mul_lt_kk n
  have hqle : (k : ℝ) / n < 1 := by
    rw [div_lt_one hnpos]; exact_mod_cast hkn
  -- binEntropy (k/n) < (k/n) * log 2
  have hlt : Real.binEntropy ((k : ℝ) / n) < ((k : ℝ) / n) * Real.log 2 :=
    ent_lt hqbig hqle.le
  -- choose n k < 2 ^ k
  have hc1 : (n.choose k : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / n)) :=
    choose_le_entropy n k hk0 hkn
  have hexp_lt : Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / n)) < (2 : ℝ) ^ k := by
    rw [← exp_mul_log 2 (by norm_num) k]
    apply Real.exp_lt_exp.mpr
    have hstep : (n : ℝ) * Real.binEntropy ((k : ℝ) / n)
        < (n : ℝ) * (((k : ℝ) / n) * Real.log 2) := mul_lt_mul_of_pos_left hlt hnpos
    have heq : (n : ℝ) * (((k : ℝ) / n) * Real.log 2) = (k : ℝ) * Real.log 2 := by
      field_simp
    rw [heq] at hstep
    exact hstep
  have hchoose_lt : (n.choose k : ℝ) < (2 : ℝ) ^ k := lt_of_le_of_lt hc1 hexp_lt
  have hchoose_lt_nat : n.choose k < 2 ^ k := by
    have : (n.choose k : ℝ) < ((2 ^ k : ℕ) : ℝ) := by push_cast; exact hchoose_lt
    exact_mod_cast this
  have hmodeq : n.choose k % 2 ^ k = n.choose k := Nat.mod_eq_of_lt hchoose_lt_nat
  -- a n ≥ choose n k
  have hmem : k ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hk1, hkn.le⟩
  have hsingle := Finset.single_le_sum (f := fun j => n.choose j % 2 ^ j)
    (fun i _ => Nat.zero_le _) hmem
  dsimp only at hsingle
  rw [hmodeq] at hsingle
  have hca : (n.choose k : ℝ) ≤ (a n : ℝ) := by
    have : (n.choose k : ℝ) ≤ ((a n : ℕ) : ℝ) := by exact_mod_cast hsingle
    exact this
  exact (entropy_le_choose n k hk0 hkn).trans hca

open Filter Topology

lemma tendsto_logdiv_nat : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) := by
  have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := tendsto_pow_log_div_mul_add_atTop 1 0 1 (one_ne_zero)
    simpa using this
  exact hlogdiv.comp tendsto_natCast_atTop_atTop

lemma tendsto_log_add_one_div_nat :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have hlog1 : Tendsto (fun x : ℝ => Real.log x / (x - 1)) atTop (𝓝 0) := by
    have := tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (one_ne_zero)
    simpa using this
  have hcomp : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have h := hlog1.comp hcomp
  refine h.congr' ?_
  filter_upwards with n
  simp only [Function.comp]
  rw [add_sub_cancel_right]

/-- `kk n / n → x*`. -/
lemma tendsto_q : Tendsto (fun n : ℕ => (kk n : ℝ) / n) atTop (𝓝 xs) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => xs)
    (h := fun n : ℕ => xs + 1 / n) tendsto_const_nhds
  · have : Tendsto (fun n : ℕ => xs + 1 / (n : ℝ)) atTop (𝓝 (xs + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    simpa using this
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hnpos]
    exact (xs_mul_lt_kk n).le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hnpos, add_mul]
    have h1 : (kk n : ℝ) ≤ xs * n + 1 := kk_le_xs_mul_add_one n
    have : (1 : ℝ) / n * n = 1 := by field_simp
    rw [this]
    linarith

/-- `binEntropy (kk n / n) → c`. -/
lemma tendsto_ent : Tendsto (fun n : ℕ => Real.binEntropy ((kk n : ℝ) / n)) atTop (𝓝 cc) := by
  have hcont : Tendsto Real.binEntropy (𝓝 xs) (𝓝 (Real.binEntropy xs)) :=
    (Real.binEntropy_continuous.tendsto xs)
  rw [← ent_xs]
  exact hcont.comp tendsto_q

/-- Eventually `kk n < n`. -/
lemma eventually_kk_lt : ∀ᶠ n : ℕ in atTop, kk n < n := by
  have hxs1 : (0 : ℝ) < 1 - xs := by have := xs_one; linarith
  have hbig : Tendsto (fun n : ℕ => (n : ℝ) * (1 - xs)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hxs1 tendsto_natCast_atTop_atTop
  filter_upwards [hbig.eventually_gt_atTop 1, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 : (kk n : ℝ) ≤ xs * n + 1 := kk_le_xs_mul_add_one n
  have h2 : (kk n : ℝ) < n := by nlinarith [hn]
  exact_mod_cast h2

/-- The core limit: `log (a n) / n → c`. -/
lemma tendsto_u : Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 cc) := by
  have hUlim : Tendsto (fun n : ℕ => Real.log n / n + cc) atTop (𝓝 cc) := by
    have := tendsto_logdiv_nat.add (tendsto_const_nhds (x := cc))
    simpa using this
  have hLlim : Tendsto
      (fun n : ℕ => Real.binEntropy ((kk n : ℝ) / n) - Real.log ((n : ℝ) + 1) / n)
      atTop (𝓝 cc) := by
    have := tendsto_ent.sub tendsto_log_add_one_div_nat
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLlim hUlim ?_ ?_
  · -- lower bound eventually
    filter_upwards [eventually_kk_lt, eventually_ge_atTop 1] with n hkn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hlow := a_lower n hn1 hkn
    have han : (0 : ℝ) < a n := by
      have := a_pos n hn1
      exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
    have hpos_lhs : (0 : ℝ) <
        Real.exp ((n : ℝ) * Real.binEntropy ((kk n : ℝ) / n)) / ((n : ℝ) + 1) := by
      positivity
    have hlog := Real.log_le_log hpos_lhs hlow
    rw [Real.log_div (Real.exp_ne_zero _) (by positivity), Real.log_exp] at hlog
    -- hlog : n * binEntropy(q) - log(n+1) ≤ log (a n)
    rw [le_div_iff₀ hnpos, sub_mul, div_mul_cancel₀ _ hn0, mul_comm (Real.binEntropy _) (n : ℝ)]
    exact hlog
  · -- upper bound eventually
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hup := a_upper n hn1
    have han : (0 : ℝ) < a n := by
      have := a_pos n hn1
      exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
    have hlog := Real.log_le_log han hup
    rw [Real.log_mul hn0 (Real.exp_ne_zero _), Real.log_exp] at hlog
    -- hlog : log (a n) ≤ log n + n * cc
    rw [div_le_iff₀ hnpos, add_mul, div_mul_cancel₀ _ hn0]
    linarith [hlog]

/-- Main statement: `(a n) ^ (1/n) → exp c`. -/
lemma main_tendsto :
    Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 (Real.exp cc)) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (Real.log (a n) / n)) atTop (𝓝 (Real.exp cc)) :=
    (Real.continuous_exp.tendsto cc).comp tendsto_u
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have han : (0 : ℝ) < a n := by
    have := a_pos n hn1
    exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
  rw [Real.rpow_def_of_pos han]
  ring_nf

end

-- Conjecture based on OEIS A386660, comment C.
/--
oeis_386660_conjecture_0: The limit of $a(n)^{1/n}$ exists.
The numerical evidence suggests a limit of approximately $1.7086...$
-/
theorem oeis_386660_conjecture_0 :
  let f (n : ℕ) : ℝ := (a n : ℝ) ^ (1 / (n : ℝ))
  ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) := by
  intro f
  exact ⟨Real.exp cc, main_tendsto⟩
