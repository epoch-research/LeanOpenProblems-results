import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def c_seq : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun e IH ↦
    if h0 : e = 0 then 0
    else if h1 : e % 2 = 1 then ((2 : ℚ) ^ (e - 1)) / e
    else
      let m := e / 2
      have h_m : m < e := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by omega)
      ((4 : ℚ) ^ m) * (IH m h_m - 1 / (4 * m))

theorem c_seq_unfold (e : ℕ) : c_seq e =
    if h0 : e = 0 then 0
    else if h1 : e % 2 = 1 then ((2 : ℚ) ^ (e - 1)) / e
    else
      let m := e / 2
      have h_m : m < e := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by omega)
      ((4 : ℚ) ^ m) * (c_seq m - 1 / (4 * m)) := by
  rw [c_seq, WellFounded.fix_eq]

noncomputable def u_seq (k : ℕ) : ℚ := k * c_seq k

theorem u_seq_odd (j : ℕ) : u_seq (2 * j + 1) = (4 : ℚ) ^ j := by
  unfold u_seq
  rw [c_seq_unfold]
  have h_odd : (2 * j + 1) % 2 = 1 := by omega
  have h_ne0 : 2 * j + 1 ≠ 0 := by omega
  split_ifs
  · -- odd case
    have : (2 * j + 1 - 1) = 2 * j := by omega
    rw [this]
    have : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
      have : (4 : ℚ) = 2 ^ 2 := by norm_num
      rw [this, ← pow_mul]
    rw [this]
    have : (2 * j + 1 : ℚ) ≠ 0 := by positivity
    field_simp
    ring

theorem u_seq_even (j : ℕ) (hj : j ≥ 1) : u_seq (2 * j) = 2 * (4 : ℚ) ^ j * u_seq j - (1 / 2) * (4 : ℚ) ^ j := by
  unfold u_seq
  rw [c_seq_unfold]
  have h_even : (2 * j) % 2 = 0 := by omega
  have h_ne0 : 2 * j ≠ 0 := by omega
  split_ifs
  have h_div : 2 * j / 2 = j := by omega
  rw [h_div]
  have : (2 * j : ℚ) = 2 * (j : ℚ) := by push_cast; rfl
  rw [this]
  have : (j : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem c_seq_pos (e : ℕ) (he : e ≥ 1) : c_seq e ≥ (2 : ℚ)^(e - 1) / e := by
  induction' e using Nat.strong_induction_on with e IH
  rw [c_seq_unfold]
  have h_ne0 : e ≠ 0 := by omega
  split_ifs with h_odd
  · -- odd case
    rfl
  · -- even case
    have h_even : e % 2 = 0 := Nat.mod_two_of_bnot_ne_true h_odd
    let m := e / 2
    have h_div : e = 2 * m := (Nat.double_of_div_two_eq_of_even h_even).symm
    have hm : m < e := Nat.div_lt_self (Nat.pos_of_ne_zero h_ne0) (by omega)
    have hm1 : m ≥ 1 := by omega
    have ih := IH m hm hm1
    -- e = 2 * m
    have h_eq : (2 * m : ℚ) ≠ 0 := by positivity
    have h_m_pos : (m : ℚ) > 0 := by positivity
    have h_pow : (4 : ℚ) ^ m = (2 : ℚ) ^ (2 * m) := by
      have : (4 : ℚ) = 2^2 := by norm_num
      rw [this, ← pow_mul]
    have h_pow2 : (4 : ℚ) ^ m / (4 * m) = (2 : ℚ) ^ (2 * m - 2) / m := by
      have : (4 * m : ℚ) = 4 * (m : ℚ) := by push_cast; rfl
      rw [this]
      have : (4 : ℚ) ^ m = 4 * (4 : ℚ) ^ (m - 1) := by
        have : m = (m - 1) + 1 := by omega
        nth_rewrite 1 [this]
        rw [pow_add, pow_one]
        ring
      rw [this]
      have : (4 : ℚ) ≠ 0 := by norm_num
      field_simp
      have : (4 : ℚ) ^ (m - 1) = (2 : ℚ) ^ (2 * m - 2) := by
        have : (4 : ℚ) = 2^2 := by norm_num
        rw [this, ← pow_mul]
        congr 1
        omega
      rw [this]
    simp only [h_cond1, not_false_iff, dif_neg, h_cond2]
    rw [h_div]
    have h_div_m : (2 * m) / 2 = m := by omega
    have h_div_m_q : ((2 * m : ℚ) / 2) = m := by push_cast; omega
    rw [h_div_m]
    have h_sub : (4 : ℚ) ^ m * (c_seq m - 1 / (4 * m)) = (4 : ℚ) ^ m * c_seq m - (4 : ℚ) ^ m / (4 * m) := by ring
    rw [h_sub]
    have h_pos_4m : (4 : ℚ) ^ m ≥ 0 := by positivity
    have h_le1 : (4 : ℚ) ^ m * c_seq m - (4 : ℚ) ^ m / (4 * m) ≥ (4 : ℚ) ^ m * ((2 : ℚ) ^ (m - 1) / m) - (4 : ℚ) ^ m / (4 * m) := by
      linarith [mul_le_mul_of_nonneg_left ih h_pos_4m]
    apply ge_trans h_le1
    -- Now we prove:
    -- (4 : ℚ) ^ m * ((2 : ℚ) ^ (m - 1) / m) - (4 : ℚ) ^ m / (4 * m) ≥ (2 : ℚ) ^ (2 * m - 1) / (2 * m)
    have h_pow4 : (4 : ℚ) = 2^2 := by norm_num
    have h_pow : (4 : ℚ) ^ m = (2 : ℚ) ^ (2 * m) := by
      rw [h_pow4, ← pow_mul]
    have h_pow_sub : (4 : ℚ) ^ m = 4 * (2 : ℚ) ^ (2 * m - 2) := by
      rw [h_pow]
      have : 2 * m = (2 * m - 2) + 2 := by omega
      nth_rewrite 1 [this]
      rw [pow_add]
      ring
    have h_term2 : (4 : ℚ) ^ m / (4 * m) = (2 : ℚ) ^ (2 * m - 2) / m := by
      rw [h_pow_sub]
      have : (4 * m : ℚ) = 4 * (m : ℚ) := by push_cast; rfl
      rw [this]
      have : (4 : ℚ) ≠ 0 := by norm_num
      have : (m : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    have h_term1 : (4 : ℚ) ^ m * ((2 : ℚ) ^ (m - 1) / m) = (2 : ℚ) ^ (3 * m - 1) / m := by
      rw [h_pow]
      have : (2 : ℚ) ^ (2 * m) * ((2 : ℚ) ^ (m - 1) / m) = ((2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ (m - 1)) / m := by ring
      rw [this, ← pow_add]
      congr 3
      omega
    have h_term3 : (2 : ℚ) ^ (2 * m - 1) / (2 * m) = (2 : ℚ) ^ (2 * m - 2) / m := by
      have : (2 * m : ℚ) = 2 * (m : ℚ) := by push_cast; rfl
      rw [this]
      have : (2 : ℚ) ^ (2 * m - 1) = 2 * (2 : ℚ) ^ (2 * m - 2) := by
        have : 2 * m - 1 = (2 * m - 2) + 1 := by omega
        nth_rewrite 1 [this]
        rw [pow_add]
        ring
      rw [this]
      have : (2 : ℚ) ≠ 0 := by norm_num
      have : (m : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    rw [h_term1, h_term2, h_term3]
    -- Goal: (2 : ℚ) ^ (3 * m - 1) / m - (2 : ℚ) ^ (2 * m - 2) / m ≥ (2 : ℚ) ^ (2 * m - 2) / m
    -- which is (2 : ℚ) ^ (3 * m - 1) / m ≥ 2 * (2 : ℚ) ^ (2 * m - 2) / m
    have h_div_pos : (m : ℚ) > 0 := by positivity
    rw [ge_iff_le]
    rw [div_sub_div]
    · rw [le_div_iff h_div_pos]
      have : (2 : ℚ) ^ (2 * m - 2) / m * m = (2 : ℚ) ^ (2 * m - 2) := by
        have : (m : ℚ) ≠ 0 := by positivity
        exact div_mul_cancel₀ ((2 : ℚ) ^ (2 * m - 2)) this
      rw [this]
      have h_sum : (2 : ℚ) ^ (3 * m - 1) * m - (2 : ℚ) ^ (2 * m - 2) * m = ((2 : ℚ) ^ (3 * m - 1) - (2 : ℚ) ^ (2 * m - 2)) * m := by ring
      rw [h_sum]
      rw [mul_le_mul_iff_of_pos_right h_div_pos]
      -- Goal: (2 : ℚ) ^ (2 * m - 2) ≤ (2 : ℚ) ^ (3 * m - 1) - (2 : ℚ) ^ (2 * m - 2)
      -- which is 2 * (2 : ℚ) ^ (2 * m - 2) ≤ (2 : ℚ) ^ (3 * m - 1)
      have : (2 : ℚ) ^ (2 * m - 2) ≤ (2 : ℚ) ^ (3 * m - 1) - (2 : ℚ) ^ (2 * m - 2) ↔ 2 * (2 : ℚ) ^ (2 * m - 2) ≤ (2 : ℚ) ^ (3 * m - 1) := by
        constructor <;> intro h <;> linarith
      rw [this]
      have h_lhs : 2 * (2 : ℚ) ^ (2 * m - 2) = (2 : ℚ) ^ (2 * m - 1) := by
        have : 2 * m - 1 = (2 * m - 2) + 1 := by omega
        nth_rewrite 2 [this]
        rw [pow_add]
        ring
      rw [h_lhs]
      -- Goal: (2 : ℚ) ^ (2 * m - 1) ≤ (2 : ℚ) ^ (3 * m - 1)
      -- which is true since 2 * m - 1 ≤ 3 * m - 1
      have h_mono : 2 * m - 1 ≤ 3 * m - 1 := by omega
      exact pow_le_pow_right₀ (by norm_num) h_mono
    · positivity
    · positivity


noncomputable def a_seq : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun e IH ↦
    if h0 : e = 0 then 1
    else
      let sum_val := Finset.sum (Finset.Ico 1 (e + 1)) fun k ↦
        have h_k : e - k < e := by omega
        (u_seq k) * (IH (e - k) h_k)
      sum_val / e

theorem a_seq_unfold (e : ℕ) : a_seq e =
    if h : e = 0 then 1
    else
      (Finset.sum (Finset.Ico 1 (e + 1)) fun k ↦
        have h_k : e - k < e := by omega
        u_seq k * a_seq (e - k)) / e := by
  rw [a_seq, WellFounded.fix_eq]


theorem u_seq_nonneg (k : ℕ) (hk : k ≥ 1) : u_seq k ≥ 0 := by
  unfold u_seq
  have hc : c_seq k ≥ 0 := by
    have h_pos := c_seq_pos k hk
    have : (2 : ℚ) ^ (k - 1) / k > 0 := by positivity
    linarith
  positivity


theorem a_seq_nonneg (e : ℕ) : a_seq e ≥ 0 := by
  induction' e using Nat.strong_induction_on with e IH
  rw [a_seq_unfold]
  split_ifs with h0
  · linarith
  · apply div_nonneg
    · apply Finset.sum_nonneg
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : k ≥ 1 := hk.1
      have h_u := u_seq_nonneg k hk1
      have h_a := IH (e - k) (by omega)
      positivity
    · positivity

theorem sum_sum_swap (e : ℕ) (f : ℕ → ℕ → ℚ) :
    Finset.sum (Finset.range (e + 1)) (fun j ↦ Finset.sum (Finset.range (j + 1)) (fun k ↦ f j k)) =
    Finset.sum (Finset.range (e + 1)) (fun k ↦ Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ f j k)) := by
  induction' e with e IH
  · simp
  · -- IH says the identity holds for e.
    -- We want to prove it for e + 1.
    rw [Finset.sum_range_succ (fun j ↦ Finset.sum (Finset.range (j + 1)) (fun k ↦ f j k))]
    rw [IH]
    -- RHS for e + 1 is:
    -- Finset.sum (Finset.range (e + 2)) (fun k ↦ Finset.sum (Finset.Ico k (e + 2)) (fun j ↦ f j k))
    rw [Finset.sum_range_succ (fun k ↦ Finset.sum (Finset.Ico k (e + 2)) (fun j ↦ f j k))]
    -- Let's rewrite the sum over range (e + 1) of the Ico k (e + 2)
    -- Since k < e + 2, and e + 2 = (e + 1) + 1, Ico k (e + 2) is Ico k (e + 1) ∪ {e + 1}.
    have h_ico : ∀ k ∈ Finset.range (e + 1), Finset.Ico k (e + 2) = Finset.insert (e + 1) (Finset.Ico k (e + 1)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have h_sum_ico : ∀ k ∈ Finset.range (e + 1), Finset.sum (Finset.Ico k (e + 2)) (fun j ↦ f j k) =
        Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ f j k) + f (e + 1) k := by
      intro k hk
      rw [h_ico k hk]
      rw [Finset.sum_insert]
      · ring
      · simp only [Finset.mem_Ico]
        omega
    have h_split : Finset.sum (Finset.range (e + 1)) (fun k ↦ Finset.sum (Finset.Ico k (e + 2)) (fun j ↦ f j k)) =
        Finset.sum (Finset.range (e + 1)) (fun k ↦ Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ f j k)) +
        Finset.sum (Finset.range (e + 1)) (fun k ↦ f (e + 1) k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      exact h_sum_ico
    rw [h_split]
    -- Now for the last term of RHS, which is Finset.sum (Finset.Ico (e + 1) (e + 2)) (fun j ↦ f j (e + 1))
    have h_last : Finset.sum (Finset.Ico (e + 1) (e + 2)) (fun j ↦ f j (e + 1)) = f (e + 1) (e + 1) := by
      have : Finset.Ico (e + 1) (e + 2) = {e + 1} := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      rw [this, Finset.sum_singleton]
    rw [h_last]
    -- Now we just need to group the last terms:
    -- Finset.sum (Finset.range (e + 1)) (fun k ↦ f (e + 1) k) + f (e + 1) (e + 1) = Finset.sum (Finset.range (e + 2)) (fun k ↦ f (e + 1) k)
    have h_group : Finset.sum (Finset.range (e + 1)) (fun k ↦ f (e + 1) k) + f (e + 1) (e + 1) =
        Finset.sum (Finset.range (e + 2)) (fun k ↦ f (e + 1) k) := by
      rw [Finset.sum_range_succ]
    rw [h_group]
    ring


noncomputable def A005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2^k)

theorem A005187_zero : A005187 0 = 0 := by
  unfold A005187
  simp

theorem A005187_unfold (e : ℕ) (he : e > 0) : A005187 e = e + A005187 (e / 2) := by
  unfold A005187
  -- LHS: sum (k in range (e+1)) e / 2^k
  -- = e + sum (k in range e) e / 2^(k+1)
  -- Since e > 0, range (e+1) = range 1 ∪ Ico 1 (e+1).
  -- e / 2^0 = e.
  -- For k ≥ 1, e / 2^k = (e / 2) / 2^(k-1).
  -- We can rewrite the sum:
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one]
  -- Now we have: e + Finset.sum (Finset.range e) (fun i ↦ e / 2^(i + 1))
  -- We want to show: Finset.sum (Finset.range e) (fun i ↦ e / 2^(i + 1)) = Finset.sum (Finset.range (e / 2 + 1)) (fun k ↦ (e / 2) / 2^k)
  -- Since for i ≥ e / 2 + 1, (e / 2) / 2^i = 0, and e / 2^(i+1) = (e / 2) / 2^i = 0.
  -- Wait, is e / 2^(i+1) equal to (e / 2) / 2^i? Yes, by Nat.div_div_eq_div_mul and 2^(i+1) = 2^i * 2.
  -- Let's prove e / 2^(i+1) = (e / 2) / 2^i
  have h_eq : ∀ i, e / 2^(i + 1) = (e / 2) / 2^i := by
    intro i
    rw [pow_succ]
    -- e / (2^i * 2) = (e / 2) / 2^i
    rw [Nat.div_div_eq_div_mul]
    ring
  simp_rw [h_eq]
  -- Now we want to show:
  -- Finset.sum (Finset.range e) (fun i ↦ (e / 2) / 2^i) = Finset.sum (Finset.range (e / 2 + 1)) (fun k ↦ (e / 2) / 2^k)
  -- Since e / 2 < e (since e > 0), so e / 2 + 1 ≤ e.
  -- Thus, range (e / 2 + 1) ⊆ range e.
  -- For any i inside range e \ range (e / 2 + 1), i ≥ e / 2 + 1.
  -- Since 2^i ≥ 2^(e / 2 + 1) > e / 2, (e / 2) / 2^i = 0.
  have h_le : e / 2 + 1 ≤ e := by omega
  rw [← Finset.sum_sdiff (Finset.range_mono h_le)]
  have h_zero : Finset.sum (Finset.range e \ Finset.range (e / 2 + 1)) (fun i ↦ (e / 2) / 2^i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hi
    -- hi.1 is i < e, hi.2 is ¬(i < e / 2 + 1), so i ≥ e / 2 + 1
    have hi_ge : i ≥ e / 2 + 1 := by omega
    have h_pow_gt : 2^i > e / 2 := by
      -- 2^i ≥ 2^(e / 2 + 1)
      have : 2^i ≥ 2^(e / 2 + 1) := Nat.pow_le_pow_right (by omega) hi_ge
      apply lt_of_lt_of_le _ this
      -- e / 2 < 2^(e / 2 + 1)
      -- which is always true for any natural number.
      -- Let's prove n < 2^(n+1)
      have h_ind : ∀ n, n < 2^(n+1) := by
        intro n
        induction' n with n ih
        · simp
        · rw [pow_succ]
          omega
      exact h_ind (e / 2)
    exact Nat.div_eq_of_lt h_pow_gt
  rw [h_zero, add_zero]

theorem sum_ico_odd_even_split_odd (m : ℕ) (f : ℕ → ℚ) :
    Finset.sum (Finset.Ico 1 (2 * m + 2)) f =
    Finset.sum (Finset.range (m + 1)) (fun j ↦ f (2 * j + 1)) +
    Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ f (2 * j)) := by
  induction' m with m ih
  · simp [Finset.sum_range_succ]
  · -- LHS has two more terms: 2 * m + 2 and 2 * m + 3
    have h_ico_step : Finset.Ico 1 (2 * m + 4) = Finset.insert (2 * m + 3) (Finset.insert (2 * m + 2) (Finset.Ico 1 (2 * m + 2))) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [h_ico_step]
    rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [ih]
        -- RHS: sum (range (m + 2)) + sum (Ico 1 (m + 2))
        rw [Finset.sum_range_succ]
        have h_ico_succ : Finset.Ico 1 (m + 2) = Finset.insert (m + 1) (Finset.Ico 1 (m + 1)) := by
          ext x
          simp only [Finset.mem_Ico, Finset.mem_insert]
          omega
        rw [h_ico_succ, Finset.sum_insert]
        · ring
        · simp only [Finset.mem_Ico]
          omega
      · simp only [Finset.mem_Ico]
        omega
    · simp only [Finset.mem_insert, Finset.mem_Ico]
      omega

theorem sum_ico_odd_even_split_even (m : ℕ) (f : ℕ → ℚ) :
    Finset.sum (Finset.Ico 1 (2 * m + 1)) f =
    Finset.sum (Finset.range m) (fun j ↦ f (2 * j + 1)) +
    Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ f (2 * j)) := by
  induction' m with m ih
  · simp
  · -- For m + 1, LHS is sum (Ico 1 (2 * m + 3)) f
    -- LHS = sum (Ico 1 (2 * m + 2)) f + f (2 * m + 2)
    have h_ico_step : Finset.Ico 1 (2 * m + 3) = Finset.insert (2 * m + 2) (Finset.Ico 1 (2 * m + 2)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [h_ico_step, Finset.sum_insert]
    · rw [sum_ico_odd_even_split_odd m f]
      -- We want to show:
      -- sum (range (m + 1)) f(2j+1) + sum (Ico 1 (m + 1)) f(2j) + f (2*m+2) =
      -- sum (range (m + 1)) f(2j+1) + sum (Ico 1 (m + 2)) f(2j)
      have h_ico_succ : Finset.Ico 1 (m + 2) = Finset.insert (m + 1) (Finset.Ico 1 (m + 1)) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [h_ico_succ, Finset.sum_insert]
      · ring
      · simp only [Finset.mem_Ico]
        omega
    · simp only [Finset.mem_Ico]
      omega


theorem sum_range_reflect (g : ℕ → ℚ) (m : ℕ) :
    Finset.sum (Finset.range m) (fun j ↦ g (m - 1 - j)) = Finset.sum (Finset.range m) g := by
  induction' m with m ih
  · simp
  · rw [Finset.sum_range_succ']
    have h_sub : ∀ j ∈ Finset.range m, m - (j + 1) = m - 1 - j := by
      intro j hj
      rw [Finset.mem_range] at hj
      omega
    have h_congr : Finset.sum (Finset.range m) (fun j ↦ g (m - (j + 1))) = Finset.sum (Finset.range m) (fun j ↦ g (m - 1 - j)) := by
      apply Finset.sum_congr rfl
      exact h_sub
    rw [h_congr, ih, Finset.sum_range_succ]
    have : m - 0 = m := by omega
    rw [this]
    ring


theorem A_seq_recurrence (e : ℕ) (he : e ≥ 1) :
    (2 : ℚ) ^ (A005187 e) * e = 2 * Finset.sum (Finset.Ico 1 (e + 1)) (fun k ↦ u_seq k * (2 : ℚ) ^ (A005187 (e - k))) := by
  induction' e using Nat.strong_induction_on with e IH
  by_cases h1 : e = 1
  · rw [h1]
    have : A005187 1 = 1 := by
      rw [A005187_unfold 1 (by decide), A005187_zero]
    rw [this]
    have h_ico : Finset.Ico 1 2 = {1} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [h_ico, Finset.sum_singleton]
    unfold u_seq
    have : c_seq 1 = 1 := by
      rw [c_seq_unfold]
      simp
    rw [this]
    have : A005187 0 = 0 := A005187_zero
    rw [this]
    norm_num
  · have he2 : e ≥ 2 := by omega
    have he_pos : e > 0 := by omega
    let m := e / 2
    have hm : m ≥ 1 := by
      have : e / 2 ≥ 2 / 2 := Nat.div_le_div_right he2
      omega
    by_cases h_odd : e % 2 = 1
    · -- odd case: e = 2 * m + 1
      have h_div : e = 2 * m + 1 := by
        omega
      rw [h_div]
      rw [sum_ico_odd_even_split_odd m]
      -- We want to prove: 2^(A005187 (2*m+1)) * (2*m+1) = 2 * (sum_odd + sum_even)
      -- Let's simplify A005187 (2*m+1)
      have h_unfold : A005187 (2 * m + 1) = 2 * m + 1 + A005187 m := by
        have : 2 * m + 1 > 0 := by omega
        have h_un := A005187_unfold (2 * m + 1) this
        have : (2 * m + 1) / 2 = m := by omega
        rw [this] at h_un
        exact h_un
      -- We need to simplify the odd sum:
      -- sum (range (m + 1)) (fun j ↦ u_seq (2 * j + 1) * 2 ^ A005187 (2 * m + 1 - (2 * j + 1)))
      -- Let's prove a helper for the odd terms inside the sum:
      have h_odd_term : ∀ j ∈ Finset.range (m + 1),
          u_seq (2 * j + 1) * (2 : ℚ) ^ A005187 (2 * m + 1 - (2 * j + 1)) =
          (2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ A005187 (m - j) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [u_seq_odd j]
        have h_sub : 2 * m + 1 - (2 * j + 1) = 2 * (m - j) := by omega
        rw [h_sub]
        have h_even_unfold : A005187 (2 * (m - j)) = 2 * (m - j) + A005187 (m - j) := by
          by_cases h0 : m - j = 0
          · rw [h0, mul_zero, A005187_zero]
          · have : 2 * (m - j) > 0 := by omega
            have h_un := A005187_unfold (2 * (m - j)) this
            have : 2 * (m - j) / 2 = m - j := by omega
            rw [this] at h_un
            exact h_un
        rw [h_even_unfold]
        -- We want to show: (4 : ℚ) ^ j * 2 ^ (2 * (m - j) + A005187 (m - j)) = 2 ^ (2 * m) * 2 ^ A005187 (m - j)
        have h_pow4 : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
          have : (4 : ℚ) = 2^2 := by norm_num
          rw [this, ← pow_mul]
        rw [h_pow4]
        rw [pow_add]
        have : (2 : ℚ) ^ (2 * (m - j)) = (2 : ℚ) ^ (2 * m - 2 * j) := by
          congr 1
          omega
        rw [this]
        have : (2 : ℚ) ^ (2 * j) * ((2 : ℚ) ^ (2 * m - 2 * j) * (2 : ℚ) ^ A005187 (m - j)) =
            ((2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j)) * (2 : ℚ) ^ A005187 (m - j) := by ring
        rw [this, ← pow_add]
        congr 3
        omega
      -- Now we rewrite the odd sum using this helper:
      have h_sum_odd : Finset.sum (Finset.range (m + 1)) (fun j ↦ u_seq (2 * j + 1) * (2 : ℚ) ^ A005187 (2 * m + 1 - (2 * j + 1))) =
          (2 : ℚ) ^ (2 * m) * Finset.sum (Finset.range (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) := by
        rw [← Finset.mul_sum]
        apply Finset.sum_congr rfl
        exact h_odd_term
      rw [h_sum_odd]

      -- Now we simplify the even sum:
      -- sum (Ico 1 (m + 1)) (fun j ↦ u_seq (2 * j) * 2 ^ A005187 (2 * m + 1 - 2 * j))
      have h_even_term : ∀ j ∈ Finset.Ico 1 (m + 1),
          u_seq (2 * j) * (2 : ℚ) ^ A005187 (2 * m + 1 - 2 * j) =
          4 * (2 : ℚ) ^ (2 * m) * (u_seq j * (2 : ℚ) ^ A005187 (m - j)) - (2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ A005187 (m - j) := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hj1 : j ≥ 1 := hj.1
        rw [u_seq_even j hj1]
        have h_sub : 2 * m + 1 - 2 * j = 2 * (m - j) + 1 := by omega
        rw [h_sub]
        have h_odd_unfold : A005187 (2 * (m - j) + 1) = 2 * (m - j) + 1 + A005187 (m - j) := by
          have : 2 * (m - j) + 1 > 0 := by omega
          have h_un := A005187_unfold (2 * (m - j) + 1) this
          have : (2 * (m - j) + 1) / 2 = m - j := by omega
          rw [this] at h_un
          exact h_un
        rw [h_odd_unfold]
        rw [pow_add, pow_add, pow_one]
        have h_pow4 : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
          have : (4 : ℚ) = 2^2 := by norm_num
          rw [this, ← pow_mul]
        have h_pow_div : (2 : ℚ) ^ (2 * (m - j)) = (2 : ℚ) ^ (2 * m - 2 * j) := by
          congr 1
          omega
        -- Let's multiply out:
        -- (2 * 4^j * u_seq j - 1/2 * 4^j) * 2^(2m - 2j) * 2 * 2^A(m-j)
        -- = (2 * 2^(2j) * u_seq j - 1/2 * 2^(2j)) * 2^(2m - 2j) * 2 * 2^A(m-j)
        -- Since 2^(2j) * 2^(2m - 2j) = 2^(2m), this is:
        -- = (2 * u_seq j - 1/2) * 2^(2m) * 2 * 2^A(m-j)
        -- = (4 * u_seq j - 1) * 2^(2m) * 2^A(m-j)
        -- = 4 * 2^(2m) * u_seq j * 2^A(m-j) - 2^(2m) * 2^A(m-j)
        -- This matches the RHS of our term helper exactly!
        -- Let's prove this equality of real / rational expressions:
        have : (2 * (4 : ℚ) ^ j * u_seq j - 1 / 2 * (4 : ℚ) ^ j) * (2 : ℚ) ^ (2 * (m - j) + 1 + A005187 (m - j)) =
            4 * (2 : ℚ) ^ (2 * m) * (u_seq j * (2 : ℚ) ^ A005187 (m - j)) - (2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ A005187 (m - j) := by
          rw [h_pow4]
          rw [h_pow_div]
          ring
        exact this
      have h_sum_even : Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ u_seq (2 * j) * (2 : ℚ) ^ A005187 (2 * m + 1 - 2 * j)) =
          4 * (2 : ℚ) ^ (2 * m) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ u_seq j * (2 : ℚ) ^ A005187 (m - j)) -
          (2 : ℚ) ^ (2 * m) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        exact h_even_term
      rw [h_sum_even]

      -- Now we can apply IH on m!
      -- Note that m < e, and m ≥ 1.
      have hm_lt : m < e := by omega
      have h_ih_m := IH m hm_lt hm
      -- h_ih_m says: 2^(A005187 m) * m = 2 * sum (Ico 1 (m+1)) (fun k ↦ u_seq k * 2^(A005187 (m-k)))
      -- So sum (Ico 1 (m+1)) (...) = 2^(A005187 m) * m / 2
      have h_ih_m_div : Finset.sum (Finset.Ico 1 (m + 1)) (fun k ↦ u_seq k * (2 : ℚ) ^ A005187 (m - k)) = (2 : ℚ) ^ A005187 m * m / 2 := by
        linarith
      rw [h_ih_m_div]

      -- Now we have:
      -- Total sum = sum_odd + sum_even
      -- sum_odd = 2^(2m) * sum (range (m+1)) (2^A(m-j))
      -- Since range (m+1) = {0} ∪ Ico 1 (m+1) (which is Ico 1 (m+1) ∪ {0})
      -- we can split sum_odd:
      have h_split_range : Finset.sum (Finset.range (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) =
          Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) + (2 : ℚ) ^ A005187 m := by
        rw [Finset.sum_range_succ']
        have : m - 0 = m := by omega
        rw [this]
        have h_ico_range : Finset.Ico 0 m = Finset.range m := Finset.Ico_zero_eq_range
        -- Let's do it simply: Finset.sum (range (m+1)) f = f 0 + sum (Ico 1 (m+1)) f
        -- By Finset.sum_range_succ' we have: f 0 + sum (range m) (fun i ↦ f (i+1))
        -- Let's prove it by rewriting range (m+1) as insert 0 (Ico 1 (m+1))
        have h_eq_insert : Finset.range (m + 1) = Finset.insert 0 (Finset.Ico 1 (m + 1)) := by
          ext x
          simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
          omega
        rw [h_eq_insert, Finset.sum_insert]
        · have : m - 0 = m := by omega
          rw [this]
          ring
        · simp only [Finset.mem_Ico]
          omega
      rw [h_split_range]

      -- Now we can simplify the expression:
      -- 2 * (sum_odd + sum_even)
      -- = 2 * (2^(2m) * (sum_Ico + 2^A(m)) + 4 * 2^(2m) * (2^A(m) * m / 2) - 2^(2m) * sum_Ico)
      -- Let's expand this!
      -- 2^(2m) * sum_Ico + 2^(2m) * 2^A(m) + 2 * 2^(2m) * 2^A(m) * m - 2^(2m) * sum_Ico
      -- Notice that 2^(2m) * sum_Ico cancels out!
      -- So the sum inside the parenthesis simplifies to:
      -- 2^(2m) * 2^A(m) + 2 * 2^(2m) * 2^A(m) * m
      -- = 2^(2m) * 2^A(m) * (2 * m + 1)
      -- And multiplying by 2 gives:
      -- 2 * 2^(2m) * 2^A(m) * (2 * m + 1) = 2^(2m+1) * 2^A(m) * (2 * m + 1)
      -- Since h_unfold says: A005187 (2 * m + 1) = 2 * m + 1 + A005187 m,
      -- we have 2^(A005187 (2 * m + 1)) = 2^(2 * m + 1) * 2^(A005187 m).
      -- So the LHS is 2^(2 * m + 1) * 2^(A005187 m) * (2 * m + 1).
      -- They match perfectly!
      -- Let's prove this algebraic step:
      have h_algebra : 2 * ((2 : ℚ) ^ (2 * m) * (Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) + (2 : ℚ) ^ A005187 m) +
          (4 * (2 : ℚ) ^ (2 * m) * ((2 : ℚ) ^ A005187 m * m / 2) - (2 : ℚ) ^ (2 * m) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)))) =
          (2 : ℚ) ^ (2 * m + 1) * (2 : ℚ) ^ A005187 m * (2 * m + 1) := by
        have : (4 * (2 : ℚ) ^ (2 * m) * ((2 : ℚ) ^ A005187 m * m / 2)) = 2 * (2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ A005187 m * m := by ring
        rw [this]
        have h_add_one : 2 * m + 1 = (2 * m + 1 : ℚ) := by push_cast; rfl
        rw [h_add_one]
        have h_power_add : (2 : ℚ) ^ (2 * m + 1) = 2 * (2 : ℚ) ^ (2 * m) := by
          have : 2 * m + 1 = 2 * m + 1 := rfl
          nth_rewrite 1 [this]
          rw [pow_add, pow_one]
          ring
        rw [h_power_add]
        ring
      rw [h_algebra]
      -- Finally, match LHS:
      rw [h_unfold]
      rw [pow_add]
      ring
    · -- even case: e = 2 * m
      have h_div : e = 2 * m := by
        omega
      rw [h_div]
      rw [sum_ico_odd_even_split_even m]
      -- We want to prove: 2^(A005187 (2*m)) * (2*m) = 2 * (sum_odd + sum_even)
      -- Let's simplify A005187 (2*m)
      have h_unfold : A005187 (2 * m) = 2 * m + A005187 m := by
        have : 2 * m > 0 := by omega
        have h_un := A005187_unfold (2 * m) this
        have : (2 * m) / 2 = m := by omega
        rw [this] at h_un
        exact h_un
      -- We need to simplify the odd sum:
      -- sum (range m) (fun j ↦ u_seq (2 * j + 1) * 2 ^ A005187 (2 * m - (2 * j + 1)))
      have h_odd_term : ∀ j ∈ Finset.range m,
          u_seq (2 * j + 1) * (2 : ℚ) ^ A005187 (2 * m - (2 * j + 1)) =
          (2 : ℚ) ^ (2 * m - 1) * (2 : ℚ) ^ A005187 (m - 1 - j) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [u_seq_odd j]
        have h_sub : 2 * m - (2 * j + 1) = 2 * (m - 1 - j) + 1 := by omega
        rw [h_sub]
        have h_odd_unfold : A005187 (2 * (m - 1 - j) + 1) = 2 * (m - 1 - j) + 1 + A005187 (m - 1 - j) := by
          have : 2 * (m - 1 - j) + 1 > 0 := by omega
          have h_un := A005187_unfold (2 * (m - 1 - j) + 1) this
          have : (2 * (m - 1 - j) + 1) / 2 = m - 1 - j := by omega
          rw [this] at h_un
          exact h_un
        rw [h_odd_unfold]
        -- We want to show: 4^j * 2 ^ (2 * (m-1-j) + 1 + A(m-1-j)) = 2^(2m-1) * 2^A(m-1-j)
        have h_pow4 : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
          have : (4 : ℚ) = 2^2 := by norm_num
          rw [this, ← pow_mul]
        rw [h_pow4]
        rw [pow_add, pow_add, pow_one]
        have : (2 : ℚ) ^ (2 * (m - 1 - j)) = (2 : ℚ) ^ (2 * m - 2 * j - 2) := by
          congr 1
          omega
        rw [this]
        have : (2 : ℚ) ^ (2 * j) * ((2 : ℚ) ^ (2 * m - 2 * j - 2) * 2 * (2 : ℚ) ^ A005187 (m - 1 - j)) =
            ((2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j - 2) * 2) * (2 : ℚ) ^ A005187 (m - 1 - j) := by ring
        rw [this, ← pow_add]
        congr 3
        omega
      have h_sum_odd : Finset.sum (Finset.range m) (fun j ↦ u_seq (2 * j + 1) * (2 : ℚ) ^ A005187 (2 * m - (2 * j + 1))) =
          (2 : ℚ) ^ (2 * m - 1) * Finset.sum (Finset.range m) (fun j ↦ (2 : ℚ) ^ A005187 (m - 1 - j)) := by
        rw [← Finset.mul_sum]
        apply Finset.sum_congr rfl
        exact h_odd_term
      rw [h_sum_odd]

      -- Now we simplify the even sum:
      -- sum (Ico 1 (m + 1)) (fun j ↦ u_seq (2 * j) * 2 ^ A005187 (2 * m - 2 * j))
      have h_even_term : ∀ j ∈ Finset.Ico 1 (m + 1),
          u_seq (2 * j) * (2 : ℚ) ^ A005187 (2 * m - 2 * j) =
          4 * (2 : ℚ) ^ (2 * m - 1) * (u_seq j * (2 : ℚ) ^ A005187 (m - j)) - (2 : ℚ) ^ (2 * m - 1) * (2 : ℚ) ^ A005187 (m - j) := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hj1 : j ≥ 1 := hj.1
        rw [u_seq_even j hj1]
        have h_sub : 2 * m - 2 * j = 2 * (m - j) := by omega
        rw [h_sub]
        have h_even_unfold : A005187 (2 * (m - j)) = 2 * (m - j) + A005187 (m - j) := by
          by_cases h0 : m - j = 0
          · rw [h0, mul_zero, A005187_zero]
          · have : 2 * (m - j) > 0 := by omega
            have h_un := A005187_unfold (2 * (m - j)) this
            have : (2 * (m - j)) / 2 = m - j := by omega
            rw [this] at h_un
            exact h_un
        rw [h_even_unfold]
        rw [pow_add]
        have h_pow4 : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
          have : (4 : ℚ) = 2^2 := by norm_num
          rw [this, ← pow_mul]
        have h_pow_div : (2 : ℚ) ^ (2 * (m - j)) = (2 : ℚ) ^ (2 * m - 2 * j) := by
          congr 1
          omega
        have : (2 * (4 : ℚ) ^ j * u_seq j - 1 / 2 * (4 : ℚ) ^ j) * (2 : ℚ) ^ (2 * (m - j) + A005187 (m - j)) =
            4 * (2 : ℚ) ^ (2 * m - 1) * (u_seq j * (2 : ℚ) ^ A005187 (m - j)) - (2 : ℚ) ^ (2 * m - 1) * (2 : ℚ) ^ A005187 (m - j) := by
          rw [h_pow4]
          rw [h_pow_div]
          ring
        exact this
      have h_sum_even : Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ u_seq (2 * j) * (2 : ℚ) ^ A005187 (2 * m - 2 * j)) =
          4 * (2 : ℚ) ^ (2 * m - 1) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ u_seq j * (2 : ℚ) ^ A005187 (m - j)) -
          (2 : ℚ) ^ (2 * m - 1) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        exact h_even_term
      rw [h_sum_even]

      -- Apply IH on m
      have hm_lt : m < e := by omega
      have h_ih_m := IH m hm_lt hm
      have h_ih_m_div : Finset.sum (Finset.Ico 1 (m + 1)) (fun k ↦ u_seq k * (2 : ℚ) ^ A005187 (m - k)) = (2 : ℚ) ^ A005187 m * m / 2 := by
        linarith
      rw [h_ih_m_div]

      have h_sum_reindex1 : Finset.sum (Finset.range m) (fun j ↦ (2 : ℚ) ^ A005187 (m - 1 - j)) =
          Finset.sum (Finset.range m) (fun i ↦ (2 : ℚ) ^ A005187 i) := by
        exact sum_range_reflect (fun i ↦ (2 : ℚ) ^ A005187 i) m
      have h_sum_reindex2 : Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) =
          Finset.sum (Finset.range m) (fun i ↦ (2 : ℚ) ^ A005187 i) := by
        have h_bij : ∀ j ∈ Finset.Ico 1 (m + 1), m - j ∈ Finset.range m := by
          intro j hj
          rw [Finset.mem_Ico] at hj
          rw [Finset.mem_range]
          omega
        have h_inj : ∀ j1 ∈ Finset.Ico 1 (m + 1), ∀ j2 ∈ Finset.Ico 1 (m + 1), m - j1 = m - j2 → j1 = j2 := by
          intro j1 hj1 j2 hj2 h_eq
          rw [Finset.mem_Ico] at hj1 hj2
          omega
        have h_surj : ∀ i ∈ Finset.range m, ∃ j ∈ Finset.Ico 1 (m + 1), m - j = i := by
          intro i hi
          rw [Finset.mem_range] at hi
          use m - i
          constructor
          · rw [Finset.mem_Ico]
            omega
          · omega
        have h_map : ∀ j ∈ Finset.Ico 1 (m + 1), (2 : ℚ) ^ A005187 (m - j) = (2 : ℚ) ^ A005187 (m - j) := by
          intro j hj
          rfl
        exact Finset.sum_bij (fun j _ ↦ m - j) h_bij h_map h_inj h_surj
      rw [h_sum_reindex1, h_sum_reindex2]

      have h_algebra : 2 * ((2 : ℚ) ^ (2 * m - 1) * Finset.sum (Finset.range m) (fun i ↦ (2 : ℚ) ^ A005187 i) +
          (4 * (2 : ℚ) ^ (2 * m - 1) * ((2 : ℚ) ^ A005187 m * m / 2) - (2 : ℚ) ^ (2 * m - 1) * Finset.sum (Finset.range m) (fun i ↦ (2 : ℚ) ^ A005187 i))) =
          (2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ A005187 m * (2 * m) := by
        have : (4 * (2 : ℚ) ^ (2 * m - 1) * ((2 : ℚ) ^ A005187 m * m / 2)) = 2 * (2 : ℚ) ^ (2 * m - 1) * (2 : ℚ) ^ A005187 m * m := by ring
        rw [this]
        have h_mul_m : 2 * m = (2 * m : ℚ) := by push_cast; rfl
        rw [h_mul_m]
        have h_pow_add : (2 : ℚ) ^ (2 * m) = 2 * (2 : ℚ) ^ (2 * m - 1) := by
          have : 2 * m = (2 * m - 1) + 1 := by omega
          nth_rewrite 1 [this]
          rw [pow_add, pow_one]
          ring
        rw [h_pow_add]
        ring
      rw [h_algebra]
      rw [h_unfold]
      rw [pow_add]
      ring

def S_seq (e : ℕ) : ℚ := Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j))

theorem S_seq_recurrence (e : ℕ) (he : e ≥ 1) :
    e * S_seq e = 2 * Finset.sum (Finset.Ico 1 (e + 1)) (fun k ↦ u_seq k * S_seq (e - k)) := by
  unfold S_seq
  have h_split : (e : ℚ) * Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j)) =
      2 * Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) := by
    -- We want to prove: e * sum = 2 * sum_j
    -- e * sum = sum (j * a_j * a_{e-j}) + sum ((e-j) * a_j * a_{e-j})
    have h_eq : (e : ℚ) * Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j)) =
        Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j) * (e : ℚ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [h_eq]
    have h_split2 : ∀ j ∈ Finset.range (e + 1), a_seq j * a_seq (e - j) * (e : ℚ) =
        (j : ℚ) * a_seq j * a_seq (e - j) + a_seq j * ((e - j : ℚ) * a_seq (e - j)) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have : (e : ℚ) = (j : ℚ) + (e - j : ℚ) := by
        push_cast
        omega
      rw [this]
      ring
    have h_sum_split : Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j) * (e : ℚ)) =
        Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) +
        Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * ((e - j : ℚ) * a_seq (e - j))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      exact h_split2
    rw [h_sum_split]
    -- Now we show the second sum is equal to the first sum using sum_range_reflect
    have h_reflect : Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * ((e - j : ℚ) * a_seq (e - j))) =
        Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) := by
      have h_ref := sum_range_reflect (fun j ↦ a_seq j * ((e - j : ℚ) * a_seq (e - j))) (e + 1)
      rw [h_ref]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have : e + 1 - 1 - j = e - j := by omega
      rw [this]
      have : (e - (e - j) : ℚ) = (j : ℚ) := by
        push_cast
        omega
      rw [this]
      ring
    rw [h_reflect]
    ring
  rw [h_split]
  -- Goal: 2 * Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) =
  -- 2 * Finset.sum (Finset.Ico 1 (e + 1)) (fun k ↦ u_seq k * S_seq (e - k))
  congr 1
  -- Let's rewrite (j : ℚ) * a_seq j using a_seq_unfold
  have h_j_a : ∀ j, (j : ℚ) * a_seq j = Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k)) := by
    intro j
    by_cases hj0 : j = 0
    · rw [hj0]
      simp
    · rw [a_seq_unfold j]
      simp only [hj0, not_false_iff, split_ifs]
      have : (j : ℚ) ≠ 0 := by positivity
      rw [div_mul_cancel₀ _ this]
  have h_sum_j_a : Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) =
      Finset.sum (Finset.range (e + 1)) (fun j ↦ Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k)) * a_seq (e - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [h_j_a j]
  rw [h_sum_j_a]
  -- Distribute * a_seq (e - j)
  have h_dist : ∀ j, Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k)) * a_seq (e - j) =
      Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k) * a_seq (e - j)) := by
    intro j
    rw [Finset.sum_mul]
  simp_rw [h_dist]
  -- Now we define F j k
  let F (j k : ℕ) : ℚ := if k ≥ 1 then u_seq k * a_seq (j - k) * a_seq (e - j) else 0
  have h_F_sum : ∀ j ∈ Finset.range (e + 1), Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k) * a_seq (e - j)) =
      Finset.sum (Finset.range (j + 1)) (fun k ↦ F j k) := by
    intro j hj
    rw [Finset.sum_range_succ']
    have : F j 0 = 0 := rfl
    rw [this, zero_add]
    have h_ico_range : Finset.Ico 1 (j + 1) = Finset.map ⟨fun x ↦ x + 1, fun x y h ↦ by omega⟩ (Finset.range j) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro hx
        use x - 1
        omega
      · rintro ⟨y, hy, rfl⟩
        omega
    -- Let's do it simply:
    -- Finset.sum (range (j + 1)) (fun k ↦ F j k) = F j 0 + sum (Ico 1 (j + 1)) (fun k ↦ F j k)
    -- since range (j + 1) = insert 0 (Ico 1 (j + 1))
    have h_insert : Finset.range (j + 1) = Finset.insert 0 (Finset.Ico 1 (j + 1)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [h_insert, Finset.sum_insert]
    · have : F j 0 = 0 := rfl
      rw [this, zero_add]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ico] at hk
      have : k ≥ 1 := hk.1
      simp only [this, ge_iff_le, split_ifs]
    · simp only [Finset.mem_Ico]
      omega
  have h_sum_F : Finset.sum (Finset.range (e + 1)) (fun j ↦ Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k) * a_seq (e - j))) =
      Finset.sum (Finset.range (e + 1)) (fun j ↦ Finset.sum (Finset.range (j + 1)) (fun k ↦ F j k)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact h_F_sum j hj
  rw [h_sum_F]
  rw [sum_sum_swap e F]
  -- Goal: sum (range (e + 1)) (fun k ↦ sum (Ico k (e + 1)) (fun j ↦ F j k)) =
  -- sum (Ico 1 (e + 1)) (fun k ↦ u_seq k * S_seq (e - k))
  -- Let's split range (e + 1) into 0 and Ico 1 (e + 1)
  have h_split_range_0 : Finset.sum (Finset.range (e + 1)) (fun k ↦ Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ F j k)) =
      Finset.sum (Finset.Ico 1 (e + 1)) (fun k ↦ Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ F j k)) := by
    have h_insert : Finset.range (e + 1) = Finset.insert 0 (Finset.Ico 1 (e + 1)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [h_insert, Finset.sum_insert]
    · have h_zero : Finset.sum (Finset.Ico 0 (e + 1)) (fun j ↦ F j 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rfl
      rw [h_zero, zero_add]
    · simp only [Finset.mem_Ico]
      omega
  rw [h_split_range_0]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk1 : k ≥ 1 := hk.1
  -- Inner sum: sum (Ico k (e + 1)) (fun j ↦ F j k)
  -- Since k ≥ 1, F j k = u_seq k * a_seq (j - k) * a_seq (e - j)
  have h_inner_eq : Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ F j k) =
      Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ u_seq k * a_seq (j - k) * a_seq (e - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hk1, ge_iff_le, split_ifs]
  rw [h_inner_eq]
  rw [← Finset.mul_sum]
  congr 1
  -- Goal: sum (Ico k (e + 1)) (fun j ↦ a_seq (j - k) * a_seq (e - j)) = S_seq (e - k)
  -- We use Finset.sum_bij with mapping j ↦ j - k.
  have h_bij : ∀ j ∈ Finset.Ico k (e + 1), j - k ∈ Finset.range (e - k + 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_range]
    omega
  have h_map : ∀ j ∈ Finset.Ico k (e + 1), a_seq (j - k) * a_seq (e - j) = a_seq (j - k) * a_seq (e - k - (j - k)) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have : e - j = e - k - (j - k) := by omega
    rw [this]
  have h_inj : ∀ j1 ∈ Finset.Ico k (e + 1), ∀ j2 ∈ Finset.Ico k (e + 1), j1 - k = j2 - k → j1 = j2 := by
    intro j1 hj1 j2 hj2 h_eq
    rw [Finset.mem_Ico] at hj1 hj2
    omega
  have h_surj : ∀ i ∈ Finset.range (e - k + 1), ∃ j ∈ Finset.Ico k (e + 1), j - k = i := by
    intro i hi
    rw [Finset.mem_range] at hi
    use i + k
    constructor
    · rw [Finset.mem_Ico]
      omega
    · omega
  exact Finset.sum_bij (fun j _ ↦ j - k) h_bij h_map h_inj h_surj


theorem S_seq_eq_pow (e : ℕ) : S_seq e = (2 : ℚ) ^ (A005187 e) := by
  induction' e using Nat.strong_induction_on with e IH
  by_cases h0 : e = 0
  · rw [h0]
    unfold S_seq
    simp only [Finset.sum_singleton, Nat.sub_zero]
    rw [a_seq_unfold 0]
    simp [A005187_zero]
  · have he : e ≥ 1 := by omega
    have h_recurrence := S_seq_recurrence e he
    have h_sub : ∀ k ∈ Finset.Ico 1 (e + 1), S_seq (e - k) = (2 : ℚ) ^ (A005187 (e - k)) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have : e - k < e := by omega
      exact IH (e - k) this
    have h_congr : Finset.sum (Finset.Ico 1 (e + 1)) (fun k ↦ u_seq k * S_seq (e - k)) =
        Finset.sum (Finset.Ico 1 (e + 1)) (fun k ↦ u_seq k * (2 : ℚ) ^ (A005187 (e - k))) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [h_sub k hk]
    rw [h_congr] at h_recurrence
    have h_recurrence2 := A_seq_recurrence e he
    rw [← h_recurrence2] at h_recurrence
    have he_q : (e : ℚ) ≠ 0 := by positivity
    -- e * S_seq e = 2^(A e) * e
    have : (e : ℚ) * S_seq e = S_seq e * e := by ring
    rw [this] at h_recurrence
    exact mul_right_cancel₀ he_q h_recurrence

noncomputable def a_f (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ a_seq e

theorem a_f_mul_of_coprime (x y : ℕ) (h : Coprime x y) : a_f (x * y) = a_f x * a_f y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul]
    unfold a_f
    simp
  · by_cases hy : y = 0
    · rw [hy, mul_zero]
      unfold a_f
      simp
    · have h_xy : x * y ≠ 0 := MulZeroClass.mul_ne_zero hx hy
      unfold a_f
      simp only [hx, hy, h_xy, ↓reduceIte]
      rw [factorization_mul_of_coprime h]
      rw [Finsupp.prod_add_index_of_disjoint]
      exact h.disjoint_primeFactors

noncomputable def a_f_arith : ArithmeticFunction ℚ :=
  ⟨a_f, by unfold a_f; simp⟩

theorem a_f_arith_mult : a_f_arith.IsMultiplicative := by
  constructor
  · unfold a_f_arith
    simp only [coe_mk]
    unfold a_f
    simp
  · intro m n h
    unfold a_f_arith
    simp only [coe_mk]
    exact a_f_mul_of_coprime m n h

noncomputable def A046644_arith : ArithmeticFunction ℚ :=
  ⟨A046644, by unfold A046644; simp⟩

theorem A046644_mul_of_coprime (x y : ℕ) (h : Coprime x y) : A046644 (x * y) = A046644 x * A046644 y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul]
    unfold A046644
    simp
  · by_cases hy : y = 0
    · rw [hy, mul_zero]
      unfold A046644
      simp
    · have h_xy : x * y ≠ 0 := MulZeroClass.mul_ne_zero hx hy
      unfold A046644
      simp only [hx, hy, h_xy, ↓reduceIte]
      rw [factorization_mul_of_coprime h]
      rw [Finsupp.prod_add_index_of_disjoint]
      exact h.disjoint_primeFactors

theorem A046644_arith_mult : A046644_arith.IsMultiplicative := by
  constructor
  · unfold A046644_arith
    simp only [coe_mk]
    unfold A046644
    simp
  · intro m n h
    unfold A046644_arith
    simp only [coe_mk]
    exact A046644_mul_of_coprime m n h


theorem a_f_prime_pow (p : ℕ) (hp : p.Prime) (j : ℕ) : a_f (p ^ j) = a_seq j := by
  by_cases hj : j = 0
  · rw [hj, pow_zero]
    unfold a_f
    simp only [one_ne_zero, ↓reduceIte, factorization_one, Finsupp.prod_zero_index]
    rw [a_seq_unfold 0]
    simp
  · unfold a_f
    have h_pow_ne : p ^ j ≠ 0 := by positivity
    simp only [h_pow_ne, ↓reduceIte]
    rw [Prime.factorization_pow hp]
    rw [Finsupp.prod_single_index]
    simp

theorem A046644_prime_pow (p : ℕ) (hp : p.Prime) (j : ℕ) : A046644 (p ^ j) = (2 : ℚ) ^ (A005187 j) := by
  by_cases hj : j = 0
  · rw [hj, pow_zero]
    unfold A046644
    simp only [one_ne_zero, ↓reduceIte, factorization_one, Finsupp.prod_zero_index]
    rw [A005187_zero]
    simp
  · unfold A046644
    have h_pow_ne : p ^ j ≠ 0 := by positivity
    simp only [h_pow_ne, ↓reduceIte]
    rw [Prime.factorization_pow hp]
    rw [Finsupp.prod_single_index]
    simp


theorem a_f_arith_conv_eq : a_f_arith * a_f_arith = A046644_arith := by
  have h1 : (a_f_arith * a_f_arith).IsMultiplicative := a_f_arith_mult.mul a_f_arith_mult
  have h2 : A046644_arith.IsMultiplicative := A046644_arith_mult
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (a_f_arith * a_f_arith) h1 A046644_arith h2]
  intro p i hp
  rw [ArithmeticFunction.mul_apply]
  have h_eq_af : ∀ x : ℕ × ℕ, a_f_arith x.1 * a_f_arith x.2 = a_f x.1 * a_f x.2 := by
    intro x
    rfl
  simp_rw [h_eq_af]
  rw [sum_divisorsAntidiagonal (fun i1 i2 ↦ a_f i1 * a_f i2)]
  rw [sum_divisors_prime_pow hp]
  have h_term : ∀ j ∈ Finset.range (i + 1), a_f (p ^ j) * a_f (p ^ i / p ^ j) = a_seq j * a_seq (i - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [a_f_prime_pow p hp j]
    have : p ^ i / p ^ j = p ^ (i - j) := by
      rw [Nat.pow_div (by omega) (by omega)]
    rw [this, a_f_prime_pow p hp (i - j)]
  rw [Finset.sum_congr rfl h_term]
  have : Finset.sum (Finset.range (i + 1)) (fun j ↦ a_seq j * a_seq (i - j)) = S_seq i := rfl
  rw [this]
  rw [S_seq_eq_pow i]
  unfold A046644_arith
  simp only [ArithmeticFunction.coe_mk]
  rw [A046644_prime_pow p hp i]


theorem A317940_f_eq_a_f (n : ℕ) : A317940_f n = a_f n := by
  induction' n using Nat.strong_induction_on with n IH
  rw [A317940_f_unfold]
  by_cases h0 : n = 0
  · rw [h0]
    unfold a_f
    simp
  · by_cases h1 : n = 1
    · rw [h1]
      unfold a_f
      simp
    · have hn2 : n > 1 := by omega
      simp only [h0, h1, ↓reduceIte]
      -- We want to prove: (A046644 n - sum_of_products) / 2 = a_f n
      -- Let's first replace IH d and IH (n/d) in the sum_of_products
      have h_sum_congr : (Finset.sum (divisors n) fun d ↦
          if h_prop : d > 1 ∧ d < n then
            A317940_f d * A317940_f (n / d)
          else 0) =
          Finset.sum (divisors n) fun d ↦
          if h_prop : d > 1 ∧ d < n then
            a_f d * a_f (n / d)
          else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs with h_prop
        · have hd_lt : d < n := h_prop.2
          have hq_lt : n / d < n := Nat.div_lt_self (by omega) h_prop.1
          rw [IH d hd_lt, IH (n / d) hq_lt]
        · rfl
      rw [h_sum_congr]
      -- Now we relate the sum to a_f
      have h_cases : ∀ d ∈ divisors n, d = 1 ∨ d = n ∨ (d > 1 ∧ d < n) := by
        intro d hd
        rw [mem_divisors] at hd
        omega
      have h_term_eq : ∀ d ∈ divisors n, a_f d * a_f (n / d) =
          (if d > 1 ∧ d < n then a_f d * a_f (n / d) else 0) +
          (if d = 1 then a_f n else 0) +
          (if d = n then a_f n else 0) := by
        intro d hd
        have hd_cases := h_cases d hd
        split_ifs <;> try ring
        · omega
        · omega
        · omega
        · have : n / n = 1 := Nat.div_self (by omega)
          rw [this]
          unfold a_f
          simp
        · have : n / 1 = n := Nat.div_one n
          rw [this]
          unfold a_f
          simp
        · omega
      have h_sum_all : Finset.sum (divisors n) (fun d ↦ a_f d * a_f (n / d)) =
          Finset.sum (divisors n) (fun d ↦ if d > 1 ∧ d < n then a_f d * a_f (n / d) else 0) +
          Finset.sum (divisors n) (fun d ↦ if d = 1 then a_f n else 0) +
          Finset.sum (divisors n) (fun d ↦ if d = n then a_f n else 0) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        exact h_term_eq
      have h_sum_1 : Finset.sum (divisors n) (fun d ↦ if d = 1 then a_f n else 0) = a_f n := by
        have : 1 ∈ divisors n := by
          rw [mem_divisors]
          omega
        exact Finset.sum_eq_single 1 (by simp) (fun b hb hb1 ↦ by simp [hb1])
      have h_sum_n : Finset.sum (divisors n) (fun d ↦ if d = n then a_f n else 0) = a_f n := by
        have : n ∈ divisors n := by
          rw [mem_divisors]
          omega
        exact Finset.sum_eq_single n (by simp) (fun b hb hbn ↦ by simp [hbn])
      rw [h_sum_1, h_sum_n] at h_sum_all
      -- Now we have:
      -- sum (a_f d * a_f (n/d)) = sum_of_products + a_f n + a_f n
      -- Let's relate sum (a_f d * a_f (n/d)) to A046644 n
      have h_conv_eq : (a_f_arith * a_f_arith) n = A046644 n := by
        rw [a_f_arith_conv_eq]
        rfl
      have h_conv_apply : (a_f_arith * a_f_arith) n = Finset.sum (divisors n) (fun d ↦ a_f d * a_f (n / d)) := by
        rw [ArithmeticFunction.mul_apply]
        rw [sum_divisorsAntidiagonal (fun i1 i2 ↦ a_f i1 * a_f i2)]
        rfl
      rw [h_conv_apply] at h_conv_eq
      rw [h_conv_eq] at h_sum_all
      -- Now: A046644 n = sum_of_products + a_f n + a_f n
      -- So sum_of_products = A046644 n - 2 * a_f n
      have : Finset.sum (divisors n) (fun d ↦ if d > 1 ∧ d < n then a_f d * a_f (n / d) else 0) = A046644 n - 2 * a_f n := by
        linarith
      rw [this]
      ring

theorem A317940_f_non_neg (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 := by
  rw [A317940_f_eq_a_f]
  unfold a_f
  have h_ne : n ≠ 0 := by omega
  simp only [h_ne, ↓reduceIte]
  apply Finset.prod_nonneg
  intro i hi
  exact a_seq_nonneg (n.factorization i)










