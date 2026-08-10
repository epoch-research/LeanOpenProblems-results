import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A005187: Sum of $\lfloor n / 2^k \rfloor$ for $k \ge 0$.
This is $\sum_{k=0}^\infty \lfloor n / 2^k \rfloor$.
-/
noncomputable def A005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2^k)

/--
A046644: Multiplicative function defined on prime powers $p^e$ as $2^{\text{A005187}(e)}$.
-/
noncomputable def A046644 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ (2 : ℚ) ^ (A005187 e)

/--
The sequence $f(n) \in \mathbb{Q}$ such that $f * f = \text{A046644}$.
Defined by well-founded recursion on $\mathbb{N}$ w.r.t. $<$.
-/
noncomputable def A317940_f : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if n = 0 then 0
    else if n = 1 then 1
    else
      let A_n : ℚ := A046644 n

      let sum_of_products : ℚ := Finset.sum (divisors n) fun d ↦
        if h_prop : d > 1 ∧ d < n then
          -- Proofs that recursive arguments are smaller than n:
          have d_lt_n : d < n := h_prop.2
          let q := n / d
          have q_lt_n : q < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h_prop.1

          IH d d_lt_n * IH q q_lt_n
        else 0
      (A_n - sum_of_products) / 2

/--
A317940: Numerators of sequence whose Dirichlet convolution with itself yields A046644.
$a(n) = \text{numerator}(f(n))$, where $f*f = \text{A046644}$.
-/
noncomputable def A317940 (n : ℕ) : ℕ :=
  (A317940_f n).num.natAbs

theorem A317940_f_unfold (n : ℕ) : A317940_f n = if n = 0 then 0 else if n = 1 then 1 else
      let A_n : ℚ := A046644 n
      let sum_of_products : ℚ := Finset.sum (divisors n) fun d ↦
        if h_prop : d > 1 ∧ d < n then
          have d_lt_n : d < n := h_prop.2
          let q := n / d
          have q_lt_n : q < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h_prop.1
          A317940_f d * A317940_f q
        else 0
      (A_n - sum_of_products) / 2 := by
  rw [A317940_f, WellFounded.fix_eq]

theorem A046644_nonneg (n : ℕ) : A046644 n ≥ 0 := by
  unfold A046644
  split_ifs with h
  · linarith
  · apply Finset.prod_nonneg
    intro i hi
    positivity

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
  simp [h_ne0, h_odd]
  have : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
    have : (4 : ℚ) = 2 ^ 2 := by norm_num
    rw [this, ← pow_mul]
  rw [this]
  have : (2 * j + 1 : ℚ) ≠ 0 := by positivity
  field_simp

theorem u_seq_even (j : ℕ) (hj : j ≥ 1) : u_seq (2 * j) = 2 * (4 : ℚ) ^ j * u_seq j - (1 / 2) * (4 : ℚ) ^ j := by
  unfold u_seq
  rw [c_seq_unfold]
  have h_even : (2 * j) % 2 = 0 := by omega
  have h_ne0 : 2 * j ≠ 0 := by omega
  have h_not_odd : ¬ (2 * j) % 2 = 1 := by omega
  simp [h_ne0, h_not_odd]
  have : (2 * j : ℚ) = 2 * (j : ℚ) := by push_cast; rfl
  rw [this]
  have : (j : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem c_seq_pos (e : ℕ) (he : e ≥ 1) : c_seq e ≥ (2 : ℚ)^(e - 1) / e := by
  induction' e using Nat.strong_induction_on with e IH
  rw [c_seq_unfold]
  have h_ne0 : e ≠ 0 := by omega
  simp only [h_ne0, not_false_iff, dif_neg]
  split_ifs with h_odd
  · rfl
  · have h_even : e % 2 = 0 := by omega
    let m := e / 2
    have h_div : e = 2 * m := by omega
    have hm : m < e := Nat.div_lt_self (Nat.pos_of_ne_zero h_ne0) (by omega)
    have hm1 : m ≥ 1 := by omega
    have ih := IH m hm hm1
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
    simp only [h_div]
    have h_div_m : (2 * m) / 2 = m := by omega
    have h_div_m_q : ((2 * m : ℚ) / 2) = m := by ring
    simp only [h_div_m]
    have h_sub : (4 : ℚ) ^ m * (c_seq m - 1 / (4 * m)) = (4 : ℚ) ^ m * c_seq m - (4 : ℚ) ^ m / (4 * m) := by ring
    rw [h_sub]
    have h_pos_4m : (4 : ℚ) ^ m ≥ 0 := by positivity
    have h_le1 : (4 : ℚ) ^ m * c_seq m - (4 : ℚ) ^ m / (4 * m) ≥ (4 : ℚ) ^ m * ((2 : ℚ) ^ (m - 1) / m) - (4 : ℚ) ^ m / (4 * m) := by
      linarith [mul_le_mul_of_nonneg_left ih h_pos_4m]
    apply ge_trans h_le1
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
    have h_term1 : (4 : ℚ) ^ m * ((2 : ℚ) ^ (m - 1) / m) = (2 : ℚ) ^ (3 * m - 1) / m := by
      rw [h_pow]
      have : (2 : ℚ) ^ (2 * m) * ((2 : ℚ) ^ (m - 1) / m) = ((2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ (m - 1)) / m := by ring
      rw [this, ← pow_add]
      congr 3
      omega
    have h_term3 : (2 : ℚ) ^ (2 * m - 1) / ↑(2 * m) = (2 : ℚ) ^ (2 * m - 2) / ↑m := by
      have : ↑(2 * m) = 2 * (m : ℚ) := by push_cast; rfl
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
    simp only [h_term1, h_term2, h_term3]
    have h_div_pos : (m : ℚ) > 0 := by positivity
    have h_add_goal : (2 : ℚ) ^ (2 * m - 2) / m ≤ (2 : ℚ) ^ (3 * m - 1) / m - (2 : ℚ) ^ (2 * m - 2) / m ↔
        (2 : ℚ) ^ (2 * m - 2) / m + (2 : ℚ) ^ (2 * m - 2) / m ≤ (2 : ℚ) ^ (3 * m - 1) / m := by
      constructor <;> intro h <;> linarith
    rw [h_add_goal]
    have h_double : (2 : ℚ) ^ (2 * m - 2) / m + (2 : ℚ) ^ (2 * m - 2) / m = 2 * (2 : ℚ) ^ (2 * m - 2) / m := by ring
    rw [h_double]
    have h_lhs2 : 2 * (2 : ℚ) ^ (2 * m - 2) / m = (2 : ℚ) ^ (2 * m - 1) / m := by
      have : 2 * (2 : ℚ) ^ (2 * m - 2) = (2 : ℚ) ^ (2 * m - 1) := by
        have : 2 * m - 1 = (2 * m - 2) + 1 := by omega
        rw [this]
        rw [pow_add]
        ring
      rw [this]
    rw [h_lhs2]
    have h_mono : 2 * m - 1 ≤ 3 * m - 1 := by omega
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h_mono) (by positivity)

theorem u_seq_nonneg (k : ℕ) (hk : k ≥ 1) : u_seq k ≥ 0 := by
  unfold u_seq
  have hc : c_seq k ≥ 0 := by
    have h_pos := c_seq_pos k hk
    have h_num : (2 : ℚ) ^ (k - 1) > 0 := by positivity
    have h_den : (k : ℚ) > 0 := by
      have : k > 0 := by omega
      positivity
    have : (2 : ℚ) ^ (k - 1) / k > 0 := div_pos h_num h_den
    linarith
  positivity

noncomputable def a_seq : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun e IH ↦
    if h0 : e = 0 then 1
    else
      (Finset.sum (Finset.Ico 1 (e + 1)) fun k ↦
        if h_prop : k ≥ 1 ∧ k < e + 1 then
          have h_k : e - k < e := by omega
          (u_seq k) * (IH (e - k) h_k)
        else 0) / e

theorem a_seq_unfold (e : ℕ) : a_seq e =
    if h : e = 0 then 1
    else
      (Finset.sum (Finset.Ico 1 (e + 1)) fun k ↦
        u_seq k * a_seq (e - k)) / e := by
  rw [a_seq, WellFounded.fix_eq]
  split_ifs with h0
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h_prop : k ≥ 1 ∧ k < e + 1 := by omega
    simp [h_prop]

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
  · rw [Finset.sum_range_succ (fun j ↦ Finset.sum (Finset.range (j + 1)) (fun k ↦ f j k))]
    rw [IH]
    rw [Finset.sum_range_succ (fun k ↦ Finset.sum (Finset.Ico k (e + 2)) (fun j ↦ f j k))]
    have h_ico : ∀ k ∈ Finset.range (e + 1), Finset.Ico k (e + 2) = insert (e + 1) (Finset.Ico k (e + 1)) := by
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
    have h_last : Finset.sum (Finset.Ico (e + 1) (e + 2)) (fun j ↦ f j (e + 1)) = f (e + 1) (e + 1) := by
      have : Finset.Ico (e + 1) (e + 2) = {e + 1} := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_singleton]
        omega
      rw [this, Finset.sum_singleton]
    rw [h_last]
    have h_group : Finset.sum (Finset.range (e + 1)) (fun k ↦ f (e + 1) k) + f (e + 1) (e + 1) =
        Finset.sum (Finset.range (e + 2)) (fun k ↦ f (e + 1) k) := by
      exact (Finset.sum_range_succ (fun k ↦ f (e + 1) k) (e + 1)).symm
    have h_eq_add : e + (1 + 1) = e + 2 := rfl
    rw [h_eq_add, ← h_group, add_assoc]

theorem A005187_zero : A005187 0 = 0 := by
  unfold A005187
  simp

theorem A005187_unfold (e : ℕ) (he : e > 0) : A005187 e = e + A005187 (e / 2) := by
  unfold A005187
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one]
  have h_eq : ∀ i, e / 2^(i + 1) = (e / 2) / 2^i := by
    intro i
    rw [pow_succ]
    rw [Nat.div_div_eq_div_mul]
    ring
  simp_rw [h_eq]
  have h_le : e / 2 + 1 ≤ e := by omega
  rw [← Finset.sum_sdiff (Finset.range_mono h_le)]
  have h_zero : Finset.sum (Finset.range e \ Finset.range (e / 2 + 1)) (fun i ↦ (e / 2) / 2^i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hi
    have hi_ge : i ≥ e / 2 + 1 := by omega
    have h_pow_gt : 2^i > e / 2 := by
      have : 2^i ≥ 2^(e / 2 + 1) := Nat.pow_le_pow_right (by omega) hi_ge
      apply lt_of_lt_of_le _ this
      have h_ind : ∀ n, n < 2^(n+1) := by
        intro n
        induction' n with n ih
        · simp
        · rw [pow_succ]
          omega
      exact h_ind (e / 2)
    exact Nat.div_eq_of_lt h_pow_gt
  rw [h_zero, zero_add, add_comm]

theorem sum_ico_odd_even_split_odd (m : ℕ) (f : ℕ → ℚ) :
    Finset.sum (Finset.Ico 1 (2 * m + 2)) f =
    Finset.sum (Finset.range (m + 1)) (fun j ↦ f (2 * j + 1)) +
    Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ f (2 * j)) := by
  induction' m with m ih
  · simp [Finset.sum_range_succ]
  · have h_ico_step : Finset.Ico 1 (2 * (m + 1) + 2) = insert (2 * m + 3) (insert (2 * m + 2) (Finset.Ico 1 (2 * m + 2))) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [h_ico_step]
    rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [ih]
        rw [Finset.sum_range_succ (fun j ↦ f (2 * j + 1)) (m + 1)]
        have h_ico_succ : Finset.Ico 1 (m + 2) = insert (m + 1) (Finset.Ico 1 (m + 1)) := by
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
  · have h_ico_step : Finset.Ico 1 (2 * (m + 1) + 1) = insert (2 * m + 2) (Finset.Ico 1 (2 * m + 2)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [h_ico_step, Finset.sum_insert]
    · rw [sum_ico_odd_even_split_odd m f]
      have h_ico_succ : Finset.Ico 1 (m + 2) = insert (m + 1) (Finset.Ico 1 (m + 1)) := by
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
    have h_simp : ∀ j ∈ Finset.range m, g (m + 1 - 1 - (j + 1)) = g (m - (j + 1)) := by
      intro j hj
      congr 1
    have h_congr : Finset.sum (Finset.range m) (fun j ↦ g (m + 1 - 1 - (j + 1))) = Finset.sum (Finset.range m) (fun j ↦ g (m - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [h_simp j hj, h_sub j hj]
    rw [h_congr, ih, Finset.sum_range_succ]
    have : m + 1 - 1 - 0 = m := by omega
    rw [this]

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
    · have h_div : e = 2 * m + 1 := by omega
      rw [h_div]
      rw [sum_ico_odd_even_split_odd m]
      have h_unfold : A005187 (2 * m + 1) = 2 * m + 1 + A005187 m := by
        have : 2 * m + 1 > 0 := by omega
        have h_un := A005187_unfold (2 * m + 1) this
        have : (2 * m + 1) / 2 = m := by omega
        rw [this] at h_un
        exact h_un
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
        have h_pow4 : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
          have : (4 : ℚ) = 2^2 := by norm_num
          rw [this, ← pow_mul]
        rw [h_pow4]
        rw [pow_add]
        have : (2 : ℚ) ^ (2 * (m - j)) = (2 : ℚ) ^ (2 * m - 2 * j) := by congr 1; omega
        rw [this]
        have : (2 : ℚ) ^ (2 * j) * ((2 : ℚ) ^ (2 * m - 2 * j) * (2 : ℚ) ^ A005187 (m - j)) =
            ((2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j)) * (2 : ℚ) ^ A005187 (m - j) := by ring
        rw [this, ← pow_add]
        congr 3
        omega
      have h_sum_odd : Finset.sum (Finset.range (m + 1)) (fun j ↦ u_seq (2 * j + 1) * (2 : ℚ) ^ A005187 (2 * m + 1 - (2 * j + 1))) =
          (2 : ℚ) ^ (2 * m) * Finset.sum (Finset.range (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [h_odd_term j hj]
      rw [h_sum_odd]
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
        have h_pow_div : (2 : ℚ) ^ (2 * (m - j)) = (2 : ℚ) ^ (2 * m - 2 * j) := by congr 1; omega
        have : (2 * (4 : ℚ) ^ j * u_seq j - 1 / 2 * (4 : ℚ) ^ j) * ((2 : ℚ) ^ (2 * (m - j)) * 2 * (2 : ℚ) ^ A005187 (m - j)) =
            4 * (2 : ℚ) ^ (2 * m) * (u_seq j * (2 : ℚ) ^ A005187 (m - j)) - (2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ A005187 (m - j) := by
          rw [h_pow4, h_pow_div]
          have h_pow_mul : (2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j) = (2 : ℚ) ^ (2 * m) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            (2 * (2 : ℚ) ^ (2 * j) * u_seq j - 1 / 2 * (2 : ℚ) ^ (2 * j)) * ((2 : ℚ) ^ (2 * m - 2 * j) * 2 * (2 : ℚ) ^ A005187 (m - j))
            _ = (2 * ((2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j)) * u_seq j - 1 / 2 * ((2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j))) * (2 * (2 : ℚ) ^ A005187 (m - j)) := by ring
            _ = (2 * (2 : ℚ) ^ (2 * m) * u_seq j - 1 / 2 * (2 : ℚ) ^ (2 * m)) * (2 * (2 : ℚ) ^ A005187 (m - j)) := by rw [h_pow_mul]
            _ = 4 * (2 : ℚ) ^ (2 * m) * (u_seq j * (2 : ℚ) ^ A005187 (m - j)) - (2 : ℚ) ^ (2 * m) * (2 : ℚ) ^ A005187 (m - j) := by ring
        exact this
      have h_sum_even : Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ u_seq (2 * j) * (2 : ℚ) ^ A005187 (2 * m + 1 - 2 * j)) =
          4 * (2 : ℚ) ^ (2 * m) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ u_seq j * (2 : ℚ) ^ A005187 (m - j)) -
          (2 : ℚ) ^ (2 * m) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [h_even_term j hj]
      rw [h_sum_even]
      have hm_lt : m < e := by omega
      have h_ih_m := IH m hm_lt hm
      have h_ih_m_div : Finset.sum (Finset.Ico 1 (m + 1)) (fun k ↦ u_seq k * (2 : ℚ) ^ A005187 (m - k)) = (2 : ℚ) ^ A005187 m * m / 2 := by linarith
      rw [h_ih_m_div]
      have h_split_range : Finset.sum (Finset.range (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) =
          Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) + (2 : ℚ) ^ A005187 m := by
        have h_eq_insert : Finset.range (m + 1) = insert 0 (Finset.Ico 1 (m + 1)) := by
          ext x
          simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
          omega
        rw [h_eq_insert, Finset.sum_insert]
        · have : m - 0 = m := by omega
          rw [this]; ring
        · simp only [Finset.mem_Ico]; omega
      rw [h_split_range]
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
          rw [pow_add, pow_one]; ring
        rw [h_power_add]; push_cast; ring
      rw [h_algebra]
      rw [h_unfold, pow_add]; push_cast; ring
    · have h_div : e = 2 * m := by omega
      rw [h_div]
      rw [sum_ico_odd_even_split_even m]
      have h_unfold : A005187 (2 * m) = 2 * m + A005187 m := by
        have : 2 * m > 0 := by omega
        have h_un := A005187_unfold (2 * m) this
        have : (2 * m) / 2 = m := by omega
        rw [this] at h_un
        exact h_un
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
        have h_pow4 : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
          have : (4 : ℚ) = 2^2 := by norm_num
          rw [this, ← pow_mul]
        rw [h_pow4]
        rw [pow_add, pow_add, pow_one]
        have : (2 : ℚ) ^ (2 * (m - 1 - j)) = (2 : ℚ) ^ (2 * m - 2 * j - 2) := by congr 1; omega
        rw [this]
        have : (2 : ℚ) ^ (2 * j) * ((2 : ℚ) ^ (2 * m - 2 * j - 2) * 2 * (2 : ℚ) ^ A005187 (m - 1 - j)) =
            ((2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j - 2) * 2) * (2 : ℚ) ^ A005187 (m - 1 - j) := by ring
        rw [this, ← pow_add]
        have h_eq_pow : (2 : ℚ) ^ (2 * j + (2 * m - 2 * j - 2)) * 2 = (2 : ℚ) ^ (2 * m - 1) := by
          rw [← pow_succ]
          congr 1
          omega
        rw [h_eq_pow]
      have h_sum_odd : Finset.sum (Finset.range m) (fun j ↦ u_seq (2 * j + 1) * (2 : ℚ) ^ A005187 (2 * m - (2 * j + 1))) =
          (2 : ℚ) ^ (2 * m - 1) * Finset.sum (Finset.range m) (fun j ↦ (2 : ℚ) ^ A005187 (m - 1 - j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [h_odd_term j hj]
      rw [h_sum_odd]
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
        rw [h_even_unfold, pow_add]
        have h_pow4 : (4 : ℚ) ^ j = (2 : ℚ) ^ (2 * j) := by
          have : (4 : ℚ) = 2^2 := by norm_num
          rw [this, ← pow_mul]
        have h_pow_div : (2 : ℚ) ^ (2 * (m - j)) = (2 : ℚ) ^ (2 * m - 2 * j) := by congr 1; omega
        have : (2 * (4 : ℚ) ^ j * u_seq j - 1 / 2 * (4 : ℚ) ^ j) * ((2 : ℚ) ^ (2 * (m - j)) * (2 : ℚ) ^ A005187 (m - j)) =
            4 * (2 : ℚ) ^ (2 * m - 1) * (u_seq j * (2 : ℚ) ^ A005187 (m - j)) - (2 : ℚ) ^ (2 * m - 1) * (2 : ℚ) ^ A005187 (m - j) := by
          rw [h_pow4, h_pow_div]
          have h_pow_mul : (2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j) = 2 * (2 : ℚ) ^ (2 * m - 1) := by
            have : 2 * m = (2 * m - 1) + 1 := by omega
            have h_eq : (2 : ℚ) ^ (2 * m) = 2 * (2 : ℚ) ^ (2 * m - 1) := by
              nth_rewrite 1 [this]
              rw [pow_add, pow_one]; ring
            rw [← h_eq, ← pow_add]
            congr 1
            omega
          calc
            (2 * (2 : ℚ) ^ (2 * j) * u_seq j - 1 / 2 * (2 : ℚ) ^ (2 * j)) * ((2 : ℚ) ^ (2 * m - 2 * j) * (2 : ℚ) ^ A005187 (m - j))
            _ = (2 * ((2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j)) * u_seq j - 1 / 2 * ((2 : ℚ) ^ (2 * j) * (2 : ℚ) ^ (2 * m - 2 * j))) * (2 : ℚ) ^ A005187 (m - j) := by ring
            _ = (2 * (2 * (2 : ℚ) ^ (2 * m - 1)) * u_seq j - 1 / 2 * (2 * (2 : ℚ) ^ (2 * m - 1))) * (2 : ℚ) ^ A005187 (m - j) := by rw [h_pow_mul]
            _ = 4 * (2 : ℚ) ^ (2 * m - 1) * (u_seq j * (2 : ℚ) ^ A005187 (m - j)) - (2 : ℚ) ^ (2 * m - 1) * (2 : ℚ) ^ A005187 (m - j) := by ring
        exact this
      have h_sum_even : Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ u_seq (2 * j) * (2 : ℚ) ^ A005187 (2 * m - 2 * j)) =
          4 * (2 : ℚ) ^ (2 * m - 1) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ u_seq j * (2 : ℚ) ^ A005187 (m - j)) -
          (2 : ℚ) ^ (2 * m - 1) * Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [h_even_term j hj]
      rw [h_sum_even]
      have hm_lt : m < e := by omega
      have h_ih_m := IH m hm_lt hm
      have h_ih_m_div : Finset.sum (Finset.Ico 1 (m + 1)) (fun k ↦ u_seq k * (2 : ℚ) ^ A005187 (m - k)) = (2 : ℚ) ^ A005187 m * m / 2 := by linarith
      rw [h_ih_m_div]
      have h_sum_reindex1 : Finset.sum (Finset.range m) (fun j ↦ (2 : ℚ) ^ A005187 (m - 1 - j)) =
          Finset.sum (Finset.range m) (fun i ↦ (2 : ℚ) ^ A005187 i) := by
        exact _root_.sum_range_reflect (fun i ↦ (2 : ℚ) ^ A005187 i) m
      have h_sum_reindex2 : Finset.sum (Finset.Ico 1 (m + 1)) (fun j ↦ (2 : ℚ) ^ A005187 (m - j)) =
          Finset.sum (Finset.range m) (fun i ↦ (2 : ℚ) ^ A005187 i) := by
        have h_bij : ∀ j ∈ Finset.Ico 1 (m + 1), m - j ∈ Finset.range m := by
          intro j hj
          rw [Finset.mem_Ico] at hj
          rw [Finset.mem_range]; omega
        have h_inj : ∀ j1 ∈ Finset.Ico 1 (m + 1), ∀ j2 ∈ Finset.Ico 1 (m + 1), m - j1 = m - j2 → j1 = j2 := by
          intro j1 hj1 j2 hj2 h_eq
          rw [Finset.mem_Ico] at hj1 hj2; omega
        have h_surj : ∀ i ∈ Finset.range m, ∃ j, ∃ (hj : j ∈ Finset.Ico 1 (m + 1)), m - j = i := by
          intro i hi
          rw [Finset.mem_range] at hi
          use m - i
          use (by rw [Finset.mem_Ico]; omega)
          omega
        have h_map : ∀ j ∈ Finset.Ico 1 (m + 1), (2 : ℚ) ^ A005187 (m - j) = (2 : ℚ) ^ A005187 (m - j) := by
          intro j hj; rfl
        exact Finset.sum_bij (fun j _ ↦ m - j) h_bij h_inj h_surj h_map
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
          rw [pow_add, pow_one]; ring
        rw [h_pow_add]; push_cast; ring
      rw [h_algebra]
      rw [h_unfold, pow_add]; push_cast; ring

noncomputable def S_seq (e : ℕ) : ℚ := Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j))

theorem S_seq_recurrence (e : ℕ) (he : e ≥ 1) :
    e * S_seq e = 2 * Finset.sum (Finset.Ico 1 (e + 1)) (fun k ↦ u_seq k * S_seq (e - k)) := by
  unfold S_seq
  have h_split : (e : ℚ) * Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j)) =
      2 * Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) := by
    have h_eq : (e : ℚ) * Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j)) =
        Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j) * (e : ℚ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj; ring
    rw [h_eq]
    have h_split2 : ∀ j ∈ Finset.range (e + 1), a_seq j * a_seq (e - j) * (e : ℚ) =
        (j : ℚ) * a_seq j * a_seq (e - j) + a_seq j * ((e - j : ℚ) * a_seq (e - j)) := by
      intro j hj
      ring
    have h_sum_split : Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * a_seq (e - j) * (e : ℚ)) =
        Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) +
        Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * ((e - j : ℚ) * a_seq (e - j))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      exact h_split2
    rw [h_sum_split]
    have h_reflect : Finset.sum (Finset.range (e + 1)) (fun j ↦ a_seq j * ((e - j : ℚ) * a_seq (e - j))) =
        Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) := by
      have h_ref := _root_.sum_range_reflect (fun j ↦ a_seq j * ((e - j : ℚ) * a_seq (e - j))) (e + 1)
      rw [← h_ref]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have h_le : j ≤ e := by omega
      have h_sub : e + 1 - 1 - j = e - j := by omega
      rw [h_sub]
      have h_nat : e - (e - j) = j := by omega
      have h_cast : (e : ℚ) - ((e - j : ℕ) : ℚ) = (j : ℚ) := by
        rw [Nat.cast_sub h_le]
        ring
      rw [h_nat, h_cast]
      ring
    rw [h_reflect]; ring
  rw [h_split]
  congr 1
  have h_j_a : ∀ (j : ℕ), (j : ℚ) * a_seq j = Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k)) := by
    intro j
    by_cases hj0 : j = 0
    · rw [hj0]; simp
    · rw [a_seq_unfold j]
      rw [dif_neg hj0]
      have h_ne : (j : ℚ) ≠ 0 := by positivity
      have : (j : ℚ) * (Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k)) / (j : ℚ)) = Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k)) := mul_div_cancel₀ _ h_ne
      exact this
  have h_sum_j_a : Finset.sum (Finset.range (e + 1)) (fun j ↦ (j : ℚ) * a_seq j * a_seq (e - j)) =
      Finset.sum (Finset.range (e + 1)) (fun j ↦ Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k)) * a_seq (e - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [h_j_a j]
  rw [h_sum_j_a]
  have h_dist : ∀ j, Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k)) * a_seq (e - j) =
      Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k) * a_seq (e - j)) := by
    intro j; rw [Finset.sum_mul]
  simp_rw [h_dist]
  let F (j k : ℕ) : ℚ := if k ≥ 1 then u_seq k * a_seq (j - k) * a_seq (e - j) else 0
  have h_F_sum : ∀ j ∈ Finset.range (e + 1), Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k) * a_seq (e - j)) =
      Finset.sum (Finset.range (j + 1)) (fun k ↦ F j k) := by
    intro j hj
    have h_insert : Finset.range (j + 1) = insert 0 (Finset.Ico 1 (j + 1)) := by
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
      unfold F
      rw [if_pos this]
    · simp only [Finset.mem_Ico]; omega
  have h_sum_F : Finset.sum (Finset.range (e + 1)) (fun j ↦ Finset.sum (Finset.Ico 1 (j + 1)) (fun k ↦ u_seq k * a_seq (j - k) * a_seq (e - j))) =
      Finset.sum (Finset.range (e + 1)) (fun j ↦ Finset.sum (Finset.range (j + 1)) (fun k ↦ F j k)) := by
    apply Finset.sum_congr rfl
    intro j hj; exact h_F_sum j hj
  rw [h_sum_F]
  rw [sum_sum_swap e F]
  have h_split_range_0 : Finset.sum (Finset.range (e + 1)) (fun k ↦ Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ F j k)) =
      Finset.sum (Finset.Ico 1 (e + 1)) (fun k ↦ Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ F j k)) := by
    have h_insert : Finset.range (e + 1) = insert 0 (Finset.Ico 1 (e + 1)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [h_insert, Finset.sum_insert]
    · have h_zero : Finset.sum (Finset.Ico 0 (e + 1)) (fun j ↦ F j 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj; rfl
      rw [h_zero, zero_add]
    · simp only [Finset.mem_Ico]; omega
  rw [h_split_range_0]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk1 : k ≥ 1 := hk.1
  have h_inner_eq : Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ F j k) =
      Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ u_seq k * a_seq (j - k) * a_seq (e - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    unfold F
    rw [if_pos hk1]
  rw [h_inner_eq]
  have h_assoc : Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ u_seq k * a_seq (j - k) * a_seq (e - j)) =
      Finset.sum (Finset.Ico k (e + 1)) (fun j ↦ u_seq k * (a_seq (j - k) * a_seq (e - j))) := by
    apply Finset.sum_congr rfl
    intro j hj; ring
  rw [h_assoc, ← Finset.mul_sum]
  congr 1
  have h_bij : ∀ j ∈ Finset.Ico k (e + 1), j - k ∈ Finset.range (e - k + 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_range]; omega
  have h_map : ∀ j ∈ Finset.Ico k (e + 1), a_seq (j - k) * a_seq (e - j) = a_seq (j - k) * a_seq (e - k - (j - k)) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have : e - j = e - k - (j - k) := by omega
    rw [this]
  have h_inj : ∀ j1 ∈ Finset.Ico k (e + 1), ∀ j2 ∈ Finset.Ico k (e + 1), j1 - k = j2 - k → j1 = j2 := by
    intro j1 hj1 j2 hj2 h_eq
    rw [Finset.mem_Ico] at hj1 hj2; omega
  have h_surj : ∀ i ∈ Finset.range (e - k + 1), ∃ j, ∃ (hj : j ∈ Finset.Ico k (e + 1)), j - k = i := by
    intro i hi
    rw [Finset.mem_range] at hi
    use i + k
    use (by rw [Finset.mem_Ico]; omega)
    omega
  exact Finset.sum_bij (fun j _ ↦ j - k) h_bij h_inj h_surj h_map

theorem S_seq_eq_pow (e : ℕ) : S_seq e = (2 : ℚ) ^ (A005187 e) := by
  induction' e using Nat.strong_induction_on with e IH
  by_cases h0 : e = 0
  · rw [h0]
    unfold S_seq
    rw [Finset.sum_range_one]
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
      intro k hk; rw [h_sub k hk]
    rw [h_congr] at h_recurrence
    have h_recurrence2 := A_seq_recurrence e he
    rw [← h_recurrence2] at h_recurrence
    have he_q : (e : ℚ) ≠ 0 := by positivity
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
    · have h_xy : x * y ≠ 0 := Nat.mul_ne_zero hx hy
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
    simp only [ArithmeticFunction.coe_mk]
    unfold a_f
    simp
  · intro m n h
    unfold a_f_arith
    simp only [ArithmeticFunction.coe_mk]
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
    · have h_xy : x * y ≠ 0 := Nat.mul_ne_zero hx hy
      unfold A046644
      simp only [hx, hy, h_xy, ↓reduceIte]
      rw [factorization_mul_of_coprime h]
      rw [Finsupp.prod_add_index_of_disjoint]
      exact h.disjoint_primeFactors

theorem A046644_arith_mult : A046644_arith.IsMultiplicative := by
  constructor
  · unfold A046644_arith
    simp only [ArithmeticFunction.coe_mk]
    unfold A046644
    simp
  · intro m n h
    unfold A046644_arith
    simp only [ArithmeticFunction.coe_mk]
    exact A046644_mul_of_coprime m n h

theorem a_f_prime_pow (p : ℕ) (hp : p.Prime) (j : ℕ) : a_f (p ^ j) = a_seq j := by
  by_cases hj : j = 0
  · rw [hj, pow_zero]
    unfold a_f
    simp only [one_ne_zero, ↓reduceIte, factorization_one, Finsupp.prod_zero_index]
    rw [a_seq_unfold 0]
    simp
  · unfold a_f
    have h_pow_ne : p ^ j ≠ 0 := pow_ne_zero j hp.ne_zero
    simp only [h_pow_ne, ↓reduceIte]
    rw [Prime.factorization_pow hp]
    rw [Finsupp.prod_single_index]
    · rw [a_seq_unfold 0]; rfl

theorem A046644_prime_pow (p : ℕ) (hp : p.Prime) (j : ℕ) : A046644 (p ^ j) = (2 : ℚ) ^ (A005187 j) := by
  by_cases hj : j = 0
  · rw [hj, pow_zero]
    unfold A046644
    simp only [one_ne_zero, ↓reduceIte, factorization_one, Finsupp.prod_zero_index]
    rw [A005187_zero]
    simp
  · unfold A046644
    have h_pow_ne : p ^ j ≠ 0 := pow_ne_zero j hp.ne_zero
    simp only [h_pow_ne, ↓reduceIte]
    rw [Prime.factorization_pow hp]
    rw [Finsupp.prod_single_index]
    · rw [A005187_zero]; rfl

theorem a_f_arith_conv_eq : a_f_arith * a_f_arith = A046644_arith := by
  have h1 : (a_f_arith * a_f_arith).IsMultiplicative := a_f_arith_mult.mul a_f_arith_mult
  have h2 : A046644_arith.IsMultiplicative := A046644_arith_mult
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (a_f_arith * a_f_arith) h1 A046644_arith h2]
  intro p i hp
  rw [ArithmeticFunction.mul_apply]
  have h_eq_af : ∀ x : ℕ × ℕ, a_f_arith x.1 * a_f_arith x.2 = a_f x.1 * a_f x.2 := by
    intro x; rfl
  simp_rw [h_eq_af]
  rw [sum_divisorsAntidiagonal (fun i1 i2 ↦ a_f i1 * a_f i2)]
  rw [sum_divisors_prime_pow hp]
  have h_term : ∀ j ∈ Finset.range (i + 1), a_f (p ^ j) * a_f (p ^ i / p ^ j) = a_seq j * a_seq (i - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [a_f_prime_pow p hp j]
    have : p ^ i / p ^ j = p ^ (i - j) := by
      rw [Nat.pow_div (by omega) hp.pos]
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
      have h_cases : ∀ d ∈ divisors n, d = 1 ∨ d = n ∨ (d > 1 ∧ d < n) := by
        intro d hd
        have h_dvd : d ∣ n := (mem_divisors.mp hd).1
        have h_le : d ≤ n := Nat.le_of_dvd (by omega) h_dvd
        have h_nz : d ≠ 0 := by
          rintro rfl
          simp only [zero_dvd_iff] at h_dvd
          omega
        omega
      have h_term_eq : ∀ d ∈ divisors n, a_f d * a_f (n / d) =
          (if h_prop : d > 1 ∧ d < n then a_f d * a_f (n / d) else 0) +
          (if d = 1 then a_f n else 0) +
          (if d = n then a_f n else 0) := by
        intro d hd
        have hd_cases := h_cases d hd
        rcases hd_cases with rfl | rfl | h_mid
        · have : ¬(1 > 1 ∧ 1 < n) := by omega
          have : 1 ≠ n := by omega
          simp [this]
          have h_a1 : a_f 1 = 1 := by
            unfold a_f; simp
          rw [h_a1, one_mul]
        · have : ¬(d > 1 ∧ d < d) := by omega
          have : d ≠ 1 := by omega
          simp [this]
          have h_nn : d / d = 1 := Nat.div_self (by omega)
          have h_a1 : a_f 1 = 1 := by
            unfold a_f; simp
          rw [h_nn, h_a1, mul_one]
        · have hd_mid : d > 1 ∧ d < n := h_mid
          have hd1 : d ≠ 1 := by omega
          have hdn : d ≠ n := by omega
          simp [hd1, hdn, hd_mid]
      have h_sum_all : Finset.sum (divisors n) (fun d ↦ a_f d * a_f (n / d)) =
          Finset.sum (divisors n) (fun d ↦ if h_prop : d > 1 ∧ d < n then a_f d * a_f (n / d) else 0) +
          Finset.sum (divisors n) (fun d ↦ if d = 1 then a_f n else 0) +
          Finset.sum (divisors n) (fun d ↦ if d = n then a_f n else 0) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        exact h_term_eq
      have h_sum_1 : Finset.sum (divisors n) (fun d ↦ if d = 1 then a_f n else 0) = a_f n := by
        have h_mem : 1 ∈ divisors n := by
          rw [mem_divisors]; exact ⟨one_dvd n, by omega⟩
        have : (if 1 = 1 then a_f n else 0) = a_f n := by simp
        conv_rhs => rw [← this]
        apply Finset.sum_eq_single 1
        · intro b hb hb1
          simp [hb1]
        · intro h_not
          exact (h_not h_mem).elim
      have h_sum_n : Finset.sum (divisors n) (fun d ↦ if d = n then a_f n else 0) = a_f n := by
        have h_mem : n ∈ divisors n := by
          rw [mem_divisors]; exact ⟨dvd_rfl, by omega⟩
        have : (if n = n then a_f n else 0) = a_f n := by simp
        conv_rhs => rw [← this]
        apply Finset.sum_eq_single n
        · intro b hb hbn
          simp [hbn]
        · intro h_not
          exact (h_not h_mem).elim
      rw [h_sum_1, h_sum_n] at h_sum_all
      have h_conv_eq : (a_f_arith * a_f_arith) n = A046644 n := by
        rw [a_f_arith_conv_eq]; rfl
      have h_conv_apply : (a_f_arith * a_f_arith) n = Finset.sum (divisors n) (fun d ↦ a_f d * a_f (n / d)) := by
        rw [ArithmeticFunction.mul_apply]
        change ∑ x ∈ n.divisorsAntidiagonal, a_f x.1 * a_f x.2 = ∑ d ∈ n.divisors, a_f d * a_f (n / d)
        rw [sum_divisorsAntidiagonal (fun i1 i2 ↦ a_f i1 * a_f i2)]
      rw [h_conv_apply] at h_conv_eq
      rw [h_conv_eq] at h_sum_all
      have : Finset.sum (divisors n) (fun d ↦ if h_prop : d > 1 ∧ d < n then a_f d * a_f (n / d) else 0) = A046644 n - 2 * a_f n := by
        linarith
      rw [this]; ring

/--
A317940 No negative terms among the first 2^20 terms. Is the sequence nonnegative?
Conjecture: The sequence of rational numbers $A317940\_f(n)$ is nonnegative for all $n \ge 1$.
-/
theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 := by
  rw [A317940_f_eq_a_f]
  unfold a_f
  have h_ne : n ≠ 0 := by omega
  simp only [h_ne, ↓reduceIte]
  apply Finset.prod_nonneg
  intro i hi
  exact a_seq_nonneg (n.factorization i)
