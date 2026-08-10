import FormalConjectures.Util.ProblemImports

open Nat Real Finset


def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)
def a_rat (n : ℕ) : ℚ := (a n : ℚ)⁻¹
def catalan_reciprocal_sum (j k : ℕ) : ℚ := (Finset.Icc j k).sum a_rat
def oeis_108_index_cond (j k : ℕ) : Prop := 1 ≤ k ∧ min 2 k ≤ j ∧ j ≤ k
noncomputable def frac_part (q : ℚ) : ℝ := Int.fract (q : ℝ)

lemma a_eq_catalan (n : ℕ) : a n = catalan n := by
  dsimp [a]
  rw [catalan_eq_centralBinom_div]
  rfl

lemma catalan_bound_helper (n : ℕ) (hn : 2 ≤ n) : 5 * catalan n * (n + 1) * (n + 2) ≤ 2 * catalan (n + 1) * (n + 1) * (n + 2) := by
  have h1 : 5 * catalan n * (n + 1) * (n + 2) = 5 * (n + 2) * n.centralBinom := by
    calc
      5 * catalan n * (n + 1) * (n + 2) = 5 * (n + 2) * ((n + 1) * catalan n) := by ring
      _ = 5 * (n + 2) * n.centralBinom := by rw [succ_mul_catalan_eq_centralBinom]
  have h2 : 2 * catalan (n + 1) * (n + 1) * (n + 2) = 4 * (2 * n + 1) * n.centralBinom := by
    calc
      2 * catalan (n + 1) * (n + 1) * (n + 2) = 2 * (n + 1) * ((n + 2) * catalan (n + 1)) := by ring
      _ = 2 * (n + 1) * (n + 1).centralBinom := by rw [succ_mul_catalan_eq_centralBinom]
      _ = 2 * ((n + 1) * (n + 1).centralBinom) := by ring
      _ = 2 * (2 * (2 * n + 1) * n.centralBinom) := by rw [succ_mul_centralBinom_succ]
      _ = 4 * (2 * n + 1) * n.centralBinom := by ring
  rw [h1, h2]
  have h3 : 5 * (n + 2) ≤ 4 * (2 * n + 1) := by omega
  -- now we can use Nat.mul_le_mul_right or similar
  exact Nat.mul_le_mul_right n.centralBinom h3

lemma catalan_bound (n : ℕ) (hn : 2 ≤ n) : 5 * catalan n ≤ 2 * catalan (n + 1) := by
  have h_helper := catalan_bound_helper n hn
  have h_pos : 0 < (n + 1) * (n + 2) := Nat.mul_pos (by omega) (by omega)
  -- We want to rewrite the multiplication
  have h_mul_left : 5 * catalan n * (n + 1) * (n + 2) = (5 * catalan n) * ((n + 1) * (n + 2)) := by ring
  have h_mul_right : 2 * catalan (n + 1) * (n + 1) * (n + 2) = (2 * catalan (n + 1)) * ((n + 1) * (n + 2)) := by ring
  rw [h_mul_left, h_mul_right] at h_helper
  exact Nat.le_of_mul_le_mul_right h_helper h_pos

lemma catalan_pos (n : ℕ) : 0 < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have h_cb_pos := centralBinom_pos n
  cases h_cat : catalan n with
  | zero =>
    rw [h_cat] at h
    simp at h
    omega
  | succ k =>
    omega

lemma catalan_le_mul_power (m k : ℕ) (hm : 2 ≤ m) : (5 : ℕ) ^ k * catalan m ≤ (2 : ℕ) ^ k * catalan (m + k) := by
  induction' k with k ih
  · simp
  · -- Inductive step: k -> k + 1
    have h_step : 5 * catalan (m + k) ≤ 2 * catalan (m + k + 1) := by
      apply catalan_bound
      omega
    calc
      (5 : ℕ) ^ (k + 1) * catalan m = 5 * (5 ^ k * catalan m) := by ring
      _ ≤ 5 * (2 ^ k * catalan (m + k)) := Nat.mul_le_mul_left 5 ih
      _ = 2 ^ k * (5 * catalan (m + k)) := by ring
      _ ≤ 2 ^ k * (2 * catalan (m + k + 1)) := Nat.mul_le_mul_left (2 ^ k) h_step
      _ = 2 ^ (k + 1) * catalan (m + k + 1) := by ring

lemma catalan_recip_le_mul_power (m k : ℕ) (hm : 2 ≤ m) : ((catalan (m + k) : ℝ))⁻¹ ≤ (2 / 5 : ℝ) ^ k * ((catalan m : ℝ))⁻¹ := by
  have h := catalan_le_mul_power m k hm
  have h_real : (5 : ℝ) ^ k * (catalan m : ℝ) ≤ (2 : ℝ) ^ k * (catalan (m + k) : ℝ) := by
    exact_mod_cast h
  have h_m_pos : 0 < (catalan m : ℝ) := by
    exact_mod_cast (catalan_pos m)
  have h_mk_pos : 0 < (catalan (m + k) : ℝ) := by
    exact_mod_cast (catalan_pos (m + k))
  have h5_pos : 0 < (5 : ℝ) ^ k := by positivity
  have h2_pos : 0 < (2 : ℝ) ^ k := by positivity
  -- algebraically: a * b <= c * d -> 1/d <= (c/a) * (1/b)
  -- we can prove this by multiplying both sides of h_real by ((5 : ℝ)^k * (catalan (m+k) : ℝ))⁻¹
  have h_div : (5 : ℝ) ^ k * (catalan m : ℝ) / ((5 : ℝ) ^ k * (catalan (m + k) : ℝ)) ≤ (2 : ℝ) ^ k * (catalan (m + k) : ℝ) / ((5 : ℝ) ^ k * (catalan (m + k) : ℝ)) := by
    apply div_le_div_of_nonneg_right h_real
    positivity
  -- Now simplify both sides
  have h_lhs : (5 : ℝ) ^ k * (catalan m : ℝ) / ((5 : ℝ) ^ k * (catalan (m + k) : ℝ)) = (catalan m : ℝ) / (catalan (m + k) : ℝ) := by
    have : (5 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
  have h_rhs : (2 : ℝ) ^ k * (catalan (m + k) : ℝ) / ((5 : ℝ) ^ k * (catalan (m + k) : ℝ)) = (2 : ℝ) ^ k / (5 : ℝ) ^ k := by
    have : (catalan (m + k) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [h_lhs, h_rhs] at h_div
  -- now we have: (catalan m : ℝ) / (catalan (m + k) : ℝ) ≤ (2 : ℝ) ^ k / (5 : ℝ) ^ k
  -- we want to divide by (catalan m : ℝ) on both sides
  have h_div2 : (catalan m : ℝ) / (catalan (m + k) : ℝ) / (catalan m : ℝ) ≤ ((2 : ℝ) ^ k / (5 : ℝ) ^ k) / (catalan m : ℝ) := by
    apply div_le_div_of_nonneg_right h_div
    positivity
  have h_lhs2 : (catalan m : ℝ) / (catalan (m + k) : ℝ) / (catalan m : ℝ) = (catalan (m + k) : ℝ)⁻¹ := by
    have : (catalan m : ℝ) ≠ 0 := by positivity
    have : (catalan (m + k) : ℝ) ≠ 0 := by positivity
    field_simp
  have h_rhs2 : ((2 : ℝ) ^ k / (5 : ℝ) ^ k) / (catalan m : ℝ) = (2 / 5 : ℝ) ^ k * (catalan m : ℝ)⁻¹ := by
    have : (catalan m : ℝ) ≠ 0 := by positivity
    rw [div_div]
    rw [div_pow]
    ring
  rw [h_lhs2, h_rhs2] at h_div2
  exact h_div2

lemma geom_sum_two_fifths (n : ℕ) : (∑ j ∈ range n, (2 / 5 : ℝ) ^ j) = (5 / 3 : ℝ) * (1 - (2 / 5 : ℝ) ^ n) := by
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, ih]
    -- We want to prove: (5 / 3) * (1 - (2 / 5) ^ n) + (2 / 5) ^ n = (5 / 3) * (1 - (2 / 5) ^ (n + 1))
    -- This is just real arithmetic, which `ring` can do if we expand the power!
    have h_pow : (2 / 5 : ℝ) ^ (n + 1) = (2 / 5 : ℝ) ^ n * (2 / 5) := by ring
    rw [h_pow]
    ring

lemma geom_sum_two_fifths_lt (n : ℕ) : (∑ j ∈ range n, (2 / 5 : ℝ) ^ j) < 5 / 3 := by
  rw [geom_sum_two_fifths]
  have h_pow_pos : 0 < (2 / 5 : ℝ) ^ n := by positivity
  have h_sub_lt : 1 - (2 / 5 : ℝ) ^ n < 1 := by linarith
  have h_mul_lt : (5 / 3 : ℝ) * (1 - (2 / 5 : ℝ) ^ n) < (5 / 3) * 1 := mul_lt_mul_of_pos_left h_sub_lt (by norm_num)
  rw [mul_one] at h_mul_lt
  exact h_mul_lt


lemma catalan_recip_sum_le_geom (m k : ℕ) (hm : 2 ≤ m) : ((Finset.Icc (m + 1) k).sum (fun i => ((catalan i : ℝ))⁻¹)) ≤ ((Finset.range (k - m)).sum (fun j => (2 / 5 : ℝ) ^ j)) * ((catalan (m + 1) : ℝ))⁻¹ := by
  induction' k with k ih
  · -- Case k = 0
    have h_empty_icc : Finset.Icc (m + 1) 0 = ∅ := by
      ext x
      simp
    have h_sub : 0 - m = 0 := by omega
    rw [h_empty_icc, h_sub]
    simp
  · -- Case k + 1
    by_cases h_lt : k + 1 < m + 1
    · have h_empty_icc : Finset.Icc (m + 1) (k + 1) = ∅ := by
        ext x
        simp
        omega
      have h_sub : k + 1 - m = 0 := by omega
      rw [h_empty_icc, h_sub]
      simp
    · -- Here k + 1 >= m + 1, so m <= k
      have h_ge : m ≤ k := by omega
      have h_sum_split : ∑ i ∈ Icc (m + 1) (k + 1), ((catalan i : ℝ))⁻¹ = (∑ i ∈ Icc (m + 1) k, ((catalan i : ℝ))⁻¹) + ((catalan (k + 1) : ℝ))⁻¹ := by
        apply Finset.sum_Icc_succ_top
        omega
      rw [h_sum_split]
      -- We want to bound both terms
      have h_term2 : ((catalan (k + 1) : ℝ))⁻¹ ≤ (2 / 5 : ℝ) ^ (k - m) * ((catalan (m + 1) : ℝ))⁻¹ := by
        have h_eq : k + 1 = m + 1 + (k - m) := by omega
        rw [h_eq]
        apply catalan_recip_le_mul_power (m + 1) (k - m)
        omega
      have h_sub_succ : k + 1 - m = (k - m) + 1 := by omega
      rw [h_sub_succ]
      rw [Finset.sum_range_succ]
      -- LHS is: sum(Icc) + recip(k+1)
      -- RHS is: (sum(range) + (2/5)^(k-m)) * recip(m+1)
      have h_calc : (∑ i ∈ Icc (m + 1) k, ((catalan i : ℝ))⁻¹) + ((catalan (k + 1) : ℝ))⁻¹ ≤ (∑ j ∈ range (k - m), (2 / 5 : ℝ) ^ j) * ((catalan (m + 1) : ℝ))⁻¹ + (2 / 5 : ℝ) ^ (k - m) * ((catalan (m + 1) : ℝ))⁻¹ := by
        exact add_le_add ih h_term2
      have h_ring : (∑ j ∈ range (k - m), (2 / 5 : ℝ) ^ j) * ((catalan (m + 1) : ℝ))⁻¹ + (2 / 5 : ℝ) ^ (k - m) * ((catalan (m + 1) : ℝ))⁻¹ = ((∑ j ∈ range (k - m), (2 / 5 : ℝ) ^ j) + (2 / 5 : ℝ) ^ (k - m)) * ((catalan (m + 1) : ℝ))⁻¹ := by
        ring
      rw [h_ring] at h_calc
      exact h_calc


lemma catalan_recip_sum_lt (m k : ℕ) (hm : 2 ≤ m) : ((Finset.Icc (m + 1) k).sum (fun i => ((catalan i : ℝ))⁻¹)) < ((catalan m : ℝ))⁻¹ := by
  have h_geom := catalan_recip_sum_le_geom m k hm
  have h_lt := geom_sum_two_fifths_lt (k - m)
  have h_m1_pos : 0 < ((catalan (m + 1) : ℝ))⁻¹ := inv_pos.mpr (by exact_mod_cast (catalan_pos (m + 1)))
  have h_mul : ((Finset.range (k - m)).sum (fun j => (2 / 5 : ℝ) ^ j)) * ((catalan (m + 1) : ℝ))⁻¹ < (5 / 3 : ℝ) * ((catalan (m + 1) : ℝ))⁻¹ := by
    exact mul_lt_mul_of_pos_right h_lt h_m1_pos
  have h_comb : ((Finset.Icc (m + 1) k).sum (fun i => ((catalan i : ℝ))⁻¹)) < (5 / 3 : ℝ) * ((catalan (m + 1) : ℝ))⁻¹ := by
    exact lt_of_le_of_lt h_geom h_mul
  have h_bound := catalan_bound m hm
  have h_bound_real : 5 * (catalan m : ℝ) ≤ 2 * (catalan (m + 1) : ℝ) := by
    exact_mod_cast h_bound
  have h_bound_lt : 5 * (catalan m : ℝ) < 3 * (catalan (m + 1) : ℝ) := by
    have : 2 * (catalan (m + 1) : ℝ) < 3 * (catalan (m + 1) : ℝ) := by
      have h_pos_m1 : 0 < (catalan (m + 1) : ℝ) := by exact_mod_cast catalan_pos (m + 1)
      linarith
    linarith
  have h_last : (5 / 3 : ℝ) * ((catalan (m + 1) : ℝ))⁻¹ < ((catalan m : ℝ))⁻¹ := by
    have h_pos_m : 0 < (catalan m : ℝ) := by exact_mod_cast catalan_pos m
    have h_pos_m1 : 0 < (catalan (m + 1) : ℝ) := by exact_mod_cast catalan_pos (m + 1)
    have : (catalan m : ℝ) ≠ 0 := ne_of_gt h_pos_m
    have : (catalan (m + 1) : ℝ) ≠ 0 := ne_of_gt h_pos_m1
    field_simp
    linarith
  exact lt_trans h_comb h_last

lemma finset_partition_sum {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ) :
  s.sum f = (s \ t).sum f + (s ∩ t).sum f := by
  have h_sub : s ∩ t ⊆ s := by simp
  have h := (sum_sdiff (f := f) h_sub).symm
  have h_eq : s \ (s ∩ t) = s \ t := by
    ext x
    simp only [mem_sdiff, mem_inter]
    tauto
  rw [h_eq] at h
  exact h

lemma nonempty_of_sum_eq_sum {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) (h_sum : (s \ t).sum f = (t \ s).sum f) (h_ne : s ≠ t) :
  (s \ t).Nonempty ∧ (t \ s).Nonempty := by
  have h_cases : (s \ t).Nonempty ∧ (t \ s).Nonempty ∨ (s \ t) = ∅ ∧ (t \ s) = ∅ := by
    by_cases h_st : (s \ t) = ∅
    · right
      have h_sum1 : (s \ t).sum f = 0 := by rw [h_st]; simp
      rw [h_sum1] at h_sum
      have h_ts : (t \ s) = ∅ := by
        by_contra h_ts_ne
        have h_ts_nonempty : (t \ s).Nonempty := nonempty_iff_ne_empty.mpr h_ts_ne
        have h_pos : 0 < (t \ s).sum f := sum_pos (fun x hx => hf x) h_ts_nonempty
        linarith
      exact ⟨h_st, h_ts⟩
    · by_cases h_ts : (t \ s) = ∅
      · right
        have h_sum2 : (t \ s).sum f = 0 := by rw [h_ts]; simp
        rw [h_sum2] at h_sum
        have h_st_empty : (s \ t) = ∅ := by
          by_contra h_st_ne
          have h_st_nonempty : (s \ t).Nonempty := nonempty_iff_ne_empty.mpr h_st_ne
          have h_pos : 0 < (s \ t).sum f := sum_pos (fun x hx => hf x) h_st_nonempty
          linarith
        exact ⟨h_st_empty, h_ts⟩
      · left
        exact ⟨nonempty_iff_ne_empty.mpr h_st, nonempty_iff_ne_empty.mpr h_ts⟩
  rcases h_cases with h_both | h_empty
  · exact h_both
  · exfalso
    have h_sub1 : s ⊆ t := sdiff_eq_empty_iff_subset.mp h_empty.1
    have h_sub2 : t ⊆ s := sdiff_eq_empty_iff_subset.mp h_empty.2
    have h_eq : s = t := subset_antisymm h_sub1 h_sub2
    exact h_ne h_eq

lemma distinct_sum_of_distinct_Icc {j1 k1 j2 k2 : ℕ} (hj1 : 2 ≤ j1) (_hk1 : j1 ≤ k1) (hj2 : 2 ≤ j2) (_hk2 : j2 ≤ k2) (h_ne : Icc j1 k1 ≠ Icc j2 k2) :
  (Icc j1 k1).sum (fun i => ((catalan i : ℝ))⁻¹) ≠ (Icc j2 k2).sum (fun i => ((catalan i : ℝ))⁻¹) := by
  intro h_sum
  let s := Icc j1 k1
  let t := Icc j2 k2
  let f := fun i => ((catalan i : ℝ))⁻¹
  have hf_pos : ∀ x, 0 < f x := by
    intro x
    have h_pos : 0 < (catalan x : ℝ) := by exact_mod_cast catalan_pos x
    exact inv_pos.mpr h_pos
  have h_part1 := finset_partition_sum s t f
  have h_part2 := finset_partition_sum t s f
  have h_inter_comm : s ∩ t = t ∩ s := inter_comm _ _
  rw [h_inter_comm] at h_part1
  rw [h_sum] at h_part1
  have h_sum_eq : (s \ t).sum f = (t \ s).sum f := by
    linarith
  have h_nonempty := nonempty_of_sum_eq_sum s t f hf_pos h_sum_eq h_ne
  have h_s_t_nonempty : (s \ t).Nonempty := h_nonempty.1
  have h_t_s_nonempty : (t \ s).Nonempty := h_nonempty.2
  let U := (s \ t) ∪ (t \ s)
  have h_U_nonempty : U.Nonempty := by
    rcases h_s_t_nonempty with ⟨x, hx⟩
    exact ⟨x, mem_union_left _ hx⟩
  let m := U.min' h_U_nonempty
  have hm_U : m ∈ U := min'_mem U h_U_nonempty
  have h_cases : m ∈ s \ t ∨ m ∈ t \ s := by
    exact mem_union.mp hm_U
  rcases h_cases with hm_st | hm_ts
  · have hm_ge2 : 2 ≤ m := by
      have h_m_s : m ∈ s := (mem_sdiff.mp hm_st).1
      rw [mem_Icc] at h_m_s
      omega
    have h_sub_ts : t \ s ⊆ Icc (m + 1) k2 := by
      intro x hx
      simp only [mem_Icc]
      have hx_t : x ∈ t := (mem_sdiff.mp hx).1
      rw [mem_Icc] at hx_t
      have hx_U : x ∈ U := mem_union_right _ hx
      have hm_le_x : m ≤ x := min'_le U x hx_U
      have h_ne_m : x ≠ m := by
        intro h_eq
        subst h_eq
        have h_mem_s : m ∈ s := (mem_sdiff.mp hm_st).1
        have h_not_mem_s : m ∉ s := (mem_sdiff.mp hx).2
        exact h_not_mem_s h_mem_s
      have hm_lt_x : m < x := lt_of_le_of_ne hm_le_x h_ne_m.symm
      exact ⟨hm_lt_x, hx_t.2⟩
    have h_sum_le : (t \ s).sum f ≤ (Icc (m + 1) k2).sum f := by
      apply sum_le_sum_of_subset_of_nonneg h_sub_ts
      intro i hi hnot
      exact le_of_lt (hf_pos i)
    have h_lt_fm : (Icc (m + 1) k2).sum f < f m := by
      exact catalan_recip_sum_lt m k2 hm_ge2
    have h_ts_lt_fm : (t \ s).sum f < f m := lt_of_le_of_lt h_sum_le h_lt_fm
    have h_fm_le_st : f m ≤ (s \ t).sum f := by
      apply single_le_sum
      · intro i hi
        exact le_of_lt (hf_pos i)
      · exact hm_st
    linarith
  · have hm_ge2 : 2 ≤ m := by
      have h_m_t : m ∈ t := (mem_sdiff.mp hm_ts).1
      rw [mem_Icc] at h_m_t
      omega
    have h_sub_st : s \ t ⊆ Icc (m + 1) k1 := by
      intro x hx
      simp only [mem_Icc]
      have hx_s : x ∈ s := (mem_sdiff.mp hx).1
      rw [mem_Icc] at hx_s
      have hx_U : x ∈ U := mem_union_left _ hx
      have hm_le_x : m ≤ x := min'_le U x hx_U
      have h_ne_m : x ≠ m := by
        intro h_eq
        subst h_eq
        have h_mem_t : m ∈ t := (mem_sdiff.mp hm_ts).1
        have h_not_mem_t : m ∉ t := (mem_sdiff.mp hx).2
        exact h_not_mem_t h_mem_t
      have hm_lt_x : m < x := lt_of_le_of_ne hm_le_x h_ne_m.symm
      exact ⟨hm_lt_x, hx_s.2⟩
    have h_sum_le : (s \ t).sum f ≤ (Icc (m + 1) k1).sum f := by
      apply sum_le_sum_of_subset_of_nonneg h_sub_st
      intro i hi hnot
      exact le_of_lt (hf_pos i)
    have h_lt_fm : (Icc (m + 1) k1).sum f < f m := by
      exact catalan_recip_sum_lt m k1 hm_ge2
    have h_st_lt_fm : (s \ t).sum f < f m := lt_of_le_of_lt h_sum_le h_lt_fm
    have h_fm_le_ts : f m ≤ (t \ s).sum f := by
      apply single_le_sum
      · intro i hi
        exact le_of_lt (hf_pos i)
      · exact hm_ts
    linarith


lemma oeis_108_cond_ge_two {j k : ℕ} (cond : oeis_108_index_cond j k) (hne : (j, k) ≠ (1, 1)) : 2 ≤ j ∧ j ≤ k := by
  dsimp [oeis_108_index_cond] at cond
  rcases cond with ⟨hk, hj, hjk⟩
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k = 1 := by omega
    subst this
    simp at hj
    have : j = 1 := by omega
    subst this
    exact hne rfl
  have hj2 : 2 ≤ j := by omega
  exact ⟨hj2, hjk⟩

lemma fract_eq_self_of_nonneg_of_lt_one {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) : Int.fract x = x := by
  have h_floor : ⌊x⌋ = 0 := by
    rw [Int.floor_eq_iff]
    simp
    exact ⟨h1, h2⟩
  have h_fract : x - (⌊x⌋ : ℝ) = Int.fract x := Int.self_sub_floor x
  rw [h_floor] at h_fract
  simp only [Int.cast_zero, sub_zero] at h_fract
  exact h_fract.symm

lemma sum_catalan_recip_eq {j k : ℕ} : ((catalan_reciprocal_sum j k : ℚ) : ℝ) = (Icc j k).sum (fun i => ((catalan i : ℝ))⁻¹) := by
  dsimp [catalan_reciprocal_sum]
  push_cast
  congr 1
  ext i
  dsimp [a_rat]
  push_cast
  rw [a_eq_catalan i]

lemma frac_part_eq_self {j k : ℕ} (cond : oeis_108_index_cond j k) (hne : (j, k) ≠ (1, 1)) : frac_part (catalan_reciprocal_sum j k) = (Icc j k).sum (fun i => (catalan i : ℝ)⁻¹) := by
  have h_ge := oeis_108_cond_ge_two cond hne
  have hj : 2 ≤ j := h_ge.1
  have hjk : j ≤ k := h_ge.2
  dsimp [frac_part]
  rw [sum_catalan_recip_eq]
  let S := ∑ i ∈ Icc j k, ((catalan i : ℝ))⁻¹
  have h_pos : 0 < S := by
    apply sum_pos
    · intro i hi
      have h_pos : 0 < (catalan i : ℝ) := by exact_mod_cast catalan_pos i
      exact inv_pos.mpr h_pos
    · exact nonempty_Icc.mpr hjk
  have h_lt1 : S < 1 := by
    have h_sub : Icc j k ⊆ Icc 2 k := by
      intro x hx
      simp only [mem_Icc] at hx ⊢
      omega
    have h_sum_le : S ≤ ∑ i ∈ Icc 2 k, ((catalan i : ℝ))⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg h_sub
      intro i hi hnot
      have h_pos : 0 < (catalan i : ℝ) := by exact_mod_cast catalan_pos i
      exact le_of_lt (inv_pos.mpr h_pos)
    have h_sum_split : ∑ i ∈ Icc 2 k, ((catalan i : ℝ))⁻¹ = ((catalan 2 : ℝ))⁻¹ + ∑ i ∈ Icc 3 k, ((catalan i : ℝ))⁻¹ := by
      have h_eq_set : Icc 2 k = insert 2 (Icc 3 k) := by
        ext x
        simp only [mem_Icc, mem_insert]
        omega
      rw [h_eq_set]
      rw [Finset.sum_insert]
      simp

    have h_tail_lt : ∑ i ∈ Icc 3 k, ((catalan i : ℝ))⁻¹ < ((catalan 2 : ℝ))⁻¹ := by
      exact catalan_recip_sum_lt 2 k (by omega)
    have h_c2 : catalan 2 = 2 := catalan_two
    have h_c2_real : (catalan 2 : ℝ) = 2 := by exact_mod_cast h_c2
    have h_recip2 : ((catalan 2 : ℝ))⁻¹ = 1 / 2 := by
      rw [h_c2_real]; ring
    have h_sum_lt : S < ((catalan 2 : ℝ))⁻¹ + ((catalan 2 : ℝ))⁻¹ := by
      linarith
    rw [h_recip2] at h_sum_lt
    linarith
  exact fract_eq_self_of_nonneg_of_lt_one (le_of_lt h_pos) h_lt1

lemma Icc_inj_of_le {j1 k1 j2 k2 : ℕ} (h1 : j1 ≤ k1) (h2 : j2 ≤ k2) (h : Icc j1 k1 = Icc j2 k2) : j1 = j2 ∧ k1 = k2 := by
  have hj1 : j1 ∈ Icc j1 k1 := by simp [h1]
  rw [h] at hj1
  simp only [mem_Icc] at hj1
  have hj2 : j2 ∈ Icc j2 k2 := by simp [h2]
  rw [← h] at hj2
  simp only [mem_Icc] at hj2
  have hk1 : k1 ∈ Icc j1 k1 := by simp [h1]
  rw [h] at hk1
  simp only [mem_Icc] at hk1
  have hk2 : k2 ∈ Icc j2 k2 := by simp [h2]
  rw [← h] at hk2
  simp only [mem_Icc] at hk2
  have hj : j1 = j2 := by omega
  have hk : k1 = k2 := by omega
  exact ⟨hj, hk⟩

theorem oeis_108_conjecture_2 :
  ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄,
     oeis_108_index_cond j₁ k₁ →
     oeis_108_index_cond j₂ k₂ →
     (j₁, k₁) ≠ (j₂, k₂) →
     frac_part (catalan_reciprocal_sum j₁ k₁) ≠ frac_part (catalan_reciprocal_sum j₂ k₂) := by
  intro j1 k1 j2 k2 cond1 cond2 h_ne
  by_cases h11_1 : j1 = 1 ∧ k1 = 1
  · have h11_1_eq : (j1, k1) = (1, 1) := by ext <;> simp [h11_1.1, h11_1.2]
    have h11_2 : (j2, k2) ≠ (1, 1) := by
      intro h_eq
      exact h_ne (h11_1_eq.trans h_eq.symm)
    have h_fp1 : frac_part (catalan_reciprocal_sum j1 k1) = 0 := by
      have hj1 : j1 = 1 := h11_1.1
      have hk1 : k1 = 1 := h11_1.2
      rw [hj1, hk1]
      dsimp [frac_part, catalan_reciprocal_sum, a_rat, a]
      have h_sum : ∑ i ∈ Icc 1 1, a_rat i = 1 := by
        have h_eq : Icc 1 1 = {1} := by ext x; simp
        rw [h_eq]
        simp [a_rat, a]
      rw [h_sum]
      simp
    have h_fp2 : frac_part (catalan_reciprocal_sum j2 k2) = ∑ i ∈ Icc j2 k2, ((catalan i : ℝ))⁻¹ := by
      exact frac_part_eq_self cond2 h11_2
    rw [h_fp1, h_fp2]
    intro h_eq
    have h_pos : 0 < ∑ i ∈ Icc j2 k2, ((catalan i : ℝ))⁻¹ := by
      have h_ge := oeis_108_cond_ge_two cond2 h11_2
      apply sum_pos
      · intro i hi
        have h_pos : 0 < (catalan i : ℝ) := by exact_mod_cast catalan_pos i
        exact inv_pos.mpr h_pos
      · exact nonempty_Icc.mpr h_ge.2
    linarith
  · have h11_1_ne : (j1, k1) ≠ (1, 1) := by
      intro h_eq
      injection h_eq with hj hk
      exact h11_1 ⟨hj, hk⟩
    by_cases h11_2 : j2 = 1 ∧ k2 = 1
    · have h11_2_eq : (j2, k2) = (1, 1) := by ext <;> simp [h11_2.1, h11_2.2]
      have h_fp1 : frac_part (catalan_reciprocal_sum j1 k1) = ∑ i ∈ Icc j1 k1, ((catalan i : ℝ))⁻¹ := by
        exact frac_part_eq_self cond1 h11_1_ne
      have h_fp2 : frac_part (catalan_reciprocal_sum j2 k2) = 0 := by
        have hj2 : j2 = 1 := h11_2.1
        have hk2 : k2 = 1 := h11_2.2
        rw [hj2, hk2]
        dsimp [frac_part, catalan_reciprocal_sum, a_rat, a]
        have h_sum : ∑ i ∈ Icc 1 1, a_rat i = 1 := by
          have h_eq : Icc 1 1 = {1} := by ext x; simp
          rw [h_eq]
          simp [a_rat, a]
        rw [h_sum]
        simp
      rw [h_fp1, h_fp2]
      intro h_eq
      have h_pos : 0 < ∑ i ∈ Icc j1 k1, ((catalan i : ℝ))⁻¹ := by
        have h_ge := oeis_108_cond_ge_two cond1 h11_1_ne
        apply sum_pos
        · intro i hi
          have h_pos : 0 < (catalan i : ℝ) := by exact_mod_cast catalan_pos i
          exact inv_pos.mpr h_pos
        · exact nonempty_Icc.mpr h_ge.2
      linarith
    · have h11_2_ne : (j2, k2) ≠ (1, 1) := by
        intro h_eq
        injection h_eq with hj hk
        exact h11_2 ⟨hj, hk⟩
      have h_fp1 : frac_part (catalan_reciprocal_sum j1 k1) = ∑ i ∈ Icc j1 k1, ((catalan i : ℝ))⁻¹ := by
        exact frac_part_eq_self cond1 h11_1_ne
      have h_fp2 : frac_part (catalan_reciprocal_sum j2 k2) = ∑ i ∈ Icc j2 k2, ((catalan i : ℝ))⁻¹ := by
        exact frac_part_eq_self cond2 h11_2_ne
      rw [h_fp1, h_fp2]
      have h_ge1 := oeis_108_cond_ge_two cond1 h11_1_ne
      have h_ge2 := oeis_108_cond_ge_two cond2 h11_2_ne
      have h_icc_ne : Icc j1 k1 ≠ Icc j2 k2 := by
        intro h_eq
        have h_pair_eq := Icc_inj_of_le h_ge1.2 h_ge2.2 h_eq
        have h_eq_final : (j1, k1) = (j2, k2) := by
          ext <;> simp [h_pair_eq]
        exact h_ne h_eq_final
      exact distinct_sum_of_distinct_Icc h_ge1.1 h_ge1.2 h_ge2.1 h_ge2.2 h_icc_ne































