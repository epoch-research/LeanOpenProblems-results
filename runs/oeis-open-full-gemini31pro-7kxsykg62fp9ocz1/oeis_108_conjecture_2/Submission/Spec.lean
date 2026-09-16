import FormalConjectures.Util.ProblemImports
import Mathlib.Combinatorics.Enumerative.Catalan

open Nat Real Finset Int

def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)
def a_rat (n : ℕ) : ℚ := (a n : ℚ)⁻¹
def catalan_reciprocal_sum (j k : ℕ) : ℚ := (Finset.Icc j k).sum a_rat
def oeis_108_index_cond (j k : ℕ) : Prop := 1 ≤ k ∧ min 2 k ≤ j ∧ j ≤ k
noncomputable def frac_part (q : ℚ) : ℝ := fract (q : ℝ)

lemma a_eq_catalan (n : ℕ) : a n = catalan n := by
  dsimp [a]
  rw [catalan_eq_centralBinom_div, centralBinom]

lemma a_recurrence (n : ℕ) : (n + 2) * a (n + 1) = (4 * n + 2) * a n := by
  have H : (n + 1) * ((n + 2) * a (n + 1)) = (n + 1) * ((4 * n + 2) * a n) := by
    have h1 : (n + 2) * catalan (n + 1) = (n + 1).centralBinom := succ_mul_catalan_eq_centralBinom (n + 1)
    have h2 : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
    have h3 := succ_mul_centralBinom_succ n
    have h4 : (n + 1) * ((n + 2) * catalan (n + 1)) = (n + 1) * (n + 1).centralBinom := by rw [h1]
    rw [h3] at h4
    have h5 : 2 * (2 * n + 1) * n.centralBinom = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [←h2]
    rw [h5] at h4
    simp_rw [a_eq_catalan]
    calc (n + 1) * ((n + 2) * catalan (n + 1))
      _ = (n + 1) * ((n + 2) * catalan (n + 1)) := by ring
      _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := h4
      _ = (n + 1) * ((4 * n + 2) * catalan n) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ n) H

lemma a_pos (n : ℕ) : 0 < a n := by
  induction' n with n ih
  · exact zero_lt_one
  · have H := a_recurrence n
    have H1 : 0 < (4 * n + 2) * a n := Nat.mul_pos (by linarith) ih
    rw [←H] at H1
    rw [mul_comm] at H1
    exact Nat.pos_of_mul_pos_right H1

lemma a_rat_pos (n : ℕ) : 0 < a_rat n := by
  dsimp [a_rat]
  have h := a_pos n
  positivity

lemma a_bound (n : ℕ) (hn : 2 ≤ n) : 5 * a n ≤ 2 * a (n + 1) := by
  have H := a_recurrence n
  have H1 : 5 * (n + 2) * a n ≤ 2 * (n + 2) * a (n + 1) := by
    calc 5 * (n + 2) * a n
      _ = (5 * n + 10) * a n := by ring
      _ ≤ (8 * n + 4) * a n := by
        apply Nat.mul_le_mul_right
        linarith
      _ = 2 * ((4 * n + 2) * a n) := by ring
      _ = 2 * ((n + 2) * a (n + 1)) := by rw [←H]
      _ = 2 * (n + 2) * a (n + 1) := by ring
  have H2 : (n + 2) * (5 * a n) ≤ (n + 2) * (2 * a (n + 1)) := by
    calc (n + 2) * (5 * a n)
      _ = 5 * (n + 2) * a n := by ring
      _ ≤ 2 * (n + 2) * a (n + 1) := H1
      _ = (n + 2) * (2 * a (n + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left H2 (by linarith)

lemma a_rat_bound (n : ℕ) (hn : 2 ≤ n) : a_rat (n + 1) ≤ (2 / 5 : ℚ) * a_rat n := by
  have h1 := a_bound n hn
  have h2 : (5 : ℚ) * (a n : ℚ) ≤ (2 : ℚ) * (a (n + 1) : ℚ) := by exact_mod_cast h1
  dsimp [a_rat]
  have hn1 : (0 : ℚ) < a n := by exact_mod_cast a_pos n
  have hn2 : (0 : ℚ) < a (n + 1) := by exact_mod_cast a_pos (n + 1)
  rw [inv_eq_one_div, inv_eq_one_div]
  have h3 : 1 / (a (n + 1) : ℚ) ≤ 2 / (5 * (a n : ℚ)) := by
    rw [div_le_div_iff₀ hn2 (by positivity)]
    linarith
  calc 1 / (a (n + 1) : ℚ)
    _ ≤ 2 / (5 * (a n : ℚ)) := h3
    _ = (2 / 5 : ℚ) * (1 / (a n : ℚ)) := by ring

lemma a_rat_two : a_rat 2 = 1 / 2 := by
  change (2 : ℚ)⁻¹ = 1 / 2
  norm_num

lemma a_rat_bound_d (j d : ℕ) (hj : 2 ≤ j) :
    a_rat (j + d) ≤ (2 / 5 : ℚ)^d * a_rat j := by
  induction' d with d ih
  · simp
  · have h1 : a_rat (j + d + 1) ≤ (2 / 5 : ℚ) * a_rat (j + d) := a_rat_bound (j + d) (by omega)
    have h2 : (2 / 5 : ℚ) * a_rat (j + d) ≤ (2 / 5 : ℚ) * ((2 / 5 : ℚ)^d * a_rat j) := by
      gcongr
    have h_eq : j + (d + 1) = j + d + 1 := by omega
    rw [h_eq]
    calc a_rat (j + d + 1)
      _ ≤ (2 / 5 : ℚ) * a_rat (j + d) := h1
      _ ≤ (2 / 5 : ℚ) * ((2 / 5 : ℚ)^d * a_rat j) := h2
      _ = (2 / 5 : ℚ)^(d + 1) * a_rat j := by ring

lemma a_rat_mono_d (j1 d : ℕ) (h1 : 2 ≤ j1) :
    a_rat (j1 + d) ≤ a_rat j1 := by
  have H := a_rat_bound_d j1 d h1
  calc a_rat (j1 + d)
    _ ≤ (2 / 5 : ℚ)^d * a_rat j1 := H
    _ ≤ 1 * a_rat j1 := by
      apply mul_le_mul_of_nonneg_right
      · have hp : (0 : ℚ) ≤ (2 / 5 : ℚ) := by positivity
        have hpow : (2 / 5 : ℚ)^d ≤ 1^d := by
          have h_le_one : (2 / 5 : ℚ) ≤ 1 := by norm_num
          have h2 : (2 / 5 : ℚ)^d ≤ 1^d := by gcongr
          exact h2
        rw [one_pow] at hpow
        exact hpow
      · exact le_of_lt (a_rat_pos j1)
    _ = a_rat j1 := by ring

lemma a_rat_mono (j1 j2 : ℕ) (h1 : 2 ≤ j1) (h12 : j1 ≤ j2) :
    a_rat j2 ≤ a_rat j1 := by
  have h_eq : j2 = j1 + (j2 - j1) := by omega
  rw [h_eq]
  exact a_rat_mono_d j1 (j2 - j1) h1

lemma sum_a_rat_bound_d (j d : ℕ) (hj : 2 ≤ j) :
    ∑ i ∈ Ico j (j + d), a_rat i ≤ (1 - (2/5:ℚ)^d) * (5 / 3 : ℚ) * a_rat j := by
  induction' d with d ih
  · simp
  · have h_eq : j + (d + 1) = j + d + 1 := by omega
    rw [h_eq, sum_Ico_succ_top (by linarith)]
    have hd : a_rat (j + d) ≤ (2 / 5 : ℚ)^d * a_rat j := a_rat_bound_d j d hj
    calc (∑ i ∈ Ico j (j + d), a_rat i) + a_rat (j + d)
      _ ≤ (1 - (2 / 5 : ℚ)^d) * (5 / 3 : ℚ) * a_rat j + a_rat (j + d) := by gcongr
      _ ≤ (1 - (2 / 5 : ℚ)^d) * (5 / 3 : ℚ) * a_rat j + (2 / 5 : ℚ)^d * a_rat j := by gcongr
      _ = (1 - (2 / 5 : ℚ)^(d + 1)) * (5 / 3 : ℚ) * a_rat j := by ring

lemma sum_a_rat_strict_bound (j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
    ∑ i ∈ Icc (j + 1) k, a_rat i < a_rat j := by
  by_cases h : j + 1 ≤ k
  · have h_eq : Icc (j + 1) k = Ico (j + 1) (j + 1 + (k - j)) := by
      ext x
      simp only [mem_Icc, mem_Ico]
      omega
    rw [h_eq]
    have h1 := sum_a_rat_bound_d (j + 1) (k - j) (by linarith)
    have h2 : a_rat (j + 1) ≤ (2 / 5 : ℚ) * a_rat j := a_rat_bound j hj
    have h_pow_pos : (0 : ℚ) ≤ (2 / 5 : ℚ)^(k - j) := by positivity
    have h_pow_le : (2 / 5 : ℚ)^(k - j) ≤ 1 := by
      have h1 : (2 / 5 : ℚ) ≤ 1 := by norm_num
      have h2 : (2 / 5 : ℚ)^(k - j) ≤ 1^(k - j) := by gcongr
      rw [one_pow] at h2
      exact h2
    have h_pos_coeff : 0 ≤ (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) := by linarith
    have h3 : (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * a_rat (j + 1) ≤ (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * ((2 / 5 : ℚ) * a_rat j) := by
      apply mul_le_mul_of_nonneg_left h2 h_pos_coeff
    have hp1 : (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * (2 / 5 : ℚ) ≤ (2 / 3 : ℚ) := by
      calc (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * (2 / 5 : ℚ)
        _ = (1 - (2 / 5 : ℚ)^(k - j)) * (2 / 3 : ℚ) := by ring
        _ ≤ 1 * (2 / 3 : ℚ) := by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · norm_num
        _ = (2 / 3 : ℚ) := by ring
    have h4 : (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * ((2 / 5 : ℚ) * a_rat j) < a_rat j := by
      have hj_pos : 0 < a_rat j := a_rat_pos j
      calc (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * ((2 / 5 : ℚ) * a_rat j)
        _ = (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * (2 / 5 : ℚ) * a_rat j := by ring
        _ ≤ (2 / 3 : ℚ) * a_rat j := by gcongr
        _ < 1 * a_rat j := by
          apply mul_lt_mul_of_pos_right
          · norm_num
          · exact hj_pos
        _ = a_rat j := by ring
    linarith
  · have h_empty : Icc (j + 1) k = ∅ := Icc_eq_empty (by linarith)
    rw [h_empty, sum_empty]
    exact a_rat_pos j

lemma sum_a_rat_lt_one (j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
    ∑ i ∈ Icc j k, a_rat i < 1 := by
  have h_eq : ∑ i ∈ Icc j k, a_rat i = a_rat j + ∑ i ∈ Icc (j + 1) k, a_rat i := by
    have h_mem : j ∈ Icc j k := by
      rw [mem_Icc]
      omega
    rw [sum_eq_add_sum_diff_singleton h_mem]
    have h_eq2 : Icc j k \ {j} = Icc (j + 1) k := by
      ext x
      simp only [mem_sdiff, mem_Icc, mem_singleton]
      omega
    rw [h_eq2]
  have h_lt : ∑ i ∈ Icc (j + 1) k, a_rat i < a_rat j := sum_a_rat_strict_bound j k hj hjk
  have h_a2 : a_rat j ≤ a_rat 2 := a_rat_mono 2 j (by linarith) hj
  have h_a2_val : a_rat 2 = 1 / 2 := a_rat_two
  rw [h_eq]
  linarith

lemma sum_a_rat_pos (j k : ℕ) (hjk : j ≤ k) :
    0 < ∑ i ∈ Icc j k, a_rat i := by
  apply sum_pos
  · intro i _
    exact a_rat_pos i
  · rw [nonempty_Icc]
    omega

lemma sum_a_rat_lt_of_lt (j1 k1 j2 k2 : ℕ) (h1 : 2 ≤ j1) (h1k : j1 ≤ k1) (h2 : 2 ≤ j2) (h2k : j2 ≤ k2) (hj : j1 < j2) :
    ∑ i ∈ Icc j2 k2, a_rat i < ∑ i ∈ Icc j1 k1, a_rat i := by
  have h_le : ∑ i ∈ Icc j2 k2, a_rat i ≤ ∑ i ∈ Icc (j1 + 1) k2, a_rat i := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      rw [mem_Icc] at hx ⊢
      omega
    · intro i _ _
      exact le_of_lt (a_rat_pos i)
  have h_lt : ∑ i ∈ Icc (j1 + 1) k2, a_rat i < a_rat j1 := sum_a_rat_strict_bound j1 k2 h1 (by omega)
  have h_le2 : a_rat j1 ≤ ∑ i ∈ Icc j1 k1, a_rat i := by
    have h_mem : j1 ∈ Icc j1 k1 := by
      rw [mem_Icc]
      omega
    rw [sum_eq_add_sum_diff_singleton h_mem]
    have h_nonneg : 0 ≤ ∑ x ∈ Icc j1 k1 \ {j1}, a_rat x := by
      apply sum_nonneg
      intro i _
      exact le_of_lt (a_rat_pos i)
    linarith
  linarith

lemma sum_a_rat_lt_of_eq_of_lt (j k1 k2 : ℕ) (h1 : 2 ≤ j) (h1k : j ≤ k1) (h2k : j ≤ k2) (hk : k1 < k2) :
    ∑ i ∈ Icc j k1, a_rat i < ∑ i ∈ Icc j k2, a_rat i := by
  have h_eq : Icc j k2 = Icc j k1 ∪ Icc (k1 + 1) k2 := by
    ext x
    simp only [mem_Icc, mem_union]
    omega
  rw [h_eq, sum_union]
  · have h_pos : 0 < ∑ i ∈ Icc (k1 + 1) k2, a_rat i := by
      apply sum_pos
      · intro i _
        exact a_rat_pos i
      · rw [nonempty_Icc]
        omega
    linarith
  · rw [disjoint_left]
    intro x hx
    simp only [mem_Icc] at hx ⊢
    omega

lemma frac_part_eq_of_mem_Ioo (q : ℚ) (hq1 : 0 < q) (hq2 : q < 1) :
    frac_part q = (q : ℝ) := by
  dsimp [frac_part]
  apply Int.fract_eq_self.mpr
  constructor
  · exact_mod_cast le_of_lt hq1
  · exact_mod_cast hq2

lemma frac_part_eq_zero_of_one : frac_part (1 : ℚ) = 0 := by
  dsimp [frac_part]
  have h_one : ((1 : ℚ) : ℝ) = 1 := by norm_cast
  rw [h_one]
  exact Int.fract_one

lemma cond_implies (j k : ℕ) (h : oeis_108_index_cond j k) :
    (j = 1 ∧ k = 1) ∨ (2 ≤ j ∧ j ≤ k) := by
  dsimp [oeis_108_index_cond] at h
  rcases h with ⟨h1, h2, h3⟩
  by_cases hk : k = 1
  · left
    rw [hk] at h2 h3 ⊢
    revert h2
    simp
    intro hj
    omega
  · right
    have hk2 : 2 ≤ k := by omega
    have h_min : min 2 k = 2 := by
      exact min_eq_left hk2
    rw [h_min] at h2
    exact ⟨h2, h3⟩

lemma catalan_reciprocal_sum_one_one : catalan_reciprocal_sum 1 1 = 1 := by
  dsimp [catalan_reciprocal_sum]
  have h : Icc 1 1 = {1} := Icc_self 1
  rw [h, sum_singleton]
  dsimp [a_rat, a]
  norm_num

theorem oeis_108_conjecture_2 :
  ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄,
     oeis_108_index_cond j₁ k₁ →
     oeis_108_index_cond j₂ k₂ →
     (j₁, k₁) ≠ (j₂, k₂) →
     frac_part (catalan_reciprocal_sum j₁ k₁) ≠ frac_part (catalan_reciprocal_sum j₂ k₂) := by
  intro j1 k1 j2 k2 h1 h2 hne
  have hc1 := cond_implies j1 k1 h1
  have hc2 := cond_implies j2 k2 h2
  rcases hc1 with (⟨hj1_1, hk1_1⟩ | ⟨hj1_2, hjk1⟩)
  · rcases hc2 with (⟨hj2_1, hk2_1⟩ | ⟨hj2_2, hjk2⟩)
    · exfalso
      apply hne
      ext
      · rw [hj1_1, hj2_1]
      · rw [hk1_1, hk2_1]
    · rw [hj1_1, hk1_1, catalan_reciprocal_sum_one_one, frac_part_eq_zero_of_one]
      have H1 : 0 < catalan_reciprocal_sum j2 k2 := sum_a_rat_pos j2 k2 hjk2
      have H2 : catalan_reciprocal_sum j2 k2 < 1 := sum_a_rat_lt_one j2 k2 hj2_2 hjk2
      rw [frac_part_eq_of_mem_Ioo _ H1 H2]
      intro h_eq
      have h_eq_rat : (catalan_reciprocal_sum j2 k2 : ℝ) = 0 := by
        exact h_eq.symm
      have h_zero : (catalan_reciprocal_sum j2 k2 : ℝ) > 0 := by exact_mod_cast H1
      linarith
  · rcases hc2 with (⟨hj2_1, hk2_1⟩ | ⟨hj2_2, hjk2⟩)
    · rw [hj2_1, hk2_1, catalan_reciprocal_sum_one_one, frac_part_eq_zero_of_one]
      have H1 : 0 < catalan_reciprocal_sum j1 k1 := sum_a_rat_pos j1 k1 hjk1
      have H2 : catalan_reciprocal_sum j1 k1 < 1 := sum_a_rat_lt_one j1 k1 hj1_2 hjk1
      rw [frac_part_eq_of_mem_Ioo _ H1 H2]
      intro h_eq
      have h_eq_rat : (catalan_reciprocal_sum j1 k1 : ℝ) = 0 := by
        exact h_eq
      have h_zero : (catalan_reciprocal_sum j1 k1 : ℝ) > 0 := by exact_mod_cast H1
      linarith
    · have H1_1 : 0 < catalan_reciprocal_sum j1 k1 := sum_a_rat_pos j1 k1 hjk1
      have H1_2 : catalan_reciprocal_sum j1 k1 < 1 := sum_a_rat_lt_one j1 k1 hj1_2 hjk1
      have H2_1 : 0 < catalan_reciprocal_sum j2 k2 := sum_a_rat_pos j2 k2 hjk2
      have H2_2 : catalan_reciprocal_sum j2 k2 < 1 := sum_a_rat_lt_one j2 k2 hj2_2 hjk2
      rw [frac_part_eq_of_mem_Ioo _ H1_1 H1_2, frac_part_eq_of_mem_Ioo _ H2_1 H2_2]
      intro h_eq
      have h_eq_rat : catalan_reciprocal_sum j1 k1 = catalan_reciprocal_sum j2 k2 := by
        exact_mod_cast h_eq
      rcases lt_trichotomy j1 j2 with hlt1 | heq | hlt2
      · have h_lt : catalan_reciprocal_sum j2 k2 < catalan_reciprocal_sum j1 k1 := sum_a_rat_lt_of_lt j1 k1 j2 k2 hj1_2 hjk1 hj2_2 hjk2 hlt1
        linarith
      · rcases lt_trichotomy k1 k2 with hlt3 | heq2 | hlt4
        · have h_lt : catalan_reciprocal_sum j1 k1 < catalan_reciprocal_sum j1 k2 := sum_a_rat_lt_of_eq_of_lt j1 k1 k2 hj1_2 hjk1 (by omega) hlt3
          have h_sum_eq : catalan_reciprocal_sum j1 k2 = catalan_reciprocal_sum j2 k2 := by rw [heq]
          linarith
        · have hne2 : (j1, k1) = (j2, k2) := by ext; exact heq; exact heq2
          exact hne hne2
        · have h_lt : catalan_reciprocal_sum j2 k2 < catalan_reciprocal_sum j2 k1 := sum_a_rat_lt_of_eq_of_lt j2 k2 k1 hj2_2 hjk2 (by omega) hlt4
          have h_sum_eq : catalan_reciprocal_sum j1 k1 = catalan_reciprocal_sum j2 k1 := by rw [heq]
          linarith
      · have h_lt : catalan_reciprocal_sum j1 k1 < catalan_reciprocal_sum j2 k2 := sum_a_rat_lt_of_lt j2 k2 j1 k1 hj2_2 hjk2 hj1_2 hjk1 hlt2
        linarith

theorem oeis_108_conjecture_2.disproof : ¬ (type_of% @oeis_108_conjecture_2) := sorry
