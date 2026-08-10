import FormalConjectures.Util.ProblemImports

open Nat Real Finset

/--
A000108 Catalan numbers: C(n) = binomial(2n,n)/(n+1).
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) / (n + 1)

-- Reciprocal of the n-th Catalan number as a rational number.
def a_rat (n : ℕ) : ℚ := (a n : ℚ)⁻¹

/-- The sum $\sum_{i=j}^k \frac{1}{a(i)}$ of reciprocals of Catalan numbers. -/
def catalan_reciprocal_sum (j k : ℕ) : ℚ :=
  (Finset.Icc j k).sum a_rat

/-- The index condition on $(j, k)$ from the conjecture: $0 < \min\{2,k\} \le j \le k$.
Since j and k are natural numbers, $0 < \min\{2,k\}$ is equivalent to $1 \le k$. -/
def oeis_108_index_cond (j k : ℕ) : Prop :=
  1 ≤ k ∧ min 2 k ≤ j ∧ j ≤ k

open Int (fract)

/-- The fractional part of a rational number, viewed as a real number. Must be noncomputable
due to dependence on the real floor function. -/
noncomputable def frac_part (q : ℚ) : ℝ := fract (q : ℝ)

lemma a_eq_catalan (n : ℕ) : a n = catalan n := by
  simp [a, catalan_eq_centralBinom_div, Nat.centralBinom]

lemma a_pos (n : ℕ) : 0 < a n := by
  rw [a_eq_catalan]
  by_contra h
  have hz : catalan n = 0 := Nat.eq_zero_of_not_pos h
  have hc := succ_mul_catalan_eq_centralBinom n
  rw [hz, mul_zero] at hc
  exact Nat.centralBinom_pos n |>.ne' hc.symm

lemma a_rat_pos (n : ℕ) : 0 < a_rat n := by
  simp [a_rat, a_pos n]

lemma catalan_rat_succ (n : ℕ) :
    (catalan (n+1) : ℚ) = (2 * (2 * (n:ℚ) + 1) / ((n:ℚ) + 2)) * (catalan n : ℚ) := by
  have h1 : (((n + 2 : ℕ) : ℚ) * (catalan (n+1) : ℚ) = (Nat.centralBinom (n+1) : ℚ)) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom (n+1)
  have h2 : (((n + 1 : ℕ) : ℚ) * (Nat.centralBinom (n+1) : ℚ) =
      2 * (2 * (n:ℚ) + 1) * (Nat.centralBinom n : ℚ)) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have h3 : (((n + 1 : ℕ) : ℚ) * (catalan n : ℚ) = (Nat.centralBinom n : ℚ)) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have hn1 : ((n:ℚ) + 1) ≠ 0 := by positivity
  have hn2 : ((n:ℚ) + 2) ≠ 0 := by positivity
  rw [← h1, ← h3] at h2
  field_simp [show ((n + 1 : ℕ) : ℚ) = (n:ℚ) + 1 by norm_num,
    show ((n + 2 : ℕ) : ℚ) = (n:ℚ) + 2 by norm_num] at h2 ⊢
  convert h2 using 1; norm_num; ring_nf

lemma ratio_test (n : ℕ) (hn : 2 ≤ n) : a_rat (n+1) ≤ (2/5 : ℚ) * a_rat n := by
  rw [a_rat, a_rat]
  rw [a_eq_catalan n, a_eq_catalan (n+1)]
  have hrec := catalan_rat_succ n
  have hposn : (0:ℚ) < (catalan n : ℚ) := by
    exact_mod_cast (by rw [← a_eq_catalan n]; exact a_pos n)
  have hposns : (0:ℚ) < (catalan (n+1) : ℚ) := by
    exact_mod_cast (by rw [← a_eq_catalan (n+1)]; exact a_pos (n+1))
  rw [hrec]
  set coef : ℚ := 2 * (2 * (n:ℚ) + 1) / ((n:ℚ) + 2)
  have hcoef_pos : 0 < coef := by
    dsimp [coef]
    positivity
  have hcoef_inv_le : coef⁻¹ ≤ (2/5 : ℚ) := by
    dsimp [coef]
    have hn2 : ((n:ℚ) + 2) ≠ 0 := by positivity
    have hden : 2 * (2 * (n:ℚ) + 1) ≠ 0 := by positivity
    field_simp [hn2, hden]
    have hnq : (2:ℚ) ≤ n := by exact_mod_cast hn
    linarith
  rw [mul_inv_rev]
  rw [mul_comm ((catalan n : ℚ)⁻¹) (coef⁻¹)]
  exact mul_le_mul_of_nonneg_right hcoef_inv_le (le_of_lt (inv_pos.mpr hposn))

lemma ratio_third (n : ℕ) (hn : 4 ≤ n) : a_rat (n+1) ≤ (1/3 : ℚ) * a_rat n := by
  rw [a_rat, a_rat]
  rw [a_eq_catalan n, a_eq_catalan (n+1)]
  have hrec := catalan_rat_succ n
  have hposn : (0:ℚ) < (catalan n : ℚ) := by
    exact_mod_cast (by rw [← a_eq_catalan n]; exact a_pos n)
  rw [hrec]
  set coef : ℚ := 2 * (2 * (n:ℚ) + 1) / ((n:ℚ) + 2)
  have hcoef_inv_le : coef⁻¹ ≤ (1/3 : ℚ) := by
    dsimp [coef]
    have hn2 : ((n:ℚ) + 2) ≠ 0 := by positivity
    have hden : 2 * (2 * (n:ℚ) + 1) ≠ 0 := by positivity
    field_simp [hn2, hden]
    have hnq : (4:ℚ) ≤ n := by exact_mod_cast hn
    linarith
  rw [mul_inv_rev]
  rw [mul_comm ((catalan n : ℚ)⁻¹) (coef⁻¹)]
  exact mul_le_mul_of_nonneg_right hcoef_inv_le (le_of_lt (inv_pos.mpr hposn))

lemma tail_half_range (n d : ℕ) (hn : 4 ≤ n) :
    (Finset.range (d+1)).sum (fun r => a_rat (n+1+r)) ≤ (1/2 : ℚ) * a_rat n := by
  induction d generalizing n with
  | zero =>
      simp
      calc
        a_rat (n + 1) ≤ (1/3 : ℚ) * a_rat n := ratio_third n hn
        _ ≤ (1/2 : ℚ) * a_rat n := by
          exact mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt (a_rat_pos n))
        _ = (2:ℚ)⁻¹ * a_rat n := by norm_num
  | succ d ih =>
      rw [Finset.sum_range_succ']
      have htail := ih (n+1) (by omega)
      have hratio := ratio_third n hn
      rw [add_comm]
      calc
        a_rat (n + 1 + 0) + (Finset.range (d + 1)).sum (fun i => a_rat (n + 1 + (i + 1)))
            = a_rat (n+1) + (Finset.range (d+1)).sum (fun r => a_rat ((n+1)+1+r)) := by
                congr 1
                apply Finset.sum_congr rfl
                intro r hr
                congr 1
                omega
        _ ≤ a_rat (n+1) + (1/2 : ℚ) * a_rat (n+1) := by
                exact add_le_add (le_refl _) htail
        _ = (3/2 : ℚ) * a_rat (n+1) := by ring
        _ ≤ (3/2 : ℚ) * ((1/3 : ℚ) * a_rat n) := by
                exact mul_le_mul_of_nonneg_left hratio (by norm_num)
        _ = (1/2 : ℚ) * a_rat n := by ring

lemma tail_Icc_half (n k : ℕ) (hn : 4 ≤ n) :
    (Finset.Icc (n+1) k).sum a_rat ≤ (1/2 : ℚ) * a_rat n := by
  by_cases hk : n < k
  · have hk' : n + 1 ≤ k := Nat.succ_le_iff.mpr hk
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : k + 1 - (n + 1) = (k - (n + 1)) + 1 := by omega
    rw [hlen]
    simpa [add_assoc] using tail_half_range n (k - (n+1)) hn
  · have hempty : Finset.Icc (n+1) k = ∅ := Finset.Icc_eq_empty (by omega)
    simp [hempty, le_of_lt (a_rat_pos n)]

@[simp] lemma a_rat_one : a_rat 1 = 1 := by
  norm_num [a_rat, a]

@[simp] lemma a_rat_two : a_rat 2 = (1/2 : ℚ) := by
  rw [a_rat, show a 2 = 2 by rw [a_eq_catalan, catalan_two]]
  norm_num

@[simp] lemma a_rat_three : a_rat 3 = (1/5 : ℚ) := by
  rw [a_rat, show a 3 = 5 by rw [a_eq_catalan, catalan_three]]
  norm_num

@[simp] lemma a_rat_four : a_rat 4 = (1/14 : ℚ) := by
  rw [a_rat, show a 4 = 14 by
    rw [a_eq_catalan, catalan_eq_centralBinom_div]
    norm_num [Nat.centralBinom, Nat.choose]]
  norm_num

lemma Icc_succ_sum_le (m k : ℕ) :
    (Finset.Icc m k).sum a_rat ≤ a_rat m + (Finset.Icc (m+1) k).sum a_rat := by
  by_cases hk : m ≤ k
  · rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [← Finset.Ico_add_one_right_eq_Icc (a:=m+1) (b:=k)]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : k + 1 - m = (k + 1 - (m + 1)) + 1 := by omega
    rw [hlen, Finset.sum_range_succ']
    simp [add_comm, add_left_comm]
  · have hempty : Finset.Icc m k = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp
    have hsum : 0 ≤ (Finset.Icc (m+1) k).sum a_rat := by
      exact Finset.sum_nonneg (fun i hi => le_of_lt (a_rat_pos i))
    have hm : 0 < a_rat m := a_rat_pos m
    nlinarith


lemma tail_Icc_lt_self (n k : ℕ) (hn : 1 ≤ n) :
    (Finset.Icc (n+1) k).sum a_rat < a_rat n := by
  rcases lt_or_ge n 4 with hn4lt | hn4
  · interval_cases n
    · have h2 : (Finset.Icc 2 k).sum a_rat ≤ a_rat 2 + (Finset.Icc 3 k).sum a_rat := Icc_succ_sum_le 2 k
      have h3 : (Finset.Icc 3 k).sum a_rat ≤ a_rat 3 + (Finset.Icc 4 k).sum a_rat := Icc_succ_sum_le 3 k
      have h4 : (Finset.Icc 4 k).sum a_rat ≤ a_rat 4 + (Finset.Icc 5 k).sum a_rat := Icc_succ_sum_le 4 k
      have h5 := tail_Icc_half 4 k (by norm_num)
      norm_num at h2 h3 h4 h5 ⊢
      linarith
    · have h3 : (Finset.Icc 3 k).sum a_rat ≤ a_rat 3 + (Finset.Icc 4 k).sum a_rat := Icc_succ_sum_le 3 k
      have h4 : (Finset.Icc 4 k).sum a_rat ≤ a_rat 4 + (Finset.Icc 5 k).sum a_rat := Icc_succ_sum_le 4 k
      have h5 := tail_Icc_half 4 k (by norm_num)
      norm_num at h3 h4 h5 ⊢
      linarith
    · have h4 : (Finset.Icc 4 k).sum a_rat ≤ a_rat 4 + (Finset.Icc 5 k).sum a_rat := Icc_succ_sum_le 4 k
      have h5 := tail_Icc_half 4 k (by norm_num)
      norm_num at h4 h5 ⊢
      linarith
  · have hle : (Finset.Icc (n+1) k).sum a_rat ≤ (1/2 : ℚ) * a_rat n := tail_Icc_half n k hn4
    have hpos := a_rat_pos n
    nlinarith

lemma interval_sum_pos {j k : ℕ} (hjk : j ≤ k) :
    0 < catalan_reciprocal_sum j k := by
  dsimp [catalan_reciprocal_sum]
  exact Finset.sum_pos (fun i hi => a_rat_pos i) ⟨j, by simp [hjk]⟩

lemma interval_sum_lt_of_start_lt {j₁ k₁ j₂ k₂ : ℕ}
    (hj₁pos : 1 ≤ j₁) (hj₁k₁ : j₁ ≤ k₁) (hjlt : j₁ < j₂) :
    catalan_reciprocal_sum j₂ k₂ < catalan_reciprocal_sum j₁ k₁ := by
  have htail : (Finset.Icc (j₁+1) k₂).sum a_rat < a_rat j₁ := tail_Icc_lt_self j₁ k₂ hj₁pos
  have hsub : Finset.Icc j₂ k₂ ⊆ Finset.Icc (j₁+1) k₂ := by
    intro x hx
    have hx' := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega, hx'.2⟩
  have hright : catalan_reciprocal_sum j₂ k₂ ≤ (Finset.Icc (j₁+1) k₂).sum a_rat := by
    dsimp [catalan_reciprocal_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi hnot => le_of_lt (a_rat_pos i))
  have hsing : ({j₁} : Finset ℕ) ⊆ Finset.Icc j₁ k₁ := by
    intro x hx
    simp at hx
    subst x
    simp [hj₁k₁]
  have hleft : a_rat j₁ ≤ catalan_reciprocal_sum j₁ k₁ := by
    dsimp [catalan_reciprocal_sum]
    simpa using (Finset.sum_le_sum_of_subset_of_nonneg hsing (fun i hi hnot => le_of_lt (a_rat_pos i)))
  linarith

lemma interval_sum_lt_of_same_start_k_lt {j k₁ k₂ : ℕ} (hjk₁ : j ≤ k₁) (hklt : k₁ < k₂) :
    catalan_reciprocal_sum j k₁ < catalan_reciprocal_sum j k₂ := by
  have hsub : Finset.Icc j k₁ ⊆ Finset.Icc j k₂ := by
    intro x hx
    have hx' := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨hx'.1, by omega⟩
  dsimp [catalan_reciprocal_sum]
  apply Finset.sum_lt_sum_of_subset hsub (i := k₁+1)
  · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro hmem
    have hm := (Finset.mem_Icc.mp hmem).2
    omega
  · exact a_rat_pos (k₁+1)
  · intro i hi hnot
    exact le_of_lt (a_rat_pos i)

lemma interval_sum_ne_of_ne {j₁ k₁ j₂ k₂ : ℕ}
    (hj₁pos : 1 ≤ j₁) (hj₂pos : 1 ≤ j₂) (hj₁k₁ : j₁ ≤ k₁) (hj₂k₂ : j₂ ≤ k₂)
    (hne : (j₁,k₁) ≠ (j₂,k₂)) :
    catalan_reciprocal_sum j₁ k₁ ≠ catalan_reciprocal_sum j₂ k₂ := by
  intro heq
  rcases lt_trichotomy j₁ j₂ with hlt | heqj | hgt
  · have hltSum := interval_sum_lt_of_start_lt (k₂:=k₂) hj₁pos hj₁k₁ hlt
    linarith
  · subst j₂
    have hkne : k₁ ≠ k₂ := by
      intro hk
      apply hne
      simp [hk]
    rcases lt_trichotomy k₁ k₂ with hklt | hkeq | hkgt
    · have hstrict := interval_sum_lt_of_same_start_k_lt (j:=j₁) hj₁k₁ hklt
      linarith
    · exact (hkne hkeq).elim
    · have hstrict := interval_sum_lt_of_same_start_k_lt (j:=j₁) hj₂k₂ hkgt
      linarith
  · have hltSum := interval_sum_lt_of_start_lt (k₂:=k₁) hj₂pos hj₂k₂ hgt
    linarith

lemma index_cond_j_pos {j k : ℕ} (h : oeis_108_index_cond j k) : 1 ≤ j := by
  have hm : 1 ≤ min 2 k := Nat.le_min.mpr ⟨by norm_num, h.1⟩
  exact le_trans hm h.2.1

lemma index_cond_not_one_j_ge_two {j k : ℕ} (h : oeis_108_index_cond j k) (hne : (j,k) ≠ (1,1)) : 2 ≤ j := by
  by_contra hj
  have hj1 : j = 1 := by
    have hjpos := index_cond_j_pos h
    omega
  have hminle : min 2 k ≤ 1 := by simpa [hj1] using h.2.1
  have hk1 : k = 1 := by
    rcases k with _ | k
    · have hkpos : 1 ≤ 0 := h.1
      omega
    · cases k with
      | zero => rfl
      | succ k =>
          simp at hminle
  exact hne (by simp [hj1, hk1])

lemma catalan_sum_one_one : catalan_reciprocal_sum 1 1 = 1 := by
  simp [catalan_reciprocal_sum]

lemma catalan_sum_lt_one_of_not_one {j k : ℕ} (h : oeis_108_index_cond j k) (hne : (j,k) ≠ (1,1)) :
    catalan_reciprocal_sum j k < 1 := by
  have hj2 : 2 ≤ j := index_cond_not_one_j_ge_two h hne
  have htail := tail_Icc_lt_self 1 k (by norm_num)
  have hsub : Finset.Icc j k ⊆ Finset.Icc 2 k := by
    intro x hx
    have hx' := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega, hx'.2⟩
  have hle : catalan_reciprocal_sum j k ≤ (Finset.Icc 2 k).sum a_rat := by
    dsimp [catalan_reciprocal_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi hnot => le_of_lt (a_rat_pos i))
  simpa using lt_of_le_of_lt hle htail

lemma frac_part_eq_self_of_bounds {q : ℚ} (h0 : 0 ≤ q) (h1 : q < 1) :
    frac_part q = (q : ℝ) := by
  unfold frac_part
  rw [Int.fract_eq_self]
  constructor
  · exact_mod_cast h0
  · exact_mod_cast h1

lemma frac_part_one : frac_part 1 = 0 := by
  unfold frac_part
  exact Int.fract_eq_zero_iff.mpr ⟨(1:ℤ), by norm_num⟩


/--
A000108 Conjecture: All the rational numbers $\sum_{i=j..k} 1/a(i)$ with $0 < \min\{2,k\} \le j \le k$ have pairwise distinct fractional parts. - _Zhi-Wei Sun_, Sep 24 2015
-/
theorem oeis_108_conjecture_2 :
  ∀ ⦃j₁ k₁ j₂ k₂ : ℕ⦄,
     oeis_108_index_cond j₁ k₁ →
     oeis_108_index_cond j₂ k₂ →
     (j₁, k₁) ≠ (j₂, k₂) →
     frac_part (catalan_reciprocal_sum j₁ k₁) ≠ frac_part (catalan_reciprocal_sum j₂ k₂)
  := by
  intro j₁ k₁ j₂ k₂ h1 h2 hne
  have hj₁pos : 1 ≤ j₁ := index_cond_j_pos h1
  have hj₂pos : 1 ≤ j₂ := index_cond_j_pos h2
  have hsumne : catalan_reciprocal_sum j₁ k₁ ≠ catalan_reciprocal_sum j₂ k₂ :=
    interval_sum_ne_of_ne hj₁pos hj₂pos h1.2.2 h2.2.2 hne
  by_cases hp1 : (j₁,k₁) = (1,1)
  · have hp2 : (j₂,k₂) ≠ (1,1) := by
      intro hp2
      exact hne (hp1.trans hp2.symm)
    have hq1 : catalan_reciprocal_sum j₁ k₁ = 1 := by
      rcases Prod.ext_iff.mp hp1 with ⟨rfl, rfl⟩
      exact catalan_sum_one_one
    have hpos2 : 0 < catalan_reciprocal_sum j₂ k₂ := interval_sum_pos h2.2.2
    have hlt2 : catalan_reciprocal_sum j₂ k₂ < 1 := catalan_sum_lt_one_of_not_one h2 hp2
    have hf1 : frac_part (catalan_reciprocal_sum j₁ k₁) = 0 := by simpa [hq1] using frac_part_one
    have hf2 : frac_part (catalan_reciprocal_sum j₂ k₂) = (catalan_reciprocal_sum j₂ k₂ : ℝ) :=
      frac_part_eq_self_of_bounds (le_of_lt hpos2) hlt2
    intro heq
    rw [hf1, hf2] at heq
    have hpos2r : (0:ℝ) < (catalan_reciprocal_sum j₂ k₂ : ℝ) := by exact_mod_cast hpos2
    linarith
  · by_cases hp2 : (j₂,k₂) = (1,1)
    · have hq2 : catalan_reciprocal_sum j₂ k₂ = 1 := by
        rcases Prod.ext_iff.mp hp2 with ⟨rfl, rfl⟩
        exact catalan_sum_one_one
      have hpos1 : 0 < catalan_reciprocal_sum j₁ k₁ := interval_sum_pos h1.2.2
      have hlt1 : catalan_reciprocal_sum j₁ k₁ < 1 := catalan_sum_lt_one_of_not_one h1 hp1
      have hf2 : frac_part (catalan_reciprocal_sum j₂ k₂) = 0 := by simpa [hq2] using frac_part_one
      have hf1 : frac_part (catalan_reciprocal_sum j₁ k₁) = (catalan_reciprocal_sum j₁ k₁ : ℝ) :=
        frac_part_eq_self_of_bounds (le_of_lt hpos1) hlt1
      intro heq
      rw [hf1, hf2] at heq
      have hpos1r : (0:ℝ) < (catalan_reciprocal_sum j₁ k₁ : ℝ) := by exact_mod_cast hpos1
      linarith
    · have hpos1 : 0 < catalan_reciprocal_sum j₁ k₁ := interval_sum_pos h1.2.2
      have hpos2 : 0 < catalan_reciprocal_sum j₂ k₂ := interval_sum_pos h2.2.2
      have hlt1 : catalan_reciprocal_sum j₁ k₁ < 1 := catalan_sum_lt_one_of_not_one h1 hp1
      have hlt2 : catalan_reciprocal_sum j₂ k₂ < 1 := catalan_sum_lt_one_of_not_one h2 hp2
      have hf1 : frac_part (catalan_reciprocal_sum j₁ k₁) = (catalan_reciprocal_sum j₁ k₁ : ℝ) :=
        frac_part_eq_self_of_bounds (le_of_lt hpos1) hlt1
      have hf2 : frac_part (catalan_reciprocal_sum j₂ k₂) = (catalan_reciprocal_sum j₂ k₂ : ℝ) :=
        frac_part_eq_self_of_bounds (le_of_lt hpos2) hlt2
      intro heq
      rw [hf1, hf2] at heq
      exact hsumne (Rat.cast_inj.mp heq)
