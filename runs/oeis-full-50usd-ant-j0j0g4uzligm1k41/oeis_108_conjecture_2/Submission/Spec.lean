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

/-! ### Basic facts about the Catalan numbers `a` -/

lemma a_eq_catalan (n : ℕ) : a n = catalan n := by
  unfold a
  rw [catalan_eq_centralBinom_div]
  rfl

lemma a_pos (n : ℕ) : 0 < a n := by
  rw [a_eq_catalan]
  have h : (n + 1) * catalan n = Nat.centralBinom n := succ_mul_catalan_eq_centralBinom n
  have hp : 0 < (n + 1) * catalan n := h ▸ Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | h0
  · rw [h0, mul_zero] at hp; exact absurd hp (lt_irrefl 0)
  · exact h0

lemma a_one : a 1 = 1 := by rw [a_eq_catalan, catalan_one]

lemma a_two : a 2 = 2 := by rw [a_eq_catalan, catalan_two]

/-- The multiplicative recurrence for Catalan numbers. -/
lemma a_rec (n : ℕ) : (n + 2) * a (n + 1) = 2 * (2 * n + 1) * a n := by
  rw [a_eq_catalan, a_eq_catalan]
  have h1 : (n + 2) * catalan (n + 1) = Nat.centralBinom (n + 1) :=
    succ_mul_catalan_eq_centralBinom (n + 1)
  have h2 : (n + 1) * catalan n = Nat.centralBinom n := succ_mul_catalan_eq_centralBinom n
  have h3 : (n + 1) * Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * Nat.centralBinom n :=
    Nat.succ_mul_centralBinom_succ n
  apply Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega)
  calc (n + 1) * ((n + 2) * catalan (n + 1))
        = (n + 1) * Nat.centralBinom (n + 1) := by rw [h1]
    _ = 2 * (2 * n + 1) * Nat.centralBinom n := h3
    _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := by rw [h2]
    _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring

/-- For `m ≥ 2`, we have `5 * a m ≤ 2 * a (m+1)`. -/
lemma a_two_mul_ge (m : ℕ) (hm : 2 ≤ m) : 5 * a m ≤ 2 * a (m + 1) := by
  have hrec := a_rec m
  apply Nat.le_of_mul_le_mul_left _ (show 0 < m + 2 by omega)
  have e : (m + 2) * (2 * a (m + 1)) = 4 * (2 * m + 1) * a m := by
    rw [show (m + 2) * (2 * a (m + 1)) = 2 * ((m + 2) * a (m + 1)) by ring, hrec]; ring
  rw [e]
  calc (m + 2) * (5 * a m) = (m + 2) * 5 * a m := by ring
    _ ≤ 4 * (2 * m + 1) * a m := Nat.mul_le_mul_right _ (by omega)

lemma a_mono_step (m : ℕ) (hm : 2 ≤ m) : a m ≤ a (m + 1) := by
  have h := a_two_mul_ge m hm
  omega

lemma a_ge_two (j : ℕ) (hj : 2 ≤ j) : 2 ≤ a j := by
  induction j with
  | zero => omega
  | succ n ih =>
    by_cases hn : 2 ≤ n
    · have h1 := ih hn
      have h2 := a_mono_step n hn
      omega
    · have : n = 1 := by omega
      subst this
      rw [a_two]

/-! ### Facts about the reciprocals `a_rat` -/

lemma a_rat_pos (n : ℕ) : 0 < a_rat n := by
  rw [a_rat]
  have : (0 : ℚ) < (a n : ℚ) := by exact_mod_cast a_pos n
  exact inv_pos.mpr this

lemma a_rat_step (m : ℕ) (hm : 2 ≤ m) : a_rat (m + 1) ≤ (2 / 5) * a_rat m := by
  have h := a_two_mul_ge m hm
  have hq : (5 : ℚ) * (a m : ℚ) ≤ 2 * (a (m + 1) : ℚ) := by exact_mod_cast h
  have hpos_m : (0 : ℚ) < (a m : ℚ) := by exact_mod_cast a_pos m
  have hpos_m1 : (0 : ℚ) < (a (m + 1) : ℚ) := by exact_mod_cast a_pos (m + 1)
  have hne_m : (a m : ℚ) ≠ 0 := hpos_m.ne'
  have hne_m1 : (a (m + 1) : ℚ) ≠ 0 := hpos_m1.ne'
  rw [a_rat, a_rat, ← sub_nonneg]
  have key : (2 / 5) * (a m : ℚ)⁻¹ - (a (m + 1) : ℚ)⁻¹
      = (2 * (a (m + 1) : ℚ) - 5 * (a m : ℚ)) / (5 * (a m : ℚ) * (a (m + 1) : ℚ)) := by
    field_simp
  rw [key]
  apply div_nonneg
  · linarith
  · positivity

lemma a_rat_le_half (j : ℕ) (hj : 2 ≤ j) : a_rat j ≤ 1 / 2 := by
  have h := a_ge_two j hj
  have hq : (2 : ℚ) ≤ (a j : ℚ) := by exact_mod_cast h
  have hpos : (0 : ℚ) < (a j : ℚ) := by exact_mod_cast a_pos j
  have hne : (a j : ℚ) ≠ 0 := hpos.ne'
  rw [a_rat, ← sub_nonneg]
  have key : (1 : ℚ) / 2 - (a j : ℚ)⁻¹ = ((a j : ℚ) - 2) / (2 * (a j : ℚ)) := by
    field_simp
  rw [key]
  apply div_nonneg
  · linarith
  · positivity

/-! ### The tail bound -/

/-- Key bound: the sum of reciprocals from `m` to `m+d` is at most `(5/3) · a_rat m`. -/
lemma tail_bound (d : ℕ) : ∀ m : ℕ, 2 ≤ m →
    (Finset.Icc m (m + d)).sum a_rat ≤ (5 / 3) * a_rat m := by
  induction d with
  | zero =>
    intro m hm
    have hp := a_rat_pos m
    simp only [Nat.add_zero, Finset.Icc_self, Finset.sum_singleton]
    linarith
  | succ d ih =>
    intro m hm
    have key : Finset.Icc m (m + (d + 1)) = insert m (Finset.Icc (m + 1) (m + (d + 1))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : m ∉ Finset.Icc (m + 1) (m + (d + 1)) := by simp [Finset.mem_Icc]
    rw [key, Finset.sum_insert hnot]
    have ihm := ih (m + 1) (by omega)
    have hbound : (Finset.Icc (m + 1) (m + (d + 1))).sum a_rat ≤ (5 / 3) * a_rat (m + 1) := by
      have he : m + (d + 1) = (m + 1) + d := by omega
      rw [he]; exact ihm
    have hstep := a_rat_step m hm
    have h2 : (5 / 3 : ℚ) * a_rat (m + 1) ≤ (5 / 3) * ((2 / 5) * a_rat m) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num)
    have hcalc : (5 / 3 : ℚ) * ((2 / 5) * a_rat m) = (2 / 3) * a_rat m := by ring
    linarith

lemma tail_bound_gen (m K : ℕ) (hm : 2 ≤ m) :
    (Finset.Icc m K).sum a_rat ≤ (5 / 3) * a_rat m := by
  by_cases h : m ≤ K
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact tail_bound d m hm
  · push_neg at h
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have hp := a_rat_pos m
    linarith

/-- For `m ≥ 2`, the tail sum strictly below `a_rat m` (super-increasing property). -/
lemma tail_strict (m K : ℕ) (hm : 2 ≤ m) :
    (Finset.Icc (m + 1) K).sum a_rat < a_rat m := by
  have hb := tail_bound_gen (m + 1) K (by omega)
  have hstep := a_rat_step m hm
  have hp := a_rat_pos m
  have h2 : (5 / 3 : ℚ) * a_rat (m + 1) ≤ (5 / 3) * ((2 / 5) * a_rat m) :=
    mul_le_mul_of_nonneg_left hstep (by norm_num)
  have hcalc : (5 / 3 : ℚ) * ((2 / 5) * a_rat m) = (2 / 3) * a_rat m := by ring
  linarith

/-! ### Bounds on the partial sums `S(j,k)` -/

lemma S_pos (j k : ℕ) (hjk : j ≤ k) : 0 < catalan_reciprocal_sum j k := by
  rw [catalan_reciprocal_sum]
  exact Finset.sum_pos (fun i _ => a_rat_pos i) (Finset.nonempty_Icc.mpr hjk)

lemma S_lt_one (j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
    catalan_reciprocal_sum j k < 1 := by
  rw [catalan_reciprocal_sum]
  have key : Finset.Icc j k = insert j (Finset.Icc (j + 1) k) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : j ∉ Finset.Icc (j + 1) k := by simp [Finset.mem_Icc]
  rw [key, Finset.sum_insert hnot]
  have htail := tail_strict j k hj
  have hhalf := a_rat_le_half j hj
  linarith

/-! ### Monotonicity / leading-term arguments -/

lemma S_mono_k (j k₁ k₂ : ℕ) (hjk : j ≤ k₁) (hlt : k₁ < k₂) :
    catalan_reciprocal_sum j k₁ < catalan_reciprocal_sum j k₂ := by
  rw [catalan_reciprocal_sum, catalan_reciprocal_sum]
  apply Finset.sum_lt_sum_of_subset
    (Finset.Icc_subset_Icc (le_refl j) (by omega)) (i := k₂)
  · simp only [Finset.mem_Icc]; omega
  · simp only [Finset.mem_Icc]; omega
  · exact a_rat_pos k₂
  · exact fun x _ _ => (a_rat_pos x).le

lemma S_lt_of_lt_j (j₁ k₁ j₂ k₂ : ℕ) (h1 : 2 ≤ j₁) (h1k : j₁ ≤ k₁)
    (hlt : j₁ < j₂) (h2k : j₂ ≤ k₂) :
    catalan_reciprocal_sum j₂ k₂ < catalan_reciprocal_sum j₁ k₁ := by
  rw [catalan_reciprocal_sum, catalan_reciprocal_sum]
  have hsub : Finset.Icc j₂ k₂ ⊆ Finset.Icc (j₁ + 1) k₂ :=
    Finset.Icc_subset_Icc (by omega) (le_refl _)
  have h_le : (Finset.Icc j₂ k₂).sum a_rat ≤ (Finset.Icc (j₁ + 1) k₂).sum a_rat :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (a_rat_pos i).le)
  have h_tail : (Finset.Icc (j₁ + 1) k₂).sum a_rat < a_rat j₁ := tail_strict j₁ k₂ h1
  have h_low : a_rat j₁ ≤ (Finset.Icc j₁ k₁).sum a_rat :=
    Finset.single_le_sum (fun i _ => (a_rat_pos i).le) (by simp only [Finset.mem_Icc]; omega)
  linarith

lemma S_inj (j₁ k₁ j₂ k₂ : ℕ) (h1 : 2 ≤ j₁) (h1k : j₁ ≤ k₁)
    (h2 : 2 ≤ j₂) (h2k : j₂ ≤ k₂)
    (hS : catalan_reciprocal_sum j₁ k₁ = catalan_reciprocal_sum j₂ k₂) :
    j₁ = j₂ ∧ k₁ = k₂ := by
  rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
  · exfalso
    have := S_lt_of_lt_j j₁ k₁ j₂ k₂ h1 h1k hlt h2k
    linarith
  · subst heq
    refine ⟨rfl, ?_⟩
    rcases lt_trichotomy k₁ k₂ with hk | hk | hk
    · exfalso; have := S_mono_k j₁ k₁ k₂ h1k hk; linarith
    · exact hk
    · exfalso; have := S_mono_k j₁ k₂ k₁ h2k hk; linarith
  · exfalso
    have := S_lt_of_lt_j j₂ k₂ j₁ k₁ h2 h2k hgt h1k
    linarith

/-! ### Classification of valid pairs and fractional-part facts -/

lemma classify (j k : ℕ) (h : oeis_108_index_cond j k) :
    (j = 1 ∧ k = 1) ∨ (2 ≤ j ∧ j ≤ k) := by
  obtain ⟨h1, h2, h3⟩ := h
  omega

lemma frac_eq_self_of (j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
    frac_part (catalan_reciprocal_sum j k) = (catalan_reciprocal_sum j k : ℝ) := by
  rw [frac_part]
  apply Int.fract_eq_self.mpr
  constructor
  · have := (S_pos j k hjk).le; exact_mod_cast this
  · have := S_lt_one j k hj hjk; exact_mod_cast this

lemma S_one_one : catalan_reciprocal_sum 1 1 = 1 := by
  rw [catalan_reciprocal_sum, Finset.Icc_self, Finset.sum_singleton, a_rat, a_one]
  norm_num

lemma frac_S_one_one : frac_part (catalan_reciprocal_sum 1 1) = 0 := by
  rw [frac_part, S_one_one]
  push_cast
  exact Int.fract_one

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
  intro j₁ k₁ j₂ k₂ c1 c2 hne
  rcases classify j₁ k₁ c1 with ⟨hj1, hk1⟩ | ⟨hj1, hjk1⟩
  · rcases classify j₂ k₂ c2 with ⟨hj2, hk2⟩ | ⟨hj2, hjk2⟩
    · exfalso; apply hne; rw [hj1, hk1, hj2, hk2]
    · rw [show j₁ = 1 from hj1, show k₁ = 1 from hk1, frac_S_one_one,
        frac_eq_self_of j₂ k₂ hj2 hjk2]
      have hpos : (0 : ℝ) < (catalan_reciprocal_sum j₂ k₂ : ℝ) := by
        exact_mod_cast S_pos j₂ k₂ hjk2
      exact ne_of_lt hpos
  · rcases classify j₂ k₂ c2 with ⟨hj2, hk2⟩ | ⟨hj2, hjk2⟩
    · rw [show j₂ = 1 from hj2, show k₂ = 1 from hk2, frac_S_one_one,
        frac_eq_self_of j₁ k₁ hj1 hjk1]
      have hpos : (0 : ℝ) < (catalan_reciprocal_sum j₁ k₁ : ℝ) := by
        exact_mod_cast S_pos j₁ k₁ hjk1
      exact (ne_of_lt hpos).symm
    · rw [frac_eq_self_of j₁ k₁ hj1 hjk1, frac_eq_self_of j₂ k₂ hj2 hjk2]
      intro hcast
      have hS : catalan_reciprocal_sum j₁ k₁ = catalan_reciprocal_sum j₂ k₂ := by
        exact_mod_cast hcast
      obtain ⟨e1, e2⟩ := S_inj j₁ k₁ j₂ k₂ hj1 hjk1 hj2 hjk2 hS
      exact hne (by rw [e1, e2])
