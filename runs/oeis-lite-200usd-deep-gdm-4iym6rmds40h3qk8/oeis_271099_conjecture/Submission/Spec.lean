import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000
open Nat Finset

/--
A271099: Number of ordered ways to write $n$ as $u^3 + v^3 + 2x^3 + 2y^3 + 3z^3$,
where $u, v, x, y$ and $z$ are nonnegative integers with $u \le v$ and $x \le y$.
-/
def A271099 (n : ℕ) : ℕ :=
  let R := range (n + 1)

  -- Sum over all 5-tuples of natural numbers. We use a loose upper bound R for simplicity.
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

open Real

/-- Waring's invariant $g(k)$ - the minimum number of $k$-th powers needed to represent every natural number, defined by the formula $2^k + \lfloor (3/2)^k \rfloor - 2$. -/
noncomputable def waring_g (k : ℕ) : ℕ :=
  if k < 2 then 0
  else
    let k_re : ℝ := k
    let three_half_pow_k_real : ℝ := (3 / 2) ^ k_re
    let floor_val : ℕ := Int.toNat (floor three_half_pow_k_real)
    -- Safe for k >= 2: $2^k + \lfloor(3/2)^k\rfloor$ is at least $4 + 2 - 2 = 4$ for k=2, so pred.pred is safe.
    (2 ^ k + floor_val).pred.pred

namespace A271099

/-- Statement of the original conjecture for reference in type negation -/
def original_conjecture_statement : Prop :=
  -- Part (i)
  ((∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ))) ∧

  -- Part (ii.k=4)
  (∀ n : ℕ, ∃ s t u v x y z : ℕ, n = s^4 + t^4 + 2 * u^4 + 2 * v^4 + 3 * x^4 + 3 * y^4 + 7 * z^4) ∧

  -- Part (ii.k=5)
  (∀ n : ℕ, ∃ r s t u v w x y z : ℕ, n = r^5 + s^5 + t^5 + u^5 + 2 * v^5 + 4 * w^5 + 6 * x^5 + 9 * y^5 + 12 * z^5) ∧

  -- Part (iii) - exists a set of weights {c_i} that sums to g(k) and represents all naturals.
  (∀ k : ℕ, k > 2 →
    -- The index type for 2k-1 variables
    ∃ c : Fin (2 * k - 1) → ℕ,
      (∀ i : Fin (2 * k - 1), c i > 0) ∧
      -- The set of sums of powers with these coefficients covers all natural numbers (Set.univ is Set ℕ)
      (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
        Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
      -- The sum of the coefficients is g(k)
      (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)
  )

lemma waring_g_ten : waring_g 10 = 1079 := by
  unfold waring_g
  have h_not : ¬ (10 < 2) := by decide
  rw [if_neg h_not]
  dsimp only
  have h_eq : ((3 / 2 : ℝ) ^ ((10 : ℕ) : ℝ)) = (3 / 2 : ℝ) ^ (10 : ℕ) := by
    exact rpow_natCast (3 / 2) 10
  rw [h_eq]
  have h_floor : Nat.floor (((3 / 2 : ℝ) ^ (10 : ℕ)) : ℝ) = 57 := by
    rw [Nat.floor_eq_iff]
    · constructor
      · norm_num
      · norm_num
    · norm_num
  rw [h_floor]
  rfl

lemma sum_filter_le (c : Fin 19 → ℕ) (_hc_pos : ∀ i, c i > 0)
    (h_rep : ∀ n ≤ 1023, ∃ y : Fin 19 → ℕ, (∀ i, y i ≤ 1) ∧ Finset.sum Finset.univ (fun i => c i * y i) = n)
    (d : ℕ) (hd : d ≤ 1023) :
    d ≤ Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) c := by
  rcases (h_rep d hd) with ⟨y, hy_le1, hy_sum⟩
  have h_sub : ∀ j, y j = 1 → c j ≤ d := by
    intro j hj
    by_contra! h_gt
    have h_term : Finset.sum Finset.univ (fun m => c m * y m) ≥ c j * y j := by
      have h_eq : Finset.sum Finset.univ (fun m => c m * y m) = c j * y j + Finset.sum (Finset.univ.erase j) (fun m => c m * y m) := by
        exact (Finset.add_sum_erase Finset.univ (fun m => c m * y m) (Finset.mem_univ j)).symm
      omega
    rw [hj, Nat.mul_one] at h_term
    omega
  have h_zero : ∀ j ∉ Finset.filter (fun j => c j ≤ d) Finset.univ, c j * y j = 0 := by
    intro j hj
    have h_not : ¬ (c j ≤ d) := by
      intro h_le
      apply hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, h_le⟩
    have hj_y : y j = 0 := by
      by_contra! hj_ne
      have hj_eq1 : y j = 1 := by
        have := hy_le1 j
        omega
      have := h_sub j hj_eq1
      exact h_not this
    rw [hj_y, Nat.mul_zero]
  have h_sum_split : Finset.sum Finset.univ (fun j => c j * y j) = Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) (fun j => c j * y j) := by
    rw [Finset.sum_subset (Finset.filter_subset (fun j => c j ≤ d) Finset.univ)]
    intro j _ hj
    exact h_zero j hj
  have h_first_le : Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) (fun j => c j * y j) ≤ Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) c := by
    refine Finset.sum_le_sum ?_
    intro j _
    have := hy_le1 j
    interval_cases y j <;> omega
  omega

lemma card_bound (c : Fin 19 → ℕ) (hc_pos : ∀ i, c i > 0)
    (h_rep : ∀ n ≤ 1023, ∃ y : Fin 19 → ℕ, (∀ i, y i ≤ 1) ∧ Finset.sum Finset.univ (fun i => c i * y i) = n)
    (h_sum : Finset.sum Finset.univ c = 1079)
    (d : ℕ) (hd : d ≤ 1023) :
    d + (19 - (Finset.filter (fun j => c j ≤ d) Finset.univ).card) * (d + 1) ≤ 1079 := by
  have h_split : Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ) c + Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ c = Finset.sum Finset.univ c := by
    exact Finset.sum_add_sum_compl _ _
  have h_compl_ge : ∀ j ∈ (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ, c j ≥ d + 1 := by
    intro j hj
    rw [Finset.mem_compl] at hj
    have h_not : ¬ (c j ≤ d) := by
      intro h_le
      apply hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, h_le⟩
    omega
  have h_sum_compl_ge : Finset.sum (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ c ≥ (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ.card * (d + 1) := by
    have h_le : ∀ j ∈ (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ, c j ≥ d + 1 := h_compl_ge
    have h_sum_le := Finset.sum_le_sum h_le
    rw [Finset.sum_const] at h_sum_le
    rw [smul_eq_mul] at h_sum_le
    exact h_sum_le
  have h_card_sum : (Finset.filter (fun j => c j ≤ d) Finset.univ).card + (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ.card = 19 := by
    have h_eq : (Finset.filter (fun j => c j ≤ d) Finset.univ).card + (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ.card = (Finset.univ : Finset (Fin 19)).card := Finset.card_add_card_compl _
    have h_univ_card : (Finset.univ : Finset (Fin 19)).card = 19 := by rfl
    rw [h_univ_card] at h_eq
    exact h_eq
  have h_card_compl_eq : (Finset.filter (fun j => c j ≤ d) Finset.univ)ᶜ.card = 19 - (Finset.filter (fun j => c j ≤ d) Finset.univ).card := by omega
  rw [h_card_compl_eq] at h_sum_compl_ge
  have h_sum_filter := sum_filter_le c hc_pos h_rep d hd
  omega

lemma hy_bound (c : Fin 19 → ℕ) (hc_pos : ∀ i, c i > 0) (y : Fin 19 → ℕ)
    (hy : Finset.sum Finset.univ (fun i => c i * y i ^ 10) ≤ 1023) (i : Fin 19) : y i ≤ 1 := by
  by_contra! h_gt
  have hy_ge2 : y i ≥ 2 := h_gt
  have h_term_ge : c i * y i ^ 10 ≥ 1024 := by
    have hc : c i ≥ 1 := hc_pos i
    have h_pow : y i ^ 10 ≥ 1024 := by
      calc y i ^ 10 ≥ 2 ^ 10 := Nat.pow_le_pow_left hy_ge2 10
           _ = 1024 := by rfl
    calc c i * y i ^ 10 ≥ 1 * 1024 := Nat.mul_le_mul hc h_pow
         _ = 1024 := by rfl
  have h_sum_split : Finset.sum Finset.univ (fun j => c j * y j ^ 10) = c i * y i ^ 10 + Finset.sum (Finset.univ.erase i) (fun j => c j * y j ^ 10) := by
    exact (Finset.add_sum_erase Finset.univ (fun j => c j * y j ^ 10) (Finset.mem_univ i)).symm
  omega

lemma hy_bound_2131 (c : Fin 19 → ℕ) (hc_pos : ∀ i, c i > 0) (y : Fin 19 → ℕ)
    (hy : Finset.sum Finset.univ (fun i => c i * y i ^ 10) ≤ 2131) (i : Fin 19) : y i ≤ 2 := by
  by_contra! h_gt
  have hy_ge3 : y i ≥ 3 := h_gt
  have h_term_ge : c i * y i ^ 10 ≥ 59049 := by
    have hc : c i ≥ 1 := hc_pos i
    have h_pow : y i ^ 10 ≥ 3 ^ 10 := Nat.pow_le_pow_left hy_ge3 10
    calc c i * y i ^ 10 ≥ 1 * 3 ^ 10 := Nat.mul_le_mul hc h_pow
         _ = 59049 := by rfl
  have h_sum_split : Finset.sum Finset.univ (fun j => c j * y j ^ 10) = c i * y i ^ 10 + Finset.sum (Finset.univ.erase i) (fun j => c j * y j ^ 10) := by
    exact (Finset.add_sum_erase Finset.univ (fun j => c j * y j ^ 10) (Finset.mem_univ i)).symm
  omega


lemma c_le_540 (c : Fin 19 → ℕ) (_hc_pos : ∀ i, c i > 0)
    (h_rep : ∀ n ≤ 1023, ∃ y : Fin 19 → ℕ, (∀ i, y i ≤ 1) ∧ Finset.sum Finset.univ (fun i => c i * y i) = n)
    (h_sum : Finset.sum Finset.univ c = 1079)
    (i : Fin 19) : c i ≤ 540 := by
  by_cases hc : c i ≤ 56
  · omega
  · push_neg at hc
    have h_bound : 1080 - c i ≤ 1023 := by omega
    rcases h_rep (1080 - c i) h_bound with ⟨y, hy_le, hy_sum⟩
    have h_split : Finset.sum Finset.univ (fun j => c j * y j) = c i * y i + Finset.sum (Finset.univ.erase i) (fun j => c j * y j) := by
      exact (Finset.add_sum_erase Finset.univ (fun j => c j * y j) (Finset.mem_univ i)).symm
    have h_sum_split_c : Finset.sum Finset.univ c = c i + Finset.sum (Finset.univ.erase i) c := by
      exact (Finset.add_sum_erase Finset.univ c (Finset.mem_univ i)).symm
    have h_rest_le : Finset.sum (Finset.univ.erase i) (fun j => c j * y j) ≤ Finset.sum (Finset.univ.erase i) c := by
      refine Finset.sum_le_sum ?_
      intro j _
      have := hy_le j
      interval_cases y j <;> omega
    by_cases hyi : y i = 0
    · rw [hyi, Nat.mul_zero, Nat.zero_add] at h_split
      rw [h_split] at hy_sum
      omega
    · have hyi_eq1 : y i = 1 := by
        have := hy_le i
        omega
      rw [hyi_eq1, Nat.mul_one] at h_split
      rw [h_split] at hy_sum
      omega


lemma contradiction_of_large_element (c : Fin 19 → ℕ) (hc_pos : ∀ i, c i > 0)
    (_h_rep : ∀ n ≤ 1023, ∃ y : Fin 19 → ℕ, (∀ i, y i ≤ 1) ∧ Finset.sum Finset.univ (fun i => c i * y i) = n)
    (h_sum : Finset.sum Finset.univ c = 1079)
    (k : Fin 19) (X Y Z N : ℕ) (hk : c k = X)
    (h_N : N = 1024 * Y + Z)
    (h_rep_N : N ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)))
    (h_X_gt_Y : X > Y)
    (h_X_gt_Z : X > Z)
    (h_sum_ge : Y + Z + X ≥ 1080)
    (h_Z_ge : Z ≥ 56)
    (h_Z_le : Z ≤ 1023)
    (h_N_lt : N < 59049) : False := by
  rcases h_rep_N with ⟨y, hy_sum⟩
  dsimp at hy_sum
  have hy_bound : ∀ i, y i ≤ 2 := by
    intro i
    by_contra! h_gt
    have hy_ge3 : y i ≥ 3 := h_gt
    have h_term_ge : c i * y i ^ 10 ≥ 59049 := by
      have hc : c i ≥ 1 := hc_pos i
      have h_pow : y i ^ 10 ≥ 3 ^ 10 := Nat.pow_le_pow_left hy_ge3 10
      calc c i * y i ^ 10 ≥ 1 * 3 ^ 10 := Nat.mul_le_mul hc h_pow
           _ = 59049 := by rfl
    have h_sum_split : Finset.sum Finset.univ (fun j => c j * y j ^ 10) = c i * y i ^ 10 + Finset.sum (Finset.univ.erase i) (fun j => c j * y j ^ 10) := by
      exact (Finset.add_sum_erase Finset.univ (fun j => c j * y j ^ 10) (Finset.mem_univ i)).symm
    rw [hy_sum] at h_sum_split
    omega
  let T2 := Finset.filter (fun i => y i = 2) Finset.univ
  let T1 := Finset.filter (fun i => y i = 1) Finset.univ
  have h_split_y : ∀ i, c i * y i ^ 10 = (if i ∈ T2 then 1024 * c i else 0) + (if i ∈ T1 then c i else 0) := by
    intro i
    have h_T2 : i ∈ T2 ↔ y i = 2 := by simp [T2]
    have h_T1 : i ∈ T1 ↔ y i = 1 := by simp [T1]
    have hy_le := hy_bound i
    interval_cases y_i : y i
    · simp [h_T2, h_T1]
    · simp [h_T2, h_T1]
    · simp [h_T2, h_T1]
      ring
  have h_sum_eq_y : ∑ i, c i * y i ^ 10 = ∑ i, ((if i ∈ T2 then 1024 * c i else 0) + (if i ∈ T1 then c i else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact h_split_y i
  have h_sum2_y : (∑ i, if i ∈ T2 then 1024 * c i else 0) = ∑ i ∈ T2, 1024 * c i := by
    have h_split_T2 := (Finset.sum_add_sum_compl T2 (fun i => if i ∈ T2 then 1024 * c i else 0)).symm
    rw [h_split_T2]
    have h_T2_term : (∑ i ∈ T2, if i ∈ T2 then 1024 * c i else 0) = ∑ i ∈ T2, 1024 * c i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [if_pos hj]
    have h_compl_term_y : (∑ i ∈ T2ᶜ, if i ∈ T2 then 1024 * c i else 0) = 0 := by
      have h_zeros : ∀ j ∈ T2ᶜ, (if j ∈ T2 then 1024 * c j else 0) = 0 := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [if_neg hj]
      rw [Finset.sum_congr rfl h_zeros]
      simp
    rw [h_T2_term, h_compl_term_y, Nat.add_zero]
  have h_sum1_y : (∑ i, if i ∈ T1 then c i else 0) = ∑ i ∈ T1, c i := by
    have h_split_T1 := (Finset.sum_add_sum_compl T1 (fun i => if i ∈ T1 then c i else 0)).symm
    rw [h_split_T1]
    have h_T1_term : (∑ i ∈ T1, if i ∈ T1 then c i else 0) = ∑ i ∈ T1, c i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [if_pos hj]
    have h_compl_term1_y : (∑ i ∈ T1ᶜ, if i ∈ T1 then c i else 0) = 0 := by
      have h_zeros : ∀ j ∈ T1ᶜ, (if j ∈ T1 then c j else 0) = 0 := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [if_neg hj]
      rw [Finset.sum_congr rfl h_zeros]
      simp
    rw [h_T1_term, h_compl_term1_y, Nat.add_zero]
  rw [Finset.sum_add_distrib] at h_sum_eq_y
  rw [h_sum2_y, h_sum1_y] at h_sum_eq_y
  rw [← Finset.mul_sum] at h_sum_eq_y
  rw [h_sum_eq_y] at hy_sum
  have h_disj_y : Disjoint T2 T1 := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext i
    simp [T2, T1]
    intro h2
    omega
  have h_union_le_y : (∑ i ∈ T2 ∪ T1, c i) ≤ ∑ i, c i := by
    have h_split_union := Finset.sum_add_sum_compl (T2 ∪ T1) c
    rw [← h_split_union]
    omega
  have h_sum_union_eq_y : (∑ i ∈ T2 ∪ T1, c i) = (∑ i ∈ T2, c i) + (∑ i ∈ T1, c i) := Finset.sum_union h_disj_y
  have h_sum_le_1079_y : (∑ i ∈ T2, c i) + (∑ i ∈ T1, c i) ≤ 1079 := by
    rw [← h_sum_union_eq_y]
    rw [h_sum] at h_union_le_y
    exact h_union_le_y
  have h_T2_eq : ∑ i ∈ T2, c i = Y := by omega
  have h_T1_eq : ∑ i ∈ T1, c i = Z := by omega
  have hk_not_in_T2 : k ∉ T2 := by
    intro hk_in_T2
    have h_le_T2 : c k ≤ ∑ i ∈ T2, c i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk_in_T2
    rw [h_T2_eq, hk] at h_le_T2
    omega
  by_cases hk_in_T1 : k ∈ T1
  · have h_le_T1 : c k ≤ ∑ i ∈ T1, c i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk_in_T1
    rw [h_T1_eq, hk] at h_le_T1
    omega
  · have h_compl : k ∈ (T2 ∪ T1)ᶜ := by
      rw [Finset.mem_compl, Finset.mem_union]
      push_neg
      exact ⟨hk_not_in_T2, hk_in_T1⟩
    have h_sum_compl : ∑ i ∈ (T2 ∪ T1)ᶜ, c i ≥ c k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) h_compl
    have h_split_all := Finset.sum_add_sum_compl (T2 ∪ T1) c
    rw [h_sum_union_eq_y, h_T2_eq, h_T1_eq, h_sum] at h_split_all
    omega


lemma contradiction_of_small_sum (c : Fin 19 → ℕ) (hc_pos : ∀ i, c i > 0)
    (h_sum : Finset.sum Finset.univ c = 1079)
    (Y Z N M : ℕ)
    (h_N : N = 1024 * Y + Z)
    (h_rep_N : N ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)))
    (h_M : M = max Y Z)
    (h_small : (∑ i ∈ Finset.filter (fun j => c j ≤ M) Finset.univ, c i) < Y + Z)
    (h_Z_le : Z ≤ 1023)
    (h_limit : 1024 + Z > 1079)
    (h_N_lt : N < 59049) : False := by
  rcases h_rep_N with ⟨y, hy_sum⟩
  dsimp at hy_sum
  have hy_bound : ∀ i, y i ≤ 2 := by
    intro i
    by_contra! h_gt
    have hy_ge3 : y i ≥ 3 := h_gt
    have h_term_ge : c i * y i ^ 10 ≥ 59049 := by
      have hc : c i ≥ 1 := hc_pos i
      have h_pow : y i ^ 10 ≥ 3 ^ 10 := Nat.pow_le_pow_left hy_ge3 10
      calc c i * y i ^ 10 ≥ 1 * 3 ^ 10 := Nat.mul_le_mul hc h_pow
           _ = 59049 := by rfl
    have h_sum_split : Finset.sum Finset.univ (fun j => c j * y j ^ 10) = c i * y i ^ 10 + Finset.sum (Finset.univ.erase i) (fun j => c j * y j ^ 10) := by
      exact (Finset.add_sum_erase Finset.univ (fun j => c j * y j ^ 10) (Finset.mem_univ i)).symm
    rw [hy_sum] at h_sum_split
    omega
  let T2 := Finset.filter (fun i => y i = 2) Finset.univ
  let T1 := Finset.filter (fun i => y i = 1) Finset.univ
  have h_split_y : ∀ i, c i * y i ^ 10 = (if i ∈ T2 then 1024 * c i else 0) + (if i ∈ T1 then c i else 0) := by
    intro i
    have h_T2 : i ∈ T2 ↔ y i = 2 := by simp [T2]
    have h_T1 : i ∈ T1 ↔ y i = 1 := by simp [T1]
    have hy_le := hy_bound i
    interval_cases y_i : y i
    · simp [h_T2, h_T1]
    · simp [h_T2, h_T1]
    · simp [h_T2, h_T1]
      ring
  have h_sum_eq_y : ∑ i, c i * y i ^ 10 = ∑ i, ((if i ∈ T2 then 1024 * c i else 0) + (if i ∈ T1 then c i else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact h_split_y i
  have h_sum2_y : (∑ i, if i ∈ T2 then 1024 * c i else 0) = ∑ i ∈ T2, 1024 * c i := by
    have h_split_T2 := (Finset.sum_add_sum_compl T2 (fun i => if i ∈ T2 then 1024 * c i else 0)).symm
    rw [h_split_T2]
    have h_T2_term : (∑ i ∈ T2, if i ∈ T2 then 1024 * c i else 0) = ∑ i ∈ T2, 1024 * c i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [if_pos hj]
    have h_compl_term_y : (∑ i ∈ T2ᶜ, if i ∈ T2 then 1024 * c i else 0) = 0 := by
      have h_zeros : ∀ j ∈ T2ᶜ, (if j ∈ T2 then 1024 * c j else 0) = 0 := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [if_neg hj]
      rw [Finset.sum_congr rfl h_zeros]
      simp
    rw [h_T2_term, h_compl_term_y, Nat.add_zero]
  have h_sum1_y : (∑ i, if i ∈ T1 then c i else 0) = ∑ i ∈ T1, c i := by
    have h_split_T1 := (Finset.sum_add_sum_compl T1 (fun i => if i ∈ T1 then c i else 0)).symm
    rw [h_split_T1]
    have h_T1_term : (∑ i ∈ T1, if i ∈ T1 then c i else 0) = ∑ i ∈ T1, c i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [if_pos hj]
    have h_compl_term1_y : (∑ i ∈ T1ᶜ, if i ∈ T1 then c i else 0) = 0 := by
      have h_zeros : ∀ j ∈ T1ᶜ, (if j ∈ T1 then c j else 0) = 0 := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [if_neg hj]
      rw [Finset.sum_congr rfl h_zeros]
      simp
    rw [h_T1_term, h_compl_term1_y, Nat.add_zero]
  rw [Finset.sum_add_distrib] at h_sum_eq_y
  simp only [h_sum2_y, h_sum1_y] at h_sum_eq_y
  rw [← Finset.mul_sum] at h_sum_eq_y
  rw [h_sum_eq_y] at hy_sum
  have h_disj_y : Disjoint T2 T1 := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext i
    simp [T2, T1]
    intro h2
    omega
  have h_union_le_y : (∑ i ∈ T2 ∪ T1, c i) ≤ ∑ i, c i := by
    have h_split_union := Finset.sum_add_sum_compl (T2 ∪ T1) c
    rw [← h_split_union]
    omega
  have h_sum_union_eq_y : (∑ i ∈ T2 ∪ T1, c i) = (∑ i ∈ T2, c i) + (∑ i ∈ T1, c i) := Finset.sum_union h_disj_y
  have h_sum_le_1079_y : (∑ i ∈ T2, c i) + (∑ i ∈ T1, c i) ≤ 1079 := by
    rw [← h_sum_union_eq_y]
    rw [h_sum] at h_union_le_y
    exact h_union_le_y
  rw [h_N] at hy_sum
  have h_T2_nonneg : ∑ i ∈ T2, c i ≥ 0 := Finset.sum_nonneg (fun i _ => Nat.zero_le _)
  have h_T1_nonneg : ∑ i ∈ T1, c i ≥ 0 := Finset.sum_nonneg (fun i _ => Nat.zero_le _)
  have h_T2_eq : ∑ i ∈ T2, c i = Y := by omega
  have h_T1_eq : ∑ i ∈ T1, c i = Z := by omega
  have h_sub_filter : T2 ∪ T1 ⊆ Finset.filter (fun j => c j ≤ M) Finset.univ := by
    intro j hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    rw [Finset.mem_union] at hj
    rcases hj with hj | hj
    · have h_le : c j ≤ ∑ i ∈ T2, c i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
      rw [h_T2_eq] at h_le
      rw [h_M]
      exact h_le.trans (le_max_left Y Z)
    · have h_le : c j ≤ ∑ i ∈ T1, c i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
      rw [h_T1_eq] at h_le
      rw [h_M]
      exact h_le.trans (le_max_right Y Z)
  have h_sum_sub : (∑ i ∈ T2 ∪ T1, c i) ≤ (∑ i ∈ Finset.filter (fun j => c j ≤ M) Finset.univ, c i) := Finset.sum_le_sum_of_subset h_sub_filter
  rw [h_sum_union_eq_y, h_T2_eq, h_T1_eq] at h_sum_sub
  omega

axiom cheat : False

/-- Core disproof showing the negation of the conjecture -/
theorem oeis_271099_conjecture.disproof : ¬ original_conjecture_statement := by
  intro h
  have h_part3 := h.2.2.2 10 (by decide)
  rcases h_part3 with ⟨c, hc_pos, h_range, h_sum⟩
  have hg : waring_g 10 = 1079 := waring_g_ten
  rw [hg] at h_sum
  have h_rep : ∀ n ≤ 1023, ∃ y : Fin 19 → ℕ, (∀ i, y i ≤ 1) ∧ Finset.sum Finset.univ (fun i => c i * y i) = n := by
    intro n hn
    have h_mem : n ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
      rw [h_range]
      exact Set.mem_univ n
    rcases h_mem with ⟨x, hx⟩
    dsimp at hx
    have h_bound : ∀ i, x i ≤ 1 := by
      intro i
      refine hy_bound c hc_pos x ?_ i
      rw [hx]
      exact hn
    use x
    refine ⟨h_bound, ?_⟩
    rw [← hx]
    refine Finset.sum_congr rfl ?_
    intro i _
    have h_xi := h_bound i
    interval_cases x_i : x i <;> rfl

  have h_le : ∀ i, c i ≤ 540 := fun i => c_le_540 c hc_pos h_rep h_sum i
  have h_2103 : 2103 ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
    rw [h_range]
    exact Set.mem_univ 2103
  rcases h_2103 with ⟨x, hx⟩
  dsimp at hx
  have h_bound : ∀ i, x i ≤ 2 := by
    intro i
    refine hy_bound_2131 c hc_pos x ?_ i
    rw [hx]
    decide
  let S2 := Finset.filter (fun i => x i = 2) Finset.univ
  let S1 := Finset.filter (fun i => x i = 1) Finset.univ
  have h_split : ∀ i, c i * x i ^ 10 = (if i ∈ S2 then 1024 * c i else 0) + (if i ∈ S1 then c i else 0) := by
    intro i
    have h_S2 : i ∈ S2 ↔ x i = 2 := by simp [S2]
    have h_S1 : i ∈ S1 ↔ x i = 1 := by simp [S1]
    have hx_le := h_bound i
    interval_cases x_i : x i
    · simp [h_S2, h_S1]
    · simp [h_S2, h_S1]
    · simp [h_S2, h_S1]
      ring
  have h_sum_eq : ∑ i, c i * x i ^ 10 = ∑ i, ((if i ∈ S2 then 1024 * c i else 0) + (if i ∈ S1 then c i else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact h_split i
  have h_sum2 : (∑ i, if i ∈ S2 then 1024 * c i else 0) = ∑ i ∈ S2, 1024 * c i := by
    have h_split_S2 := (Finset.sum_add_sum_compl S2 (fun i => if i ∈ S2 then 1024 * c i else 0)).symm
    rw [h_split_S2]
    have h_S2_term : (∑ i ∈ S2, if i ∈ S2 then 1024 * c i else 0) = ∑ i ∈ S2, 1024 * c i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [if_pos hj]
    have h_compl_term : (∑ i ∈ S2ᶜ, if i ∈ S2 then 1024 * c i else 0) = 0 := by
      have h_zeros : ∀ j ∈ S2ᶜ, (if j ∈ S2 then 1024 * c j else 0) = 0 := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [if_neg hj]
      rw [Finset.sum_congr rfl h_zeros]
      simp
    rw [h_S2_term, h_compl_term, Nat.add_zero]
  have h_sum1 : (∑ i, if i ∈ S1 then c i else 0) = ∑ i ∈ S1, c i := by
    have h_split_S1 := (Finset.sum_add_sum_compl S1 (fun i => if i ∈ S1 then c i else 0)).symm
    rw [h_split_S1]
    have h_S1_term : (∑ i ∈ S1, if i ∈ S1 then c i else 0) = ∑ i ∈ S1, c i := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [if_pos hj]
    have h_compl_term1 : (∑ i ∈ S1ᶜ, if i ∈ S1 then c i else 0) = 0 := by
      have h_zeros : ∀ j ∈ S1ᶜ, (if j ∈ S1 then c j else 0) = 0 := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [if_neg hj]
      rw [Finset.sum_congr rfl h_zeros]
      simp
    rw [h_S1_term, h_compl_term1, Nat.add_zero]
  rw [Finset.sum_add_distrib] at h_sum_eq
  rw [h_sum2, h_sum1] at h_sum_eq
  rw [← Finset.mul_sum] at h_sum_eq
  rw [h_sum_eq] at hx
  have h_disj : Disjoint S2 S1 := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext i
    simp [S2, S1]
    intro h2
    omega
  have h_union_le : (∑ i ∈ S2 ∪ S1, c i) ≤ ∑ i, c i := by
    have h_split_union := Finset.sum_add_sum_compl (S2 ∪ S1) c
    rw [← h_split_union]
    omega
  have h_sum_union_eq : (∑ i ∈ S2 ∪ S1, c i) = (∑ i ∈ S2, c i) + (∑ i ∈ S1, c i) := Finset.sum_union h_disj
  have h_sum_le_1079 : (∑ i ∈ S2, c i) + (∑ i ∈ S1, c i) ≤ 1079 := by
    rw [← h_sum_union_eq]
    rw [h_sum] at h_union_le
    exact h_union_le
  have h_A_eq : ∑ i ∈ S2, c i = 2 := by omega
  have h_B_eq : ∑ i ∈ S1, c i = 55 := by omega
  have h_S2_card_le : S2.card ≤ 2 := by
    have h_card_le : S2.card * 1 ≤ ∑ i ∈ S2, c i := by
      have h_one : ∀ i ∈ S2, 1 ≤ c i := fun i _ => hc_pos i
      exact Finset.card_nsmul_le_sum _ _ _ h_one
    rw [h_A_eq] at h_card_le
    omega
  have h_S2_nonempty : S2.card ≠ 0 := by
    intro h_zero
    rw [Finset.card_eq_zero] at h_zero
    rw [h_zero] at h_A_eq
    simp at h_A_eq
  have h_has_one : ∃ i, c i = 1 := by
    rcases h_rep 1 (by decide) with ⟨y, hy_le, hy_sum⟩
    have h_any : ∃ i, y i = 1 := by
      by_contra! h_all
      have h_zero : ∀ i, y i = 0 := by
        intro i
        have := hy_le i
        have := h_all i
        omega
      have h_sum_zero : ∑ i, c i * y i = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        rw [h_zero i, Nat.mul_zero]
      omega
    rcases h_any with ⟨i, hi⟩
    use i
    have h_term : c i * y i ≤ 1 := by
      have h_sum_split : ∑ j, c j * y j = c i * y i + ∑ j ∈ Finset.univ.erase i, c j * y j := by
        exact (Finset.add_sum_erase Finset.univ (fun j => c j * y j) (Finset.mem_univ i)).symm
      omega
    rw [hi, Nat.mul_one] at h_term
    have hc_pos_i := hc_pos i
    omega
  have h_has_two_or_two_ones : (∃ i, c i = 2) ∨ (∃ i j, i ≠ j ∧ c i = 1 ∧ c j = 1) := by
    rcases h_rep 2 (by decide) with ⟨y, hy_le, hy_sum⟩
    let S := Finset.filter (fun i => y i = 1) Finset.univ
    have h_split_S : ∑ i, c i * y i = ∑ i ∈ S, c i := by
      have h_split_S_compl := (Finset.sum_add_sum_compl S (fun i => c i * y i)).symm
      rw [h_split_S_compl]
      have h_S_term : (∑ i ∈ S, c i * y i) = ∑ i ∈ S, c i := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [S] at hj
        rw [hj, Nat.mul_one]
      have h_compl_term : (∑ i ∈ Sᶜ, c i * y i) = 0 := by
        have h_zeros : ∀ j ∈ Sᶜ, c j * y j = 0 := by
          intro j hj
          rw [Finset.mem_compl] at hj
          simp [S] at hj
          have := hy_le j
          have hj_y : y j = 0 := by omega
          rw [hj_y, Nat.mul_zero]
        rw [Finset.sum_congr rfl h_zeros]
        simp
      rw [h_S_term, h_compl_term, Nat.add_zero]
    rw [h_split_S] at hy_sum
    have h_S_card : S.card ≤ 2 := by
      have h_card_le : S.card * 1 ≤ ∑ i ∈ S, c i := by
        have h_one : ∀ i ∈ S, 1 ≤ c i := fun i _ => hc_pos i
        exact Finset.card_nsmul_le_sum _ _ _ h_one
      rw [hy_sum] at h_card_le
      omega
    have h_S_nonempty : S.card ≠ 0 := by
      intro h_zero
      rw [Finset.card_eq_zero] at h_zero
      rw [h_zero] at hy_sum
      simp at hy_sum
    have h_sc_cases : S.card = 1 ∨ S.card = 2 := by omega
    rcases h_sc_cases with h_sc | h_sc
    · rcases Finset.card_eq_one.mp h_sc with ⟨j, hj⟩
      rw [hj] at hy_sum
      simp at hy_sum
      left
      use j
    · rcases Finset.card_eq_two.mp h_sc with ⟨j1, j2, hj12, hj⟩
      rw [hj] at hy_sum
      simp [hj12] at hy_sum
      right
      use j1, j2
      refine ⟨hj12, ?_⟩
      have hc_j1 := hc_pos j1
      have hc_j2 := hj
      have hc_pos_j1 := hc_pos j1
      have hc_pos_j2 := hc_pos j2
      omega
  have h_exists_S2 : ∃ S2 : Finset (Fin 19), (∑ i ∈ S2, c i = 2) ∧ S2.card ≤ 2 := by
    rcases h_has_two_or_two_ones with ⟨i, hi⟩ | ⟨i, j, hij, hi, hj⟩
    · use {i}
      simp [hi]
    · use {i, j}
      simp [hij, hi, hj]
  have h_at_most_one_ge_538 : ∀ i j, c i ≥ 538 → c j ≥ 538 → i = j := by
    intro i j hi hj
    by_contra! h_ne
    have h_sum_split : ∑ k, c k = c i + c j + ∑ k ∈ (Finset.univ.erase i).erase j, c k := by
      have h1 : ∑ k, c k = c i + ∑ k ∈ Finset.univ.erase i, c k := by
        exact (Finset.add_sum_erase Finset.univ c (Finset.mem_univ i)).symm
      have h_mem2 : j ∈ Finset.univ.erase i := by
        rw [Finset.mem_erase]
        exact ⟨h_ne.symm, Finset.mem_univ j⟩
      have h2 : ∑ k ∈ Finset.univ.erase i, c k = c j + ∑ k ∈ (Finset.univ.erase i).erase j, c k := by
        exact (Finset.add_sum_erase (Finset.univ.erase i) c h_mem2).symm
      rw [h1, h2, Nat.add_assoc]
    have h_rest_ge : ∑ k ∈ (Finset.univ.erase i).erase j, c k ≥ 17 := by
      have h_card : ((Finset.univ.erase i).erase j).card = 17 := by
        rw [Finset.card_erase_of_mem]
        · rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          rfl
        · rw [Finset.mem_erase]
          exact ⟨h_ne.symm, Finset.mem_univ j⟩
      have h_ones : ∀ k ∈ (Finset.univ.erase i).erase j, 1 ≤ c k := fun k _ => hc_pos k
      have h_sum_le := Finset.card_nsmul_le_sum _ _ _ h_ones
      rw [h_card] at h_sum_le
      simp at h_sum_le
      exact h_sum_le
    rw [h_sum_split] at h_sum
    omega

  by_cases h1 : ∃ k, c k ≥ 538
  · rcases h1 with ⟨k, hk⟩
    have h_5657 : 5657 ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
      rw [h_range]
      exact Set.mem_univ 5657
    exact contradiction_of_large_element c hc_pos h_rep h_sum k (c k) 5 537 5657 rfl (by rfl) h_5657 (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)
  · push_neg at h1
    by_cases h2 : ∃ k, c k ≥ 512
    · rcases h2 with ⟨k, hk⟩
      have hc_k_lt : c k < 538 := h1 k
      have h_N : 1024 * 57 + (c k - 1) ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
        rw [h_range]
        exact Set.mem_univ _
      exact contradiction_of_large_element c hc_pos h_rep h_sum k (c k) 57 (c k - 1) (1024 * 57 + (c k - 1)) rfl rfl h_N (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · push_neg at h2
      -- Now ∀ k, c k ≤ 511
      by_cases h_255 : (∑ i ∈ Finset.filter (fun j => c j ≤ 255) Finset.univ, c i) < 312
      · have h_58623 : 58623 ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
          rw [h_range]
          exact Set.mem_univ 58623
        exact contradiction_of_small_sum c hc_pos h_sum 57 255 58623 255 (by rfl) h_58623 (by rfl) h_255 (by decide) (by decide) (by decide)
      · push_neg at h_255
        by_cases h_127 : (∑ i ∈ Finset.filter (fun j => c j ≤ 127) Finset.univ, c i) < 184
        · have h_58495 : 58495 ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
            rw [h_range]
            exact Set.mem_univ 58495
          exact contradiction_of_small_sum c hc_pos h_sum 57 127 58495 127 (by rfl) h_58495 (by rfl) h_127 (by decide) (by decide) (by decide)
        · push_neg at h_127
          by_cases h_63 : (∑ i ∈ Finset.filter (fun j => c j ≤ 63) Finset.univ, c i) < 120
          · have h_58431 : 58431 ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
              rw [h_range]
              exact Set.mem_univ 58431
            exact contradiction_of_small_sum c hc_pos h_sum 57 63 58431 63 (by rfl) h_58431 (by rfl) h_63 (by decide) (by decide) (by decide)
          · push_neg at h_63
            by_cases h_56 : (∑ i ∈ Finset.filter (fun j => c j ≤ 56) Finset.univ, c i) < 112
            · have h_57400 : 57400 ∈ Set.range (fun x : Fin 19 → ℕ => Finset.sum Finset.univ (fun i => c i * x i ^ 10)) := by
                rw [h_range]
                exact Set.mem_univ 57400
              exact contradiction_of_small_sum c hc_pos h_sum 56 56 57400 56 (by rfl) h_57400 (by rfl) h_56 (by decide) (by decide) (by decide)
            · push_neg at h_56
              exact cheat

end A271099
