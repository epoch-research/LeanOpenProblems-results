import FormalConjectures.Util.ProblemImports

open Real

noncomputable def s : ℝ := goldenRatio
noncomputable def t : ℝ := 1 / s
noncomputable def r : ℝ := 5

lemma s_pos : 0 < s := goldenRatio_pos
lemma t_pos : 0 < t := by
  change 0 < 1 / goldenRatio
  exact one_div_pos.mpr goldenRatio_pos
lemma r_pos : 0 < r := by norm_num [r]

lemma s_irrational : Irrational s := goldenRatio_irrational

lemma r_div_s_irrational : Irrational (r / s) := by
  change Irrational (5 / goldenRatio)
  rw [div_eq_mul_inv]
  exact Irrational.intCast_mul goldenRatio_irrational.inv (by norm_num)

lemma r_div_t_irrational : Irrational (r / t) := by
  change Irrational (5 / (1 / goldenRatio))
  have : (5 / (1 / goldenRatio) : ℝ) = 5 * goldenRatio := by
    rw [div_div_eq_mul_div, div_one]
  rw [this]
  exact Irrational.intCast_mul goldenRatio_irrational (by norm_num)

lemma s_div_t_irrational : Irrational (s / t) := by
  change Irrational (goldenRatio / (1 / goldenRatio))
  have : (goldenRatio / (1 / goldenRatio) : ℝ) = goldenRatio ^ 2 := by
    rw [div_div_eq_mul_div, div_one]
    ring
  rw [this, goldenRatio_sq]
  have h_add : Irrational (goldenRatio + (1 : ℝ)) := by
    have h_cast : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_cast
    rw [h_cast]
    exact Irrational.add_natCast goldenRatio_irrational 1
  exact h_add

lemma rat_contradiction_r_s (i j : ℕ) (h : ((i : ℝ) + 1) / r = ((j : ℝ) + 1) / s) : False := by
  have h1 : (((i : ℝ) + 1) / 5) * (5 / ((j : ℝ) + 1)) = (((j : ℝ) + 1) / goldenRatio) * (5 / ((j : ℝ) + 1)) := by
    dsimp [r, s] at h
    rw [h]
  have h_lhs : (((i : ℝ) + 1) / 5) * (5 / ((j : ℝ) + 1)) = ((i : ℝ) + 1) / ((j : ℝ) + 1) := by
    ring
  have h_rhs : (((j : ℝ) + 1) / goldenRatio) * (5 / ((j : ℝ) + 1)) = 5 / goldenRatio := by
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hg : goldenRatio ≠ 0 := goldenRatio_ne_zero
    field_simp
  rw [h_lhs, h_rhs] at h1
  let q : ℚ := ((i : ℤ) + 1) / ((j : ℤ) + 1)
  have h_rat : (q : ℝ) = 5 / goldenRatio := by
    dsimp [q]
    push_cast
    exact h1
  have h_mem : (r / s) ∈ Set.range ((↑) : ℚ → ℝ) := by
    dsimp [r, s]
    exact ⟨q, h_rat⟩
  exact r_div_s_irrational h_mem

lemma rat_contradiction_r_t (i j : ℕ) (h : ((i : ℝ) + 1) / r = ((j : ℝ) + 1) / t) : False := by
  have h1 : (((i : ℝ) + 1) / 5) * (5 / ((j : ℝ) + 1)) = (((j : ℝ) + 1) / (1 / s)) * (5 / ((j : ℝ) + 1)) := by
    dsimp [r, t] at h
    change ((i : ℝ) + 1) / 5 = ((j : ℝ) + 1) / (1 / s) at h
    rw [h]
  have h_lhs : (((i : ℝ) + 1) / 5) * (5 / ((j : ℝ) + 1)) = ((i : ℝ) + 1) / ((j : ℝ) + 1) := by
    ring
  have h_rhs : (((j : ℝ) + 1) / (1 / s)) * (5 / ((j : ℝ) + 1)) = 5 / (1 / s) := by
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hg : (1 / s : ℝ) ≠ 0 := by
      exact one_div_ne_zero (ne_of_gt s_pos)
    field_simp
  rw [h_lhs, h_rhs] at h1
  let q : ℚ := ((i : ℤ) + 1) / ((j : ℤ) + 1)
  have h_rat : (q : ℝ) = 5 / (1 / s) := by
    dsimp [q]
    push_cast
    exact h1
  have h_mem : (r / t) ∈ Set.range ((↑) : ℚ → ℝ) := by
    dsimp [r, t]
    exact ⟨q, h_rat⟩
  exact r_div_t_irrational h_mem

lemma rat_contradiction_s_t (i j : ℕ) (h : ((i : ℝ) + 1) / s = ((j : ℝ) + 1) / t) : False := by
  have h1 : (((i : ℝ) + 1) / s) * (s / ((j : ℝ) + 1)) = (((j : ℝ) + 1) / (1 / s)) * (s / ((j : ℝ) + 1)) := by
    dsimp [t] at h
    rw [h]
  have h_lhs : (((i : ℝ) + 1) / s) * (s / ((j : ℝ) + 1)) = ((i : ℝ) + 1) / ((j : ℝ) + 1) := by
    have hs : s ≠ 0 := ne_of_gt s_pos
    field_simp
  have h_rhs : (((j : ℝ) + 1) / (1 / s)) * (s / ((j : ℝ) + 1)) = s / (1 / s) := by
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hg : (1 / s : ℝ) ≠ 0 := by
      exact one_div_ne_zero (ne_of_gt s_pos)
    field_simp
  rw [h_lhs, h_rhs] at h1
  let q : ℚ := ((i : ℤ) + 1) / ((j : ℤ) + 1)
  have h_rat : (q : ℝ) = s / (1 / s) := by
    dsimp [q]
    push_cast
    exact h1
  have h_mem : (s / t) ∈ Set.range ((↑) : ℚ → ℝ) := by
    dsimp [t]
    exact ⟨q, h_rat⟩
  exact s_div_t_irrational h_mem

/--
A207672: $a(n) = n + \\lfloor ns/r \\rfloor + \\lfloor nt/r \\rfloor$.
-/
noncomputable def A207672 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * s / r)
  let term2_int : ℤ := Int.floor (n_r * t / r)

  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

/--
A207673: $b(n) = n + \\lfloor nr/s \\rfloor + \\lfloor nt/s \\rfloor$.
-/
noncomputable def A207673 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * r / s)
  let term2_int : ℤ := Int.floor (n_r * t / s)

  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

/--
A208326: $c(n) = n + \\lfloor nr/t \\rfloor + \\lfloor ns/t \\rfloor$, where $\\lfloor \\cdot \\rfloor$ is the floor function, $r=5$, $s=(1+\\sqrt{5})/2$, and $t=1/s$.
-/
noncomputable def A208326 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * r / t)
  let term2_int : ℤ := Int.floor (n_r * s / t)

  -- Sum the components in ℤ and convert the final result back to ℕ.
  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

noncomputable def F (x : ℝ) : ℤ :=
  Int.floor (x * r) + Int.floor (x * s) + Int.floor (x * t)

lemma floor_mono {x y : ℝ} (h : x ≤ y) : Int.floor x ≤ Int.floor y :=
  Int.floor_le_floor h

lemma floor_lt_of_lt_int {x : ℝ} {k : ℤ} (h : x < k) : Int.floor x < k :=
  Int.floor_lt.mpr h

lemma F_lt_of_lt_of_int_s {u v : ℝ} (huv : u < v) (k : ℤ) (hk : v * s = k) : F u < F v := by
  dsimp [F]
  have h1 : Int.floor (u * r) ≤ Int.floor (v * r) := floor_mono (mul_le_mul_of_nonneg_right huv.le r_pos.le)
  have h2 : Int.floor (u * s) < Int.floor (v * s) := by
    have : u * s < k := by
      rw [← hk]
      exact mul_lt_mul_of_pos_right huv s_pos
    have h_lt : Int.floor (u * s) < k := floor_lt_of_lt_int this
    have h_eq : Int.floor (v * s) = k := by
      rw [hk, Int.floor_intCast]
    rwa [h_eq]
  have h3 : Int.floor (u * t) ≤ Int.floor (v * t) := floor_mono (mul_le_mul_of_nonneg_right huv.le t_pos.le)
  linarith

lemma F_lt_of_lt_of_int_r {u v : ℝ} (huv : u < v) (k : ℤ) (hk : v * r = k) : F u < F v := by
  dsimp [F]
  have h1 : Int.floor (u * r) < Int.floor (v * r) := by
    have : u * r < k := by
      rw [← hk]
      exact mul_lt_mul_of_pos_right huv r_pos
    have h_lt : Int.floor (u * r) < k := floor_lt_of_lt_int this
    have h_eq : Int.floor (v * r) = k := by
      rw [hk, Int.floor_intCast]
    rwa [h_eq]
  have h2 : Int.floor (u * s) ≤ Int.floor (v * s) := floor_mono (mul_le_mul_of_nonneg_right huv.le s_pos.le)
  have h3 : Int.floor (u * t) ≤ Int.floor (v * t) := floor_mono (mul_le_mul_of_nonneg_right huv.le t_pos.le)
  linarith

lemma F_lt_of_lt_of_int_t {u v : ℝ} (huv : u < v) (k : ℤ) (hk : v * t = k) : F u < F v := by
  dsimp [F]
  have h1 : Int.floor (u * r) ≤ Int.floor (v * r) := floor_mono (mul_le_mul_of_nonneg_right huv.le r_pos.le)
  have h2 : Int.floor (u * s) ≤ Int.floor (v * s) := floor_mono (mul_le_mul_of_nonneg_right huv.le s_pos.le)
  have h3 : Int.floor (u * t) < Int.floor (v * t) := by
    have : u * t < k := by
      rw [← hk]
      exact mul_lt_mul_of_pos_right huv t_pos
    have h_lt : Int.floor (u * t) < k := floor_lt_of_lt_int this
    have h_eq : Int.floor (v * t) = k := by
      rw [hk, Int.floor_intCast]
    rwa [h_eq]
  linarith

lemma F_inj {u v : ℝ}
  (hu : ∃ (k : ℤ), u * r = k ∨ u * s = k ∨ u * t = k)
  (hv : ∃ (k : ℤ), v * r = k ∨ v * s = k ∨ v * t = k)
  (h_eq : F u = F v) : u = v := by
  rcases lt_trichotomy u v with h | rfl | h
  · rcases hv with ⟨k, h_or⟩
    rcases h_or with hk | hk | hk
    · have := F_lt_of_lt_of_int_r h k hk
      linarith
    · have := F_lt_of_lt_of_int_s h k hk
      linarith
    · have := F_lt_of_lt_of_int_t h k hk
      linarith
  · rfl
  · rcases hu with ⟨k, h_or⟩
    rcases h_or with hk | hk | hk
    · have := F_lt_of_lt_of_int_r h k hk
      linarith
    · have := F_lt_of_lt_of_int_s h k hk
      linarith
    · have := F_lt_of_lt_of_int_t h k hk
      linarith

lemma A207672_eq_F (n : ℕ) : (A207672 n : ℤ) = F (n / r) := by
  dsimp [A207672, F, r, s, t]
  have h_mul1 : ((n : ℝ) / 5) * 5 = (n : ℝ) := by
    exact div_mul_cancel₀ (n : ℝ) (by norm_num)
  have h_mul2 : ((n : ℝ) / 5) * goldenRatio = (n : ℝ) * goldenRatio / 5 := by
    ring
  have h_mul3 : ((n : ℝ) / 5) * (1 / goldenRatio) = (n : ℝ) * (1 / goldenRatio) / 5 := by
    ring
  rw [h_mul1, h_mul2, h_mul3]
  have h_pos : 0 ≤ (n : ℤ) + Int.floor ((n : ℝ) * goldenRatio / 5) + Int.floor ((n : ℝ) * (1 / goldenRatio) / 5) := by
    have f1 : 0 ≤ Int.floor ((n : ℝ) * goldenRatio / 5) := by
      apply Int.floor_nonneg.mpr
      apply div_nonneg
      · exact mul_nonneg (by positivity) s_pos.le
      · norm_num
    have f2 : 0 ≤ Int.floor ((n : ℝ) * (1 / goldenRatio) / 5) := by
      apply Int.floor_nonneg.mpr
      apply div_nonneg
      · exact mul_nonneg (by positivity) t_pos.le
      · norm_num
    linarith
  rw [Int.toNat_of_nonneg h_pos]
  simp only [Int.floor_natCast]

lemma A207673_eq_F (n : ℕ) : (A207673 n : ℤ) = F (n / s) := by
  dsimp [A207673, F, r, s, t]
  have h_mul1 : ((n : ℝ) / goldenRatio) * 5 = (n : ℝ) * 5 / goldenRatio := by
    ring
  have h_mul2 : ((n : ℝ) / goldenRatio) * goldenRatio = (n : ℝ) := by
    exact div_mul_cancel₀ (n : ℝ) goldenRatio_ne_zero
  have h_mul3 : ((n : ℝ) / goldenRatio) * (1 / goldenRatio) = (n : ℝ) * (1 / goldenRatio) / goldenRatio := by
    ring
  rw [h_mul1, h_mul2, h_mul3]
  have h_pos : 0 ≤ (n : ℤ) + Int.floor ((n : ℝ) * 5 / goldenRatio) + Int.floor ((n : ℝ) * (1 / goldenRatio) / goldenRatio) := by
    have f1 : 0 ≤ Int.floor ((n : ℝ) * 5 / goldenRatio) := by
      apply Int.floor_nonneg.mpr
      apply div_nonneg
      · exact mul_nonneg (by positivity) (by norm_num)
      · exact goldenRatio_pos.le
    have f2 : 0 ≤ Int.floor ((n : ℝ) * (1 / goldenRatio) / goldenRatio) := by
      apply Int.floor_nonneg.mpr
      apply div_nonneg
      · exact mul_nonneg (by positivity) t_pos.le
      · exact goldenRatio_pos.le
    linarith
  rw [Int.toNat_of_nonneg h_pos]
  simp only [Int.floor_natCast]
  ring

lemma A208326_eq_F (n : ℕ) : (A208326 n : ℤ) = F (n / t) := by
  dsimp [A208326, F, r, s, t]
  have h_mul1 : ((n : ℝ) / (1 / goldenRatio)) * 5 = (n : ℝ) * 5 / (1 / goldenRatio) := by
    ring
  have h_mul2 : ((n : ℝ) / (1 / goldenRatio)) * goldenRatio = (n : ℝ) * goldenRatio / (1 / goldenRatio) := by
    ring
  have h_mul3 : ((n : ℝ) / (1 / goldenRatio)) * (1 / goldenRatio) = (n : ℝ) := by
    exact div_mul_cancel₀ (n : ℝ) (by
      intro h
      have : (1 / goldenRatio : ℝ) = 0 := h
      have : (0 : ℝ) < 1 / goldenRatio := by exact one_div_pos.mpr goldenRatio_pos
      linarith)
  rw [h_mul1, h_mul2, h_mul3]
  have h_pos : 0 ≤ (n : ℤ) + Int.floor ((n : ℝ) * 5 / (1 / goldenRatio)) + Int.floor ((n : ℝ) * goldenRatio / (1 / goldenRatio)) := by
    have f1 : 0 ≤ Int.floor ((n : ℝ) * 5 / (1 / goldenRatio)) := by
      apply Int.floor_nonneg.mpr
      apply div_nonneg
      · exact mul_nonneg (by positivity) (by norm_num)
      · exact t_pos.le
    have f2 : 0 ≤ Int.floor ((n : ℝ) * goldenRatio / (1 / goldenRatio)) := by
      apply Int.floor_nonneg.mpr
      apply div_nonneg
      · exact mul_nonneg (by positivity) goldenRatio_pos.le
      · exact t_pos.le
    linarith
  rw [Int.toNat_of_nonneg h_pos]
  simp only [Int.floor_natCast]
  ring

lemma range_disjoint_A207672_A207673 : Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A207673 ∘ Nat.succ) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  dsimp at hi hj
  have h_eq : (A207672 (i + 1) : ℤ) = (A207673 (j + 1) : ℤ) := by rw [hi, hj]
  rw [A207672_eq_F, A207673_eq_F] at h_eq
  push_cast at h_eq
  have hu : ∃ (k : ℤ), ((i : ℝ) + 1) / r * r = k ∨ ((i : ℝ) + 1) / r * s = k ∨ ((i : ℝ) + 1) / r * t = k := by
    refine ⟨i + 1, ?_⟩
    left
    push_cast
    exact div_mul_cancel₀ ((i : ℝ) + 1) (by norm_num [r])
  have hv : ∃ (k : ℤ), ((j : ℝ) + 1) / s * r = k ∨ ((j : ℝ) + 1) / s * s = k ∨ ((j : ℝ) + 1) / s * t = k := by
    refine ⟨j + 1, ?_⟩
    right; left
    push_cast
    exact div_mul_cancel₀ ((j : ℝ) + 1) goldenRatio_ne_zero
  have h_inj := F_inj hu hv h_eq
  exact rat_contradiction_r_s i j h_inj

lemma range_disjoint_A207672_A208326 : Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  dsimp at hi hj
  have h_eq : (A207672 (i + 1) : ℤ) = (A208326 (j + 1) : ℤ) := by rw [hi, hj]
  rw [A207672_eq_F, A208326_eq_F] at h_eq
  push_cast at h_eq
  have hu : ∃ (k : ℤ), ((i : ℝ) + 1) / r * r = k ∨ ((i : ℝ) + 1) / r * s = k ∨ ((i : ℝ) + 1) / r * t = k := by
    refine ⟨i + 1, ?_⟩
    left
    push_cast
    exact div_mul_cancel₀ ((i : ℝ) + 1) (by norm_num [r])
  have hv : ∃ (k : ℤ), ((j : ℝ) + 1) / t * r = k ∨ ((j : ℝ) + 1) / t * s = k ∨ ((j : ℝ) + 1) / t * t = k := by
    refine ⟨j + 1, ?_⟩
    right; right
    dsimp [t]
    push_cast
    exact div_mul_cancel₀ ((j : ℝ) + 1) (by exact one_div_ne_zero goldenRatio_ne_zero)
  have h_inj := F_inj hu hv h_eq
  exact rat_contradiction_r_t i j h_inj

lemma range_disjoint_A207673_A208326 : Set.range (A207673 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  dsimp at hi hj
  have h_eq : (A207673 (i + 1) : ℤ) = (A208326 (j + 1) : ℤ) := by rw [hi, hj]
  rw [A207673_eq_F, A208326_eq_F] at h_eq
  push_cast at h_eq
  have hu : ∃ (k : ℤ), ((i : ℝ) + 1) / s * r = k ∨ ((i : ℝ) + 1) / s * s = k ∨ ((i : ℝ) + 1) / s * t = k := by
    refine ⟨i + 1, ?_⟩
    right; left
    push_cast
    exact div_mul_cancel₀ ((i : ℝ) + 1) goldenRatio_ne_zero
  have hv : ∃ (k : ℤ), ((j : ℝ) + 1) / t * r = k ∨ ((j : ℝ) + 1) / t * s = k ∨ ((j : ℝ) + 1) / t * t = k := by
    refine ⟨j + 1, ?_⟩
    right; right
    dsimp [t]
    push_cast
    exact div_mul_cancel₀ ((j : ℝ) + 1) (by exact one_div_ne_zero goldenRatio_ne_zero)
  have h_inj := F_inj hu hv h_eq
  exact rat_contradiction_s_t i j h_inj

lemma F_mono {x y : ℝ} (h : x ≤ y) : F x ≤ F y := by
  dsimp [F]
  have h1 : Int.floor (x * r) ≤ Int.floor (y * r) := floor_mono (mul_le_mul_of_nonneg_right h r_pos.le)
  have h2 : Int.floor (x * s) ≤ Int.floor (y * s) := floor_mono (mul_le_mul_of_nonneg_right h s_pos.le)
  have h3 : Int.floor (x * t) ≤ Int.floor (y * t) := floor_mono (mul_le_mul_of_nonneg_right h t_pos.le)
  linarith

lemma lt_of_F_lt {u v : ℝ} (h : F u < F v) : u < v := by
  by_contra! h_le
  have := F_mono h_le
  linarith

lemma A207672_pos (n : ℕ) (hn : 0 < n) : 0 < A207672 n := by
  have h_eq := A207672_eq_F n
  have h_ge : (1 : ℤ) ≤ F (n / r) := by
    dsimp [F]
    have f1 : (1 : ℤ) ≤ Int.floor (((n : ℝ) / r) * r) := by
      change (1 : ℤ) ≤ Int.floor (((n : ℝ) / 5) * 5)
      rw [div_mul_cancel₀ (n : ℝ) (by norm_num)]
      simp; exact hn
    have f2 : 0 ≤ Int.floor (((n : ℝ) / r) * s) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) r_pos.le
      · exact s_pos.le
    have f3 : 0 ≤ Int.floor (((n : ℝ) / r) * t) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) r_pos.le
      · exact t_pos.le
    linarith
  rw [← h_eq] at h_ge
  exact_mod_cast h_ge

lemma A207673_pos (n : ℕ) (hn : 0 < n) : 0 < A207673 n := by
  have h_eq := A207673_eq_F n
  have h_ge : (1 : ℤ) ≤ F (n / s) := by
    dsimp [F]
    have f1 : 0 ≤ Int.floor (((n : ℝ) / s) * r) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) s_pos.le
      · exact r_pos.le
    have f2 : (1 : ℤ) ≤ Int.floor (((n : ℝ) / s) * s) := by
      change (1 : ℤ) ≤ Int.floor (((n : ℝ) / goldenRatio) * goldenRatio)
      rw [div_mul_cancel₀ (n : ℝ) goldenRatio_ne_zero]
      simp; exact hn
    have f3 : 0 ≤ Int.floor (((n : ℝ) / s) * t) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) s_pos.le
      · exact t_pos.le
    linarith
  rw [← h_eq] at h_ge
  exact_mod_cast h_ge

lemma A208326_pos (n : ℕ) (hn : 0 < n) : 0 < A208326 n := by
  have h_eq := A208326_eq_F n
  have h_ge : (1 : ℤ) ≤ F (n / t) := by
    dsimp [F]
    have f1 : 0 ≤ Int.floor (((n : ℝ) / t) * r) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) t_pos.le
      · exact r_pos.le
    have f2 : 0 ≤ Int.floor (((n : ℝ) / t) * s) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) t_pos.le
      · exact s_pos.le
    have f3 : (1 : ℤ) ≤ Int.floor (((n : ℝ) / t) * t) := by
      change (1 : ℤ) ≤ Int.floor (((n : ℝ) / (1 / goldenRatio)) * (1 / goldenRatio))
      rw [div_mul_cancel₀ (n : ℝ) (one_div_ne_zero goldenRatio_ne_zero)]
      simp; exact hn
    linarith
  rw [← h_eq] at h_ge
  exact_mod_cast h_ge

lemma A207672_ge (n : ℕ) : A207672 n ≥ n := by
  have h_eq := A207672_eq_F n
  have h_ge : (n : ℤ) ≤ F (n / r) := by
    dsimp [F]
    have f2 : 0 ≤ Int.floor (((n : ℝ) / r) * s) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) r_pos.le
      · exact s_pos.le
    have f3 : 0 ≤ Int.floor (((n : ℝ) / r) * t) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) r_pos.le
      · exact t_pos.le
    have h_cancel : ((n : ℝ) / r) * r = n := by
      change ((n : ℝ) / 5) * 5 = n
      rw [div_mul_cancel₀ (n : ℝ) (by norm_num)]
    have f1 : Int.floor (((n : ℝ) / r) * r) = (n : ℤ) := by
      rw [h_cancel]
      simp
    linarith
  rw [← h_eq] at h_ge
  exact_mod_cast h_ge

lemma A207673_ge (n : ℕ) : A207673 n ≥ n := by
  have h_eq := A207673_eq_F n
  have h_ge : (n : ℤ) ≤ F (n / s) := by
    dsimp [F]
    have f1 : 0 ≤ Int.floor (((n : ℝ) / s) * r) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) s_pos.le
      · exact r_pos.le
    have f3 : 0 ≤ Int.floor (((n : ℝ) / s) * t) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) s_pos.le
      · exact t_pos.le
    have h_cancel : ((n : ℝ) / s) * s = n := by
      exact div_mul_cancel₀ (n : ℝ) (ne_of_gt s_pos)
    have f2 : Int.floor (((n : ℝ) / s) * s) = (n : ℤ) := by
      rw [h_cancel]
      simp
    linarith
  rw [← h_eq] at h_ge
  exact_mod_cast h_ge

lemma A208326_ge (n : ℕ) : A208326 n ≥ n := by
  have h_eq := A208326_eq_F n
  have h_ge : (n : ℤ) ≤ F (n / t) := by
    dsimp [F]
    have f1 : 0 ≤ Int.floor (((n : ℝ) / t) * r) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) t_pos.le
      · exact r_pos.le
    have f2 : 0 ≤ Int.floor (((n : ℝ) / t) * s) := by
      apply Int.floor_nonneg.mpr
      apply mul_nonneg
      · apply div_nonneg (by positivity) t_pos.le
      · exact s_pos.le
    have h_cancel : ((n : ℝ) / t) * t = n := by
      exact div_mul_cancel₀ (n : ℝ) (ne_of_gt t_pos)
    have f3 : Int.floor (((n : ℝ) / t) * t) = (n : ℤ) := by
      rw [h_cancel]
      simp
    linarith
  rw [← h_eq] at h_ge
  exact_mod_cast h_ge

lemma A207672_zero : A207672 0 = 0 := by
  have : (A207672 0 : ℤ) = F 0 := by
    rw [A207672_eq_F 0]
    congr 1
    ring
  have h_f0 : F 0 = 0 := by dsimp [F]; simp
  rw [h_f0] at this
  exact_mod_cast this

lemma A207673_zero : A207673 0 = 0 := by
  have : (A207673 0 : ℤ) = F 0 := by
    rw [A207673_eq_F 0]
    congr 1
    ring
  have h_f0 : F 0 = 0 := by dsimp [F]; simp
  rw [h_f0] at this
  exact_mod_cast this

lemma A208326_zero : A208326 0 = 0 := by
  have : (A208326 0 : ℤ) = F 0 := by
    rw [A208326_eq_F 0]
    congr 1
    ring
  have h_f0 : F 0 = 0 := by dsimp [F]; simp
  rw [h_f0] at this
  exact_mod_cast this


lemma oeis_208326_conjecture_0_coverage : ({n : ℕ | 0 < n} : Set ℕ) ⊆
    (Set.range (A207672 ∘ Nat.succ)) ∪
    (Set.range (A207673 ∘ Nat.succ)) ∪
    (Set.range (A208326 ∘ Nat.succ)) := by
  intro y hy
  dsimp at hy
  induction y using Nat.strong_induction_on with
  | h y h_ind =>
    have h_ex_a : ∃ n, A207672 n ≥ y := ⟨y, A207672_ge y⟩
    have h_ex_b : ∃ n, A207673 n ≥ y := ⟨y, A207673_ge y⟩
    have h_ex_c : ∃ n, A208326 n ≥ y := ⟨y, A208326_ge y⟩
    let m_a := Nat.find h_ex_a
    let m_b := Nat.find h_ex_b
    let m_c := Nat.find h_ex_c
    have hm_a_pos : 0 < m_a := by
      by_contra! hm
      have h_spec := Nat.find_spec h_ex_a
      have : m_a = 0 := by omega
      change A207672 m_a ≥ y at h_spec
      rw [this, A207672_zero] at h_spec
      omega
    have hm_b_pos : 0 < m_b := by
      by_contra! hm
      have h_spec := Nat.find_spec h_ex_b
      have : m_b = 0 := by omega
      change A207673 m_b ≥ y at h_spec
      rw [this, A207673_zero] at h_spec
      omega
    have hm_c_pos : 0 < m_c := by
      by_contra! hm
      have h_spec := Nat.find_spec h_ex_c
      have : m_c = 0 := by omega
      change A208326 m_c ≥ y at h_spec
      rw [this, A208326_zero] at h_spec
      omega
    let n_a := m_a - 1
    let n_b := m_b - 1
    let n_c := m_c - 1
    have hma : m_a = n_a + 1 := (Nat.sub_add_cancel hm_a_pos).symm
    have hmb : m_b = n_b + 1 := (Nat.sub_add_cancel hm_b_pos).symm
    have hmc : m_c = n_c + 1 := (Nat.sub_add_cancel hm_c_pos).symm

    let v_a := ((n_a : ℝ) + 1) / r
    let v_b := ((n_b : ℝ) + 1) / s
    let v_c := ((n_c : ℝ) + 1) / t

    have h_spec_a : A207672 (n_a + 1) ≥ y := by
      have := Nat.find_spec h_ex_a
      rwa [← hma]
    have h_spec_b : A207673 (n_b + 1) ≥ y := by
      have := Nat.find_spec h_ex_b
      rwa [← hmb]
    have h_spec_c : A208326 (n_c + 1) ≥ y := by
      have := Nat.find_spec h_ex_c
      rwa [← hmc]

    have h_cases : (v_a ≤ v_b ∧ v_a ≤ v_c) ∨ (v_b ≤ v_a ∧ v_b ≤ v_c) ∨ (v_c ≤ v_a ∧ v_c ≤ v_b) := by
      rcases le_total v_a v_b with h1 | h1
      · rcases le_total v_a v_c with h2 | h2
        · left; exact ⟨h1, h2⟩
        · right; right; exact ⟨h2, h2.trans h1⟩
      · rcases le_total v_b v_c with h2 | h2
        · right; left; exact ⟨h1, h2⟩
        · right; right; exact ⟨h2.trans h1, h2⟩

    rcases h_cases with ⟨hab, hac⟩ | ⟨hab, hbc⟩ | ⟨hac, hbc⟩
    · -- Case 1: v_a ≤ v_b and v_a ≤ v_c
      left; left
      rw [Set.mem_range]
      refine ⟨n_a, ?_⟩
      dsimp
      have h_ab : v_a < v_b := by
        rcases hab.lt_or_eq with h | h
        · exact h
        · exfalso; exact rat_contradiction_r_s n_a n_b h
      have h_ac : v_a < v_c := by
        rcases hac.lt_or_eq with h | h
        · exact h
        · exfalso; exact rat_contradiction_r_t n_a n_c h
      have h1 : v_a * s < n_b + 1 := by
        rwa [lt_div_iff₀ s_pos] at h_ab
      have h1_floor : Int.floor (v_a * s) ≤ n_b := by
        have : Int.floor (v_a * s) < (n_b : ℤ) + 1 := by
          rw [Int.floor_lt]
          exact_mod_cast h1
        omega
      have h2 : v_a * t < n_c + 1 := by
        rwa [lt_div_iff₀ t_pos] at h_ac
      have h2_floor : Int.floor (v_a * t) ≤ n_c := by
        have : Int.floor (v_a * t) < (n_c : ℤ) + 1 := by
          rw [Int.floor_lt]
          exact_mod_cast h2
        omega
      have h3_floor : (n_b : ℤ) ≤ Int.floor (v_a * s) := by
        by_cases hn_b : n_b = 0
        · rw [hn_b]
          have : 0 ≤ v_a * s := mul_nonneg (div_nonneg (by positivity) r_pos.le) s_pos.le
          exact Int.floor_nonneg.mpr this
        · have hn_b_pos : 0 < n_b := by omega
          have h_lt : A207673 n_b < y := by
            have : ¬ A207673 n_b ≥ y := Nat.find_min h_ex_b (by omega : n_b < m_b)
            omega
          have h_comp : (A207673 n_b : ℤ) < (A207672 (n_a + 1) : ℤ) := by linarith [h_spec_a]
          rw [A207673_eq_F, A207672_eq_F] at h_comp
          push_cast at h_comp
          have h_comp_lt := lt_of_F_lt h_comp
          have : (n_b : ℝ) < v_a * s := (div_lt_iff₀ s_pos).mp h_comp_lt
          exact Int.le_floor.mpr this.le
      have h4_floor : (n_c : ℤ) ≤ Int.floor (v_a * t) := by
        by_cases hn_c : n_c = 0
        · rw [hn_c]
          have : 0 ≤ v_a * t := mul_nonneg (div_nonneg (by positivity) r_pos.le) t_pos.le
          exact Int.floor_nonneg.mpr this
        · have hn_c_pos : 0 < n_c := by omega
          have h_lt : A208326 n_c < y := by
            have : ¬ A208326 n_c ≥ y := Nat.find_min h_ex_c (by omega : n_c < m_c)
            omega
          have h_comp : (A208326 n_c : ℤ) < (A207672 (n_a + 1) : ℤ) := by linarith [h_spec_a]
          rw [A208326_eq_F, A207672_eq_F] at h_comp
          push_cast at h_comp
          have h_comp_lt := lt_of_F_lt h_comp
          have : (n_c : ℝ) < v_a * t := (div_lt_iff₀ t_pos).mp h_comp_lt
          exact Int.le_floor.mpr this.le
      have h_eq_s : Int.floor (v_a * s) = n_b := by omega
      have h_eq_t : Int.floor (v_a * t) = n_c := by omega
      have h_eq_r : Int.floor (v_a * r) = n_a + 1 := by
        change Int.floor (((n_a : ℝ) + 1) / 5 * 5) = n_a + 1
        rw [div_mul_cancel₀ ((n_a : ℝ) + 1) (by norm_num)]
        simp
      have h_sum : F v_a = n_a + 1 + n_b + n_c := by
        dsimp [F]
        rw [h_eq_r, h_eq_s, h_eq_t]

      let u := max (n_a / r) (max (n_b / s) (n_c / t))
      have hu_r : n_a / r ≤ u := le_max_left _ _
      have hu_s : n_b / s ≤ u := by
        have : n_b / s ≤ max (n_b / s) (n_c / t) := le_max_left _ _
        exact this.trans (le_max_right _ _)
      have hu_t : n_c / t ≤ u := by
        have : n_c / t ≤ max (n_b / s) (n_c / t) := le_max_right _ _
        exact this.trans (le_max_right _ _)

      have hu_lt : u < v_a := by
        rw [max_lt_iff]
        refine ⟨?_, ?_⟩
        · change (n_a : ℝ) / 5 < ((n_a : ℝ) + 1) / 5
          linarith
        · rw [max_lt_iff]
          refine ⟨?_, ?_⟩
          · by_cases hn_b : n_b = 0
            · rw [hn_b]
              norm_num
              exact div_pos (by positivity) r_pos
            · have hn_b_pos : 0 < n_b := by omega
              have h_lt : A207673 n_b < y := by
                have : ¬ A207673 n_b ≥ y := Nat.find_min h_ex_b (by omega : n_b < m_b)
                omega
              have h_comp : (A207673 n_b : ℤ) < (A207672 (n_a + 1) : ℤ) := by linarith [h_spec_a]
              rw [A207673_eq_F, A207672_eq_F] at h_comp
              push_cast at h_comp
              exact lt_of_F_lt h_comp
          · by_cases hn_c : n_c = 0
            · rw [hn_c]
              norm_num
              exact div_pos (by positivity) r_pos
            · have hn_c_pos : 0 < n_c := by omega
              have h_lt : A208326 n_c < y := by
                have : ¬ A208326 n_c ≥ y := Nat.find_min h_ex_c (by omega : n_c < m_c)
                omega
              have h_comp : (A208326 n_c : ℤ) < (A207672 (n_a + 1) : ℤ) := by linarith [h_spec_a]
              rw [A208326_eq_F, A207672_eq_F] at h_comp
              push_cast at h_comp
              exact lt_of_F_lt h_comp

      have h_fu : F u = n_a + n_b + n_c := by
        dsimp [F]
        have f1 : Int.floor (u * r) = n_a := by
          have l1 : u * r < n_a + 1 := by
            rwa [lt_div_iff₀ r_pos] at hu_lt
          have l2 : (n_a : ℝ) ≤ u * r := by
            rwa [div_le_iff₀ r_pos] at hu_r
          have l1_f : Int.floor (u * r) < n_a + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_a ≤ Int.floor (u * r) := by
            have : (n_a : ℝ) ≤ u * r := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        have f2 : Int.floor (u * s) = n_b := by
          have l1 : u * s < n_b + 1 := by
            have : u < v_a := hu_lt
            have : u < v_b := this.trans h_ab
            rwa [lt_div_iff₀ s_pos] at this
          have l2 : (n_b : ℝ) ≤ u * s := by
            rwa [div_le_iff₀ s_pos] at hu_s
          have l1_f : Int.floor (u * s) < n_b + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_b ≤ Int.floor (u * s) := by
            have : (n_b : ℝ) ≤ u * s := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        have f3 : Int.floor (u * t) = n_c := by
          have l1 : u * t < n_c + 1 := by
            have : u < v_a := hu_lt
            have : u < v_c := this.trans h_ac
            rwa [lt_div_iff₀ t_pos] at this
          have l2 : (n_c : ℝ) ≤ u * t := by
            rwa [div_le_iff₀ t_pos] at hu_t
          have l1_f : Int.floor (u * t) < n_c + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_c ≤ Int.floor (u * t) := by
            have : (n_c : ℝ) ≤ u * t := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        omega

      have h_fu_lt : F u < y := by
        have h_cases : u = n_a / r ∨ u = n_b / s ∨ u = n_c / t := by
          dsimp [u]
          rcases le_total (n_a / r) (max (n_b / s) (n_c / t)) with h | h
          · rw [max_eq_right h]
            rcases le_total (n_b / s) (n_c / t) with h2 | h2
            · rw [max_eq_right h2]
              right; right; rfl
            · rw [max_eq_left h2]
              right; left; rfl
          · rw [max_eq_left h]
            left; rfl
        rcases h_cases with hu_eq | hu_eq | hu_eq
        · rw [hu_eq]
          by_cases hn_a : n_a = 0
          · rw [hn_a]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_a_pos : 0 < n_a := by omega
            have h_lt : A207672 n_a < y := by
              have : ¬ A207672 n_a ≥ y := Nat.find_min h_ex_a (by omega : n_a < m_a)
              omega
            have h_lt_cast : (A207672 n_a : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A207672_eq_F] at h_lt_cast
            exact h_lt_cast
        · rw [hu_eq]
          by_cases hn_b : n_b = 0
          · rw [hn_b]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_b_pos : 0 < n_b := by omega
            have h_lt : A207673 n_b < y := by
              have : ¬ A207673 n_b ≥ y := Nat.find_min h_ex_b (by omega : n_b < m_b)
              omega
            have h_lt_cast : (A207673 n_b : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A207673_eq_F] at h_lt_cast
            exact h_lt_cast
        · rw [hu_eq]
          by_cases hn_c : n_c = 0
          · rw [hn_c]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_c_pos : 0 < n_c := by omega
            have h_lt : A208326 n_c < y := by
              have : ¬ A208326 n_c ≥ y := Nat.find_min h_ex_c (by omega : n_c < m_c)
              omega
            have h_lt_cast : (A208326 n_c : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A208326_eq_F] at h_lt_cast
            exact h_lt_cast

      have h_final : (A207672 (n_a + 1) : ℤ) = y := by
        have h_spec_a_cast : (A207672 (n_a + 1) : ℤ) ≥ (y : ℤ) := by exact_mod_cast h_spec_a
        rw [A207672_eq_F]
        rw [A207672_eq_F] at h_spec_a_cast
        push_cast at h_spec_a_cast
        push_cast
        linarith
      exact_mod_cast h_final

    · -- Case 2: v_b ≤ v_a and v_b ≤ v_c
      left; right
      rw [Set.mem_range]
      refine ⟨n_b, ?_⟩
      dsimp
      have h_ba : v_b < v_a := by
        rcases hab.lt_or_eq with h | h
        · exact h
        · exfalso; exact rat_contradiction_r_s n_a n_b h.symm
      have h_bc : v_b < v_c := by
        rcases hbc.lt_or_eq with h | h
        · exact h
        · exfalso; exact rat_contradiction_s_t n_b n_c h
      have h1 : v_b * r < n_a + 1 := by
        rwa [lt_div_iff₀ r_pos] at h_ba
      have h1_floor : Int.floor (v_b * r) ≤ n_a := by
        have : Int.floor (v_b * r) < (n_a : ℤ) + 1 := by
          rw [Int.floor_lt]
          exact_mod_cast h1
        omega
      have h2 : v_b * t < n_c + 1 := by
        rwa [lt_div_iff₀ t_pos] at h_bc
      have h2_floor : Int.floor (v_b * t) ≤ n_c := by
        have : Int.floor (v_b * t) < (n_c : ℤ) + 1 := by
          rw [Int.floor_lt]
          exact_mod_cast h2
        omega
      have h3_floor : (n_a : ℤ) ≤ Int.floor (v_b * r) := by
        by_cases hn_a : n_a = 0
        · rw [hn_a]
          have : 0 ≤ v_b * r := mul_nonneg (div_nonneg (by positivity) s_pos.le) r_pos.le
          exact Int.floor_nonneg.mpr this
        · have hn_a_pos : 0 < n_a := by omega
          have h_lt : A207672 n_a < y := by
            have : ¬ A207672 n_a ≥ y := Nat.find_min h_ex_a (by omega : n_a < m_a)
            omega
          have h_comp : (A207672 n_a : ℤ) < (A207673 (n_b + 1) : ℤ) := by linarith [h_spec_b]
          rw [A207672_eq_F, A207673_eq_F] at h_comp
          push_cast at h_comp
          have h_comp_lt := lt_of_F_lt h_comp
          have : (n_a : ℝ) < v_b * r := (div_lt_iff₀ r_pos).mp h_comp_lt
          exact Int.le_floor.mpr this.le
      have h4_floor : (n_c : ℤ) ≤ Int.floor (v_b * t) := by
        by_cases hn_c : n_c = 0
        · rw [hn_c]
          have : 0 ≤ v_b * t := mul_nonneg (div_nonneg (by positivity) s_pos.le) t_pos.le
          exact Int.floor_nonneg.mpr this
        · have hn_c_pos : 0 < n_c := by omega
          have h_lt : A208326 n_c < y := by
            have : ¬ A208326 n_c ≥ y := Nat.find_min h_ex_c (by omega : n_c < m_c)
            omega
          have h_comp : (A208326 n_c : ℤ) < (A207673 (n_b + 1) : ℤ) := by linarith [h_spec_b]
          rw [A208326_eq_F, A207673_eq_F] at h_comp
          push_cast at h_comp
          have h_comp_lt := lt_of_F_lt h_comp
          have : (n_c : ℝ) < v_b * t := (div_lt_iff₀ t_pos).mp h_comp_lt
          exact Int.le_floor.mpr this.le
      have h_eq_r : Int.floor (v_b * r) = n_a := by omega
      have h_eq_t : Int.floor (v_b * t) = n_c := by omega
      have h_eq_s : Int.floor (v_b * s) = n_b + 1 := by
        change Int.floor (((n_b : ℝ) + 1) / goldenRatio * goldenRatio) = n_b + 1
        rw [div_mul_cancel₀ ((n_b : ℝ) + 1) goldenRatio_ne_zero]
        simp
      have h_sum : F v_b = n_a + (n_b + 1) + n_c := by
        dsimp [F]
        rw [h_eq_r, h_eq_s, h_eq_t]

      let u := max (n_a / r) (max (n_b / s) (n_c / t))
      have hu_r : n_a / r ≤ u := le_max_left _ _
      have hu_s : n_b / s ≤ u := by
        have : n_b / s ≤ max (n_b / s) (n_c / t) := le_max_left _ _
        exact this.trans (le_max_right _ _)
      have hu_t : n_c / t ≤ u := by
        have : n_c / t ≤ max (n_b / s) (n_c / t) := le_max_right _ _
        exact this.trans (le_max_right _ _)

      have hu_lt : u < v_b := by
        rw [max_lt_iff]
        refine ⟨?_, ?_⟩
        · by_cases hn_a : n_a = 0
          · rw [hn_a]
            norm_num
            exact div_pos (by positivity) s_pos
          · have hn_a_pos : 0 < n_a := by omega
            have h_lt : A207672 n_a < y := by
              have : ¬ A207672 n_a ≥ y := Nat.find_min h_ex_a (by omega : n_a < m_a)
              omega
            have h_comp : (A207672 n_a : ℤ) < (A207673 (n_b + 1) : ℤ) := by linarith [h_spec_b]
            rw [A207672_eq_F, A207673_eq_F] at h_comp
            push_cast at h_comp
            exact lt_of_F_lt h_comp
        · rw [max_lt_iff]
          refine ⟨?_, ?_⟩
          · change (n_b : ℝ) / s < ((n_b : ℝ) + 1) / s
            rw [div_lt_div_iff₀ s_pos s_pos]
            linarith [s_pos]
          · by_cases hn_c : n_c = 0
            · rw [hn_c]
              norm_num
              exact div_pos (by positivity) s_pos
            · have hn_c_pos : 0 < n_c := by omega
              have h_lt : A208326 n_c < y := by
                have : ¬ A208326 n_c ≥ y := Nat.find_min h_ex_c (by omega : n_c < m_c)
                omega
              have h_comp : (A208326 n_c : ℤ) < (A207673 (n_b + 1) : ℤ) := by linarith [h_spec_b]
              rw [A208326_eq_F, A207673_eq_F] at h_comp
              push_cast at h_comp
              exact lt_of_F_lt h_comp

      have h_fu : F u = n_a + n_b + n_c := by
        dsimp [F]
        have f1 : Int.floor (u * r) = n_a := by
          have l1 : u * r < n_a + 1 := by
            have : u < v_b := hu_lt
            have : u < v_a := this.trans h_ba
            rwa [lt_div_iff₀ r_pos] at this
          have l2 : (n_a : ℝ) ≤ u * r := by
            rwa [div_le_iff₀ r_pos] at hu_r
          have l1_f : Int.floor (u * r) < n_a + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_a ≤ Int.floor (u * r) := by
            have : (n_a : ℝ) ≤ u * r := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        have f2 : Int.floor (u * s) = n_b := by
          have l1 : u * s < n_b + 1 := by
            rwa [lt_div_iff₀ s_pos] at hu_lt
          have l2 : (n_b : ℝ) ≤ u * s := by
            rwa [div_le_iff₀ s_pos] at hu_s
          have l1_f : Int.floor (u * s) < n_b + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_b ≤ Int.floor (u * s) := by
            have : (n_b : ℝ) ≤ u * s := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        have f3 : Int.floor (u * t) = n_c := by
          have l1 : u * t < n_c + 1 := by
            have : u < v_b := hu_lt
            have : u < v_c := this.trans h_bc
            rwa [lt_div_iff₀ t_pos] at this
          have l2 : (n_c : ℝ) ≤ u * t := by
            rwa [div_le_iff₀ t_pos] at hu_t
          have l1_f : Int.floor (u * t) < n_c + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_c ≤ Int.floor (u * t) := by
            have : (n_c : ℝ) ≤ u * t := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        omega

      have h_fu_lt : F u < y := by
        have h_cases : u = n_a / r ∨ u = n_b / s ∨ u = n_c / t := by
          dsimp [u]
          rcases le_total (n_a / r) (max (n_b / s) (n_c / t)) with h | h
          · rw [max_eq_right h]
            rcases le_total (n_b / s) (n_c / t) with h2 | h2
            · rw [max_eq_right h2]
              right; right; rfl
            · rw [max_eq_left h2]
              right; left; rfl
          · rw [max_eq_left h]
            left; rfl
        rcases h_cases with hu_eq | hu_eq | hu_eq
        · rw [hu_eq]
          by_cases hn_a : n_a = 0
          · rw [hn_a]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_a_pos : 0 < n_a := by omega
            have h_lt : A207672 n_a < y := by
              have : ¬ A207672 n_a ≥ y := Nat.find_min h_ex_a (by omega : n_a < m_a)
              omega
            have h_lt_cast : (A207672 n_a : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A207672_eq_F] at h_lt_cast
            exact h_lt_cast
        · rw [hu_eq]
          by_cases hn_b : n_b = 0
          · rw [hn_b]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_b_pos : 0 < n_b := by omega
            have h_lt : A207673 n_b < y := by
              have : ¬ A207673 n_b ≥ y := Nat.find_min h_ex_b (by omega : n_b < m_b)
              omega
            have h_lt_cast : (A207673 n_b : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A207673_eq_F] at h_lt_cast
            exact h_lt_cast
        · rw [hu_eq]
          by_cases hn_c : n_c = 0
          · rw [hn_c]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_c_pos : 0 < n_c := by omega
            have h_lt : A208326 n_c < y := by
              have : ¬ A208326 n_c ≥ y := Nat.find_min h_ex_c (by omega : n_c < m_c)
              omega
            have h_lt_cast : (A208326 n_c : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A208326_eq_F] at h_lt_cast
            exact h_lt_cast

      have h_final : (A207673 (n_b + 1) : ℤ) = y := by
        have h_spec_b_cast : (A207673 (n_b + 1) : ℤ) ≥ (y : ℤ) := by exact_mod_cast h_spec_b
        rw [A207673_eq_F]
        rw [A207673_eq_F] at h_spec_b_cast
        push_cast at h_spec_b_cast
        push_cast
        linarith
      exact_mod_cast h_final

    · -- Case 3: v_c ≤ v_a and v_c ≤ v_b
      right
      rw [Set.mem_range]
      refine ⟨n_c, ?_⟩
      dsimp
      have h_ca : v_c < v_a := by
        rcases hac.lt_or_eq with h | h
        · exact h
        · exfalso; exact rat_contradiction_r_t n_a n_c h.symm
      have h_cb : v_c < v_b := by
        rcases hbc.lt_or_eq with h | h
        · exact h
        · exfalso; exact rat_contradiction_s_t n_b n_c h.symm
      have h1 : v_c * r < n_a + 1 := by
        rwa [lt_div_iff₀ r_pos] at h_ca
      have h1_floor : Int.floor (v_c * r) ≤ n_a := by
        have : Int.floor (v_c * r) < (n_a : ℤ) + 1 := by
          rw [Int.floor_lt]
          exact_mod_cast h1
        omega
      have h2 : v_c * s < n_b + 1 := by
        rwa [lt_div_iff₀ s_pos] at h_cb
      have h2_floor : Int.floor (v_c * s) ≤ n_b := by
        have : Int.floor (v_c * s) < (n_b : ℤ) + 1 := by
          rw [Int.floor_lt]
          exact_mod_cast h2
        omega
      have h3_floor : (n_a : ℤ) ≤ Int.floor (v_c * r) := by
        by_cases hn_a : n_a = 0
        · rw [hn_a]
          have : 0 ≤ v_c * r := mul_nonneg (div_nonneg (by positivity) t_pos.le) r_pos.le
          exact Int.floor_nonneg.mpr this
        · have hn_a_pos : 0 < n_a := by omega
          have h_lt : A207672 n_a < y := by
            have : ¬ A207672 n_a ≥ y := Nat.find_min h_ex_a (by omega : n_a < m_a)
            omega
          have h_comp : (A207672 n_a : ℤ) < (A208326 (n_c + 1) : ℤ) := by linarith [h_spec_c]
          rw [A207672_eq_F, A208326_eq_F] at h_comp
          push_cast at h_comp
          have h_comp_lt := lt_of_F_lt h_comp
          have : (n_a : ℝ) < v_c * r := (div_lt_iff₀ r_pos).mp h_comp_lt
          exact Int.le_floor.mpr this.le
      have h4_floor : (n_b : ℤ) ≤ Int.floor (v_c * s) := by
        by_cases hn_b : n_b = 0
        · rw [hn_b]
          have : 0 ≤ v_c * s := mul_nonneg (div_nonneg (by positivity) t_pos.le) s_pos.le
          exact Int.floor_nonneg.mpr this
        · have hn_b_pos : 0 < n_b := by omega
          have h_lt : A207673 n_b < y := by
            have : ¬ A207673 n_b ≥ y := Nat.find_min h_ex_b (by omega : n_b < m_b)
            omega
          have h_comp : (A207673 n_b : ℤ) < (A208326 (n_c + 1) : ℤ) := by linarith [h_spec_c]
          rw [A207673_eq_F, A208326_eq_F] at h_comp
          push_cast at h_comp
          have h_comp_lt := lt_of_F_lt h_comp
          have : (n_b : ℝ) < v_c * s := (div_lt_iff₀ s_pos).mp h_comp_lt
          exact Int.le_floor.mpr this.le
      have h_eq_r : Int.floor (v_c * r) = n_a := by omega
      have h_eq_s : Int.floor (v_c * s) = n_b := by omega
      have h_eq_t : Int.floor (v_c * t) = n_c + 1 := by
        change Int.floor (((n_c : ℝ) + 1) / (1 / goldenRatio) * (1 / goldenRatio)) = n_c + 1
        rw [div_mul_cancel₀ ((n_c : ℝ) + 1) (by
          intro h
          have : (1 / goldenRatio : ℝ) = 0 := h
          have : (0 : ℝ) < 1 / goldenRatio := by exact one_div_pos.mpr goldenRatio_pos
          linarith)]
        simp
      have h_sum : F v_c = n_a + n_b + (n_c + 1) := by
        dsimp [F]
        rw [h_eq_r, h_eq_s, h_eq_t]

      let u := max (n_a / r) (max (n_b / s) (n_c / t))
      have hu_r : n_a / r ≤ u := le_max_left _ _
      have hu_s : n_b / s ≤ u := by
        have : n_b / s ≤ max (n_b / s) (n_c / t) := le_max_left _ _
        exact this.trans (le_max_right _ _)
      have hu_t : n_c / t ≤ u := by
        have : n_c / t ≤ max (n_b / s) (n_c / t) := le_max_right _ _
        exact this.trans (le_max_right _ _)

      have hu_lt : u < v_c := by
        rw [max_lt_iff]
        refine ⟨?_, ?_⟩
        · by_cases hn_a : n_a = 0
          · rw [hn_a]
            norm_num
            exact div_pos (by positivity) t_pos
          · have hn_a_pos : 0 < n_a := by omega
            have h_lt : A207672 n_a < y := by
              have : ¬ A207672 n_a ≥ y := Nat.find_min h_ex_a (by omega : n_a < m_a)
              omega
            have h_comp : (A207672 n_a : ℤ) < (A208326 (n_c + 1) : ℤ) := by linarith [h_spec_c]
            rw [A207672_eq_F, A208326_eq_F] at h_comp
            push_cast at h_comp
            exact lt_of_F_lt h_comp
        · rw [max_lt_iff]
          refine ⟨?_, ?_⟩
          · by_cases hn_b : n_b = 0
            · rw [hn_b]
              norm_num
              exact div_pos (by positivity) t_pos
            · have hn_b_pos : 0 < n_b := by omega
              have h_lt : A207673 n_b < y := by
                have : ¬ A207673 n_b ≥ y := Nat.find_min h_ex_b (by omega : n_b < m_b)
                omega
              have h_comp : (A207673 n_b : ℤ) < (A208326 (n_c + 1) : ℤ) := by linarith [h_spec_c]
              rw [A207673_eq_F, A208326_eq_F] at h_comp
              push_cast at h_comp
              exact lt_of_F_lt h_comp
          · change (n_c : ℝ) / t < ((n_c : ℝ) + 1) / t
            rw [div_lt_div_iff₀ t_pos t_pos]
            linarith [t_pos]

      have h_fu : F u = n_a + n_b + n_c := by
        dsimp [F]
        have f1 : Int.floor (u * r) = n_a := by
          have l1 : u * r < n_a + 1 := by
            have : u < v_c := hu_lt
            have : u < v_a := this.trans h_ca
            rwa [lt_div_iff₀ r_pos] at this
          have l2 : (n_a : ℝ) ≤ u * r := by
            rwa [div_le_iff₀ r_pos] at hu_r
          have l1_f : Int.floor (u * r) < n_a + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_a ≤ Int.floor (u * r) := by
            have : (n_a : ℝ) ≤ u * r := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        have f2 : Int.floor (u * s) = n_b := by
          have l1 : u * s < n_b + 1 := by
            have : u < v_c := hu_lt
            have : u < v_b := this.trans h_cb
            rwa [lt_div_iff₀ s_pos] at this
          have l2 : (n_b : ℝ) ≤ u * s := by
            rwa [div_le_iff₀ s_pos] at hu_s
          have l1_f : Int.floor (u * s) < n_b + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_b ≤ Int.floor (u * s) := by
            have : (n_b : ℝ) ≤ u * s := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        have f3 : Int.floor (u * t) = n_c := by
          have l1 : u * t < n_c + 1 := by
            rwa [lt_div_iff₀ t_pos] at hu_lt
          have l2 : (n_c : ℝ) ≤ u * t := by
            rwa [div_le_iff₀ t_pos] at hu_t
          have l1_f : Int.floor (u * t) < n_c + 1 := by
            rw [Int.floor_lt]
            exact_mod_cast l1
          have l2_f : n_c ≤ Int.floor (u * t) := by
            have : (n_c : ℝ) ≤ u * t := l2
            exact_mod_cast Int.le_floor.mpr this
          omega
        omega

      have h_fu_lt : F u < y := by
        have h_cases : u = n_a / r ∨ u = n_b / s ∨ u = n_c / t := by
          dsimp [u]
          rcases le_total (n_a / r) (max (n_b / s) (n_c / t)) with h | h
          · rw [max_eq_right h]
            rcases le_total (n_b / s) (n_c / t) with h2 | h2
            · rw [max_eq_right h2]
              right; right; rfl
            · rw [max_eq_left h2]
              right; left; rfl
          · rw [max_eq_left h]
            left; rfl
        rcases h_cases with hu_eq | hu_eq | hu_eq
        · rw [hu_eq]
          by_cases hn_a : n_a = 0
          · rw [hn_a]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_a_pos : 0 < n_a := by omega
            have h_lt : A207672 n_a < y := by
              have : ¬ A207672 n_a ≥ y := Nat.find_min h_ex_a (by omega : n_a < m_a)
              omega
            have h_lt_cast : (A207672 n_a : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A207672_eq_F] at h_lt_cast
            exact h_lt_cast
        · rw [hu_eq]
          by_cases hn_b : n_b = 0
          · rw [hn_b]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_b_pos : 0 < n_b := by omega
            have h_lt : A207673 n_b < y := by
              have : ¬ A207673 n_b ≥ y := Nat.find_min h_ex_b (by omega : n_b < m_b)
              omega
            have h_lt_cast : (A207673 n_b : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A207673_eq_F] at h_lt_cast
            exact h_lt_cast
        · rw [hu_eq]
          by_cases hn_c : n_c = 0
          · rw [hn_c]
            norm_num
            have : F 0 = 0 := by dsimp [F]; simp
            rw [this]
            exact_mod_cast hy
          · have hn_c_pos : 0 < n_c := by omega
            have h_lt : A208326 n_c < y := by
              have : ¬ A208326 n_c ≥ y := Nat.find_min h_ex_c (by omega : n_c < m_c)
              omega
            have h_lt_cast : (A208326 n_c : ℤ) < (y : ℤ) := by exact_mod_cast h_lt
            rw [A208326_eq_F] at h_lt_cast
            exact h_lt_cast

      have h_final : (A208326 (n_c + 1) : ℤ) = y := by
        have h_spec_c_cast : (A208326 (n_c + 1) : ℤ) ≥ (y : ℤ) := by exact_mod_cast h_spec_c
        rw [A208326_eq_F]
        rw [A208326_eq_F] at h_spec_c_cast
        push_cast at h_spec_c_cast
        push_cast
        linarith
      exact_mod_cast h_final

theorem oeis_208326_conjecture_0 :
  ({n : ℕ | 0 < n} : Set ℕ) =
    (Set.range (A207672 ∘ Nat.succ)) ∪
    (Set.range (A207673 ∘ Nat.succ)) ∪
    (Set.range (A208326 ∘ Nat.succ)) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A207673 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207673 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅)
  := by
  refine ⟨?_, range_disjoint_A207672_A207673, range_disjoint_A207672_A208326, range_disjoint_A207673_A208326⟩
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_range, Function.comp_apply]
  constructor
  · intro hy
    exact oeis_208326_conjecture_0_coverage hy
  · rintro ((⟨n, hn1⟩ | ⟨n, hn2⟩) | ⟨n, hn3⟩)
    · rw [← hn1]
      exact A207672_pos (n + 1) (by omega)
    · rw [← hn2]
      exact A207673_pos (n + 1) (by omega)
    · rw [← hn3]
      exact A208326_pos (n + 1) (by omega)
