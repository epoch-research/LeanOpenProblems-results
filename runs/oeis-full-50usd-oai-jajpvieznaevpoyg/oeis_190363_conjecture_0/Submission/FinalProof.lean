import FormalConjectures.Util.ProblemImports

open Real

noncomputable def a (n : ℕ) : ℕ :=
  let n_R : ℝ := n
  let sqrt_expr : ℝ := sqrt (5 / 4)
  let floor_term_sqrt : ℕ := (Int.floor (n_R * sqrt_expr)).toNat
  let floor_term_div : ℕ := n / 4
  2 * n + floor_term_sqrt + floor_term_div

open scoped BigOperators

noncomputable def A190363_coeffs : Fin 21 → ℤ :=
  fun i =>
    match i.val with
    | 0 => -1
    | 4 => 1
    | 17 => 1
    | _ => 0

noncomputable def A190363_LR : LinearRecurrence ℤ :=
  LinearRecurrence.mk 21 A190363_coeffs

lemma floor_140 : (Int.floor ((140 : ℝ) * sqrt (5 / 4))).toNat = 156 := by
  have hfloor : Int.floor ((140 : ℝ) * sqrt (5 / 4)) = (156 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · change (156 : ℝ) ≤ (140 : ℝ) * sqrt (5 / 4)
      have h : (39/35 : ℝ) ≤ sqrt (5 / 4) := by
        rw [Real.le_sqrt] <;> norm_num
      nlinarith
    · have h : (140 : ℝ) * sqrt (5 / 4) < (157 : ℝ) := by
        have hs : sqrt (5 / 4) < (157/140 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        nlinarith
      convert h using 1
      norm_num
  rw [hfloor]
  rfl

lemma floor_144 : (Int.floor ((144 : ℝ) * sqrt (5 / 4))).toNat = 160 := by
  have hfloor : Int.floor ((144 : ℝ) * sqrt (5 / 4)) = (160 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · change (160 : ℝ) ≤ (144 : ℝ) * sqrt (5 / 4)
      have h : (10/9 : ℝ) ≤ sqrt (5 / 4) := by
        rw [Real.le_sqrt] <;> norm_num
      nlinarith
    · have h : (144 : ℝ) * sqrt (5 / 4) < (161 : ℝ) := by
        have hs : sqrt (5 / 4) < (161/144 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        nlinarith
      convert h using 1
      norm_num
  rw [hfloor]
  rfl

lemma floor_157 : (Int.floor ((157 : ℝ) * sqrt (5 / 4))).toNat = 175 := by
  have hfloor : Int.floor ((157 : ℝ) * sqrt (5 / 4)) = (175 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · change (175 : ℝ) ≤ (157 : ℝ) * sqrt (5 / 4)
      have h : (175/157 : ℝ) ≤ sqrt (5 / 4) := by
        rw [Real.le_sqrt] <;> norm_num
      nlinarith
    · have h : (157 : ℝ) * sqrt (5 / 4) < (176 : ℝ) := by
        have hs : sqrt (5 / 4) < (176/157 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        nlinarith
      convert h using 1
      norm_num
  rw [hfloor]
  rfl

lemma floor_161 : (Int.floor ((161 : ℝ) * sqrt (5 / 4))).toNat = 180 := by
  have hfloor : Int.floor ((161 : ℝ) * sqrt (5 / 4)) = (180 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · change (180 : ℝ) ≤ (161 : ℝ) * sqrt (5 / 4)
      have h : (180/161 : ℝ) ≤ sqrt (5 / 4) := by
        rw [Real.le_sqrt] <;> norm_num
      nlinarith
    · have h : (161 : ℝ) * sqrt (5 / 4) < (181 : ℝ) := by
        have hs : sqrt (5 / 4) < (181/161 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
        nlinarith
      convert h using 1
      norm_num
  rw [hfloor]
  rfl

lemma a140 : a 140 = 471 := by
  unfold a
  dsimp
  rw [floor_140]

lemma a144 : a 144 = 484 := by
  unfold a
  dsimp
  rw [floor_144]

lemma a157 : a 157 = 528 := by
  unfold a
  dsimp
  rw [floor_157]

lemma a161 : a 161 = 542 := by
  unfold a
  dsimp
  rw [floor_161]

theorem oeis_190363_conjecture_0.disproof :
  ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro hsol
  have h139 := hsol 139
  simp only [A190363_LR, LinearRecurrence.IsSolution, A190363_coeffs,
    Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ] at h139
  norm_num [a140, a144, a157, a161] at h139
