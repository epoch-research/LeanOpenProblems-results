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
    · norm_num
      -- goal 156 ≤ 140 * sqrt (5/4)
      have hs : (0:ℝ) ≤ 5 / 4 := by norm_num
      have hsq := sq_sqrt hs
      nlinarith [sq_nonneg (sqrt (5 / 4) : ℝ)]
    · norm_num
      -- goal 140 * sqrt (5/4) < 157
      have hs : (0:ℝ) ≤ 5 / 4 := by norm_num
      have hsq := sq_sqrt hs
      nlinarith [sq_nonneg (sqrt (5 / 4) : ℝ)]
  rw [hfloor]
  norm_num

lemma floor_144 : (Int.floor ((144 : ℝ) * sqrt (5 / 4))).toNat = 160 := by
  have hfloor : Int.floor ((144 : ℝ) * sqrt (5 / 4)) = (160 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_num
      have hs : (0:ℝ) ≤ 5 / 4 := by norm_num
      have hsq := sq_sqrt hs
      nlinarith [sq_nonneg (sqrt (5 / 4) : ℝ)]
    · norm_num
      have hs : (0:ℝ) ≤ 5 / 4 := by norm_num
      have hsq := sq_sqrt hs
      nlinarith [sq_nonneg (sqrt (5 / 4) : ℝ)]
  rw [hfloor]
  norm_num

lemma floor_157 : (Int.floor ((157 : ℝ) * sqrt (5 / 4))).toNat = 175 := by
  have hfloor : Int.floor ((157 : ℝ) * sqrt (5 / 4)) = (175 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_num
      have hs : (0:ℝ) ≤ 5 / 4 := by norm_num
      have hsq := sq_sqrt hs
      nlinarith [sq_nonneg (sqrt (5 / 4) : ℝ)]
    · norm_num
      have hs : (0:ℝ) ≤ 5 / 4 := by norm_num
      have hsq := sq_sqrt hs
      nlinarith [sq_nonneg (sqrt (5 / 4) : ℝ)]
  rw [hfloor]
  norm_num

lemma floor_161 : (Int.floor ((161 : ℝ) * sqrt (5 / 4))).toNat = 180 := by
  have hfloor : Int.floor ((161 : ℝ) * sqrt (5 / 4)) = (180 : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_num
      have hs : (0:ℝ) ≤ 5 / 4 := by norm_num
      have hsq := sq_sqrt hs
      nlinarith [sq_nonneg (sqrt (5 / 4) : ℝ)]
    · norm_num
      have hs : (0:ℝ) ≤ 5 / 4 := by norm_num
      have hsq := sq_sqrt hs
      nlinarith [sq_nonneg (sqrt (5 / 4) : ℝ)]
  rw [hfloor]
  norm_num

lemma avals : a 161 = 542 ∧ a 157 = 528 ∧ a 144 = 484 ∧ a 140 = 471 := by
  simp [a, floor_161, floor_157, floor_144, floor_140]

theorem disproof : ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h139 := h 139
  have hvals := avals
  norm_num [A190363_LR, LinearRecurrence.IsSolution, A190363_coeffs, a, floor_161, floor_157, floor_144, floor_140] at h139
