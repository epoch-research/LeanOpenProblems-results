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
    · change (140 : ℝ) * sqrt (5 / 4) < (157 : ℝ)
      have h : sqrt (5 / 4) < (157/140 : ℝ) := by
        rw [Real.sqrt_lt] <;> norm_num
      nlinarith
  rw [hfloor]
  rfl

lemma a140 : a 140 = 471 := by
  unfold a
  dsimp
  rw [floor_140]
  norm_num

theorem disproof : ¬ A190363_LR.IsSolution (fun n : ℕ => (a (n + 1) : ℤ)) := by
  intro h
  have h139 := h 139
  norm_num [A190363_LR, LinearRecurrence.IsSolution, A190363_coeffs] at h139
