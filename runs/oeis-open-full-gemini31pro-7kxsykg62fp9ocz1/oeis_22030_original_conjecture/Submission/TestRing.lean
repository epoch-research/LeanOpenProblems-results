import FormalConjectures.Util.ProblemImports

def C : ℕ → ℤ
| 0 => 4
| 1 => 16
| 2 => 63
| (n + 3) => 4 * C (n + 2) - C n

def d (n : ℕ) : ℤ := C (n + 1)^2 - C (n + 2) * C n

lemma C_add_3 (n : ℕ) : C (n + 3) = 4 * C (n + 2) - C n := by rfl

theorem d_rec (n : ℕ) : d (n + 3) = 4 * d (n + 1) + d n := by
  dsimp [d]
  have h1 : C (n + 3) = 4 * C (n + 2) - C n := C_add_3 n
  have h2 : C (n + 4) = 4 * C (n + 3) - C (n + 1) := C_add_3 (n + 1)
  have h3 : C (n + 5) = 4 * C (n + 4) - C (n + 2) := C_add_3 (n + 2)
  rw [h3, h2, h1]
  ring

theorem d_nonneg (n : ℕ) : 0 ≤ d n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => norm_num [d, C]
  | 1 => norm_num [d, C]
  | 2 => norm_num [d, C]
  | m + 3 =>
    rw [d_rec m]
    have h1 : 0 ≤ d (m + 1) := ih (m + 1) (by omega)
    have h2 : 0 ≤ d m := ih m (by omega)
    linarith

theorem C_growth (n : ℕ) : 3 * C n ≤ C (n + 1) ∧ 0 ≤ C n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => norm_num [C]
  | 1 => norm_num [C]
  | 2 => norm_num [C]
  | m + 3 =>
    constructor
    · rw [C_add_3 (m + 1)]
      have h1 : 3 * C (m + 2) ≤ C (m + 3) := (ih (m + 2) (by omega)).1
      have h2 : 3 * C (m + 1) ≤ C (m + 2) := (ih (m + 1) (by omega)).1
      have h3 : 0 ≤ C (m + 1) := (ih (m + 1) (by omega)).2
      linarith
    · have h1 : 3 * C (m + 2) ≤ C (m + 3) := (ih (m + 2) (by omega)).1
      have h2 : 0 ≤ C (m + 2) := (ih (m + 2) (by omega)).2
      linarith

theorem d_le_C (n : ℕ) : d n ≤ C n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => norm_num [d, C]
  | 1 => norm_num [d, C]
  | 2 => norm_num [d, C]
  | m + 3 =>
    rw [d_rec m, C_add_3 m]
    have h1 : d (m + 1) ≤ C (m + 1) := ih (m + 1) (by omega)
    have h2 : d m ≤ C m := ih m (by omega)
    have h3 : 3 * C (m + 1) ≤ C (m + 2) := (C_growth (m + 1)).1
    have h4 : 3 * C m ≤ C (m + 1) := (C_growth m).1
    have h5 : 0 ≤ C m := (C_growth m).2
    linarith

theorem d_pos (n : ℕ) : 0 < d n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => norm_num [d, C]
  | 1 => norm_num [d, C]
  | 2 => norm_num [d, C]
  | m + 3 =>
    rw [d_rec m]
    have h1 : 0 < d (m + 1) := ih (m + 1) (by omega)
    have h2 : 0 < d m := ih m (by omega)
    linarith
