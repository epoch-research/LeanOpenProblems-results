import Mathlib

lemma choose_two_add (p : ℕ) : p.choose 2 + p.choose 2 = p * (p - 1) := by
  cases p with
  | zero => rfl
  | succ p =>
    induction p with
    | zero => rfl
    | succ p ih =>
      have H1 : (p + 2).choose 2 = (p + 1).choose 2 + (p + 1) := by
        change (p + 1 + 1).choose (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [H1]
      have H2 : (p + 1).choose 2 + (p + 1) + ((p + 1).choose 2 + (p + 1)) =
        ((p + 1).choose 2 + (p + 1).choose 2) + 2 * (p + 1) := by omega
      rw [H2, ih]
      have H4 : p + 1 - 1 = p := rfl
      rw [H4]
      have H5 : p + 1 + 1 - 1 = p + 1 := rfl
      rw [H5]
      ring
