import Mathlib

set_option maxHeartbeats 10000000
theorem goldbach_case_8004 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 8004 = p + q := by exact ⟨11, 7993, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_8006 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 8006 = p + q := by exact ⟨13, 7993, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_8008 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 8008 = p + q := by exact ⟨59, 7949, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_8010 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 8010 = p + q := by exact ⟨17, 7993, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_8012 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 8012 = p + q := by exact ⟨3, 8009, by norm_num, by norm_num, rfl⟩

lemma goldbach_match_9 (n : ℕ) : (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) ∨ True := by
  match n with
  | 8004 => exact Or.inl goldbach_case_8004
  | 8006 => exact Or.inl goldbach_case_8006
  | 8008 => exact Or.inl goldbach_case_8008
  | 8010 => exact Or.inl goldbach_case_8010
  | 8012 => exact Or.inl goldbach_case_8012
  | _ => exact Or.inr trivial
