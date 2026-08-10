import FormalConjectures.Util.ProblemImports
open Nat Finset

def A335624_rep (n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x^2 + y^2 + z^2 + w^2 = n ∧ Nat.sqrt (x + 3 * y + 4 * z) ^ 2 = x + 3 * y + 4 * z

lemma not_rep_8 : ¬ A335624_rep 8 := by
  intro ⟨x, y, z, w, h1, h2⟩
  have hx : x < 3 := by nlinarith
  have hy : y < 3 := by nlinarith
  have hz : z < 3 := by nlinarith
  have hw : w < 3 := by nlinarith
  have hs : Nat.sqrt (x + 3 * y + 4 * z) < 5 := by
    rw [Nat.sqrt_lt]
    omega
  generalize hs_eq : Nat.sqrt (x + 3 * y + 4 * z) = s at h2 hs
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;> interval_cases s <;> revert h1 h2 <;> omega

lemma not_rep_24 : ¬ A335624_rep 24 := by
  intro ⟨x, y, z, w, h1, h2⟩
  have hx : x < 5 := by nlinarith
  have hy : y < 5 := by nlinarith
  have hz : z < 5 := by nlinarith
  have hw : w < 5 := by nlinarith
  have hs : Nat.sqrt (x + 3 * y + 4 * z) < 7 := by
    rw [Nat.sqrt_lt]
    omega
  generalize hs_eq : Nat.sqrt (x + 3 * y + 4 * z) = s at h2 hs
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;> interval_cases s <;> revert h1 h2 <;> omega

lemma not_rep_40 : ¬ A335624_rep 40 := by
  intro ⟨x, y, z, w, h1, h2⟩
  have hx : x < 7 := by nlinarith
  have hy : y < 7 := by nlinarith
  have hz : z < 7 := by nlinarith
  have hw : w < 7 := by nlinarith
  have hs : Nat.sqrt (x + 3 * y + 4 * z) < 9 := by
    rw [Nat.sqrt_lt]
    omega
  generalize hs_eq : Nat.sqrt (x + 3 * y + 4 * z) = s at h2 hs
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;> interval_cases s <;> revert h1 h2 <;> omega
