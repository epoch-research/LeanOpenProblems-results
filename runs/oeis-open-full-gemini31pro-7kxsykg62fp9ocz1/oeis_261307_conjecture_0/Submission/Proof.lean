import Submission.Spec
open Nat

noncomputable def C (n : ℕ) : ℕ := 7 * a n + 7 * n + 6

lemma a_step (n : ℕ) : a (n + 2) = Int.natAbs (a (n + 1) - Nat.gcd (a (n + 1)) (7 * (n + 1) + 6)) := rfl

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 1 := rfl
lemma a_2 : a 2 = 0 := rfl
lemma a_3 : a 3 = 20 := rfl

lemma gcd_le {x y : ℕ} (hx : x > 0) : Nat.gcd x y ≤ x := Nat.gcd_le_left y hx

lemma abs_sub_eq_sub {x y : ℕ} (h : y ≤ x) : Int.natAbs ((x : ℤ) - (y : ℤ)) = x - y := by omega

lemma C_step (n : ℕ) (h : a (n + 1) > 0) : 
  let g := Nat.gcd (a (n + 1)) (7 * (n + 1) + 6)
  C (n + 2) = C (n + 1) - 7 * (g - 1) ∧ a (n + 2) = a (n + 1) - g := by
  intro g
  have hg : g ≤ a (n + 1) := gcd_le h
  have ha : a (n + 2) = a (n + 1) - g := by rw [a_step, abs_sub_eq_sub hg]
  refine ⟨?_, ha⟩
  dsimp [C]
  rw [ha]
  have hy : 7 * (n + 1) + 6 > 0 := by omega
  have hg_pos : g > 0 := Nat.gcd_pos_of_pos_right (a (n + 1)) hy
  omega

lemma a_lt_C (n : ℕ) : a n < C n := by
  dsimp [C]
  omega
