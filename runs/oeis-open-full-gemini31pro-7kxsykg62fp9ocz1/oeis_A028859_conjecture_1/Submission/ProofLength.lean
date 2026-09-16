import Submission.Generator
import Mathlib

@[simp] theorem a_0 : a 0 = 1 := a.eq_1
@[simp] theorem a_1 : a 1 = 3 := a.eq_2
@[simp] theorem a_add2 (n : ℕ) : a (n + 2) = 2 * a (n + 1) + 2 * a n := a.eq_3 n

theorem gen_length (n : ℕ) : (gen (n + 1)).length = a n := by
  induction' n using Nat.strongRecOn with n ih
  rcases n with _ | _ | n
  · rw [a_0, gen.eq_2]; rfl
  · rw [a_1, gen.eq_3]; rfl
  · have h_gen : gen (n + 3) = 
      (gen (n + 2)).map map1 ++ (gen (n + 2)).map map2 ++
      ((gen (n + 1)).map map3 ++ (gen (n + 1)).map map4) := rfl
    have h1 : gen (n + 2 + 1) = gen (n + 3) := rfl
    rw [h1, h_gen]
    simp
    rw [ih (n + 1) (by omega), ih n (by omega)]
    omega
