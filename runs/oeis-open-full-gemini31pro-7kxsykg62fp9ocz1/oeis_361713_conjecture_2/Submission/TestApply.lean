import Mathlib
import Submission.Fast
import Submission.ExactDef

def apply_exact : ℕ → (ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ
| 0, g, x => x
| f + 1, g, x => apply_exact f g (g x)

theorem apply_exact_eq_a_fast_loop (n f : ℕ) (st : ℕ × ℕ × ℕ × ℕ) (h : f = n - st.1) :
  (apply_exact f (step_exact n) st).2.2.2 = a_fast_loop n st.1 st.2.1 st.2.2.1 st.2.2.2 := by
  induction f generalizing st with
  | zero =>
    rcases st with ⟨k, c1, c2, acc⟩
    unfold a_fast_loop
    dsimp
    split_ifs with h2
    · omega
    · rfl
  | succ f ih =>
    rcases st with ⟨k, c1, c2, acc⟩
    unfold apply_exact
    unfold a_fast_loop
    dsimp
    split_ifs with h2
    · let c1' := c1 * (n - k) / (k + 1)
      let c2' := c2 * (n + k) / (k + 1)
      have : (step_exact n (k, c1, c2, acc)) = (k + 1, c1', c2', acc + c1^2 * c2^2) := by
        unfold step_exact
        dsimp
        split_ifs
        rfl
      rw [this]
      apply ih
      omega
    · omega

theorem apply_exact_comm (b : ℕ) (g : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ) (x : ℕ × ℕ × ℕ × ℕ) :
  apply_exact b g (g x) = g (apply_exact b g x) := by
  induction b generalizing x with
  | zero => rfl
  | succ b ih =>
    unfold apply_exact
    rw [ih (g x)]

theorem apply_exact_add (a b : ℕ) (g : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ) (x : ℕ × ℕ × ℕ × ℕ) :
  apply_exact (a + b) g x = apply_exact a g (apply_exact b g x) := by
  induction a generalizing x with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a ih =>
    rw [Nat.succ_add]
    unfold apply_exact
    rw [ih (g x)]
    rw [apply_exact_comm b g x]
