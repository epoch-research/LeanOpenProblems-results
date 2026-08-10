import Mathlib.Data.Nat.Basic
def x_seq_loop : ℕ → ℕ → ℕ → ℕ
| 0, _, x => x
| n + 1, i, x => x_seq_loop n (i + 1) (2 * x + Nat.lcm x i)

def x_seq_tr (n : ℕ) : ℕ :=
  if n = 0 then 0
  else x_seq_loop (n - 1) 2 1

lemma x_seq_loop_add (a b i x : ℕ) :
    x_seq_loop (a + b) i x = x_seq_loop b (i + a) (x_seq_loop a i x) := sorry

lemma test_dvd : 29 ∣ x_seq_tr 317 := by
  rw [x_seq_tr]
  simp
  have h_val1 : x_seq_loop 300 2 1 = 12781445 := sorry
  have h_val2 : x_seq_loop 16 302 12781445 = 580234 := sorry
  have h_eq : x_seq_loop 316 2 1 = x_seq_loop 16 302 (x_seq_loop 300 2 1) := by
    have : 316 = 300 + 16 := by rfl
    rw [this, x_seq_loop_add]
  rw [h_eq]
  rw [h_val1, h_val2]
  decide

