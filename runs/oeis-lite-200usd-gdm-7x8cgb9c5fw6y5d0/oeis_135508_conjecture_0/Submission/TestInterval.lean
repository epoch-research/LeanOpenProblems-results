import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 20000
set_option synthInstance.maxSize 2048



open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

def x_seq_loop : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | i + 1, idx, acc => x_seq_loop i (idx + 1) (2 * acc + Nat.lcm acc idx)

def x_seq_tail (n : ℕ) : ℕ :=
  if n = 0 then 0 else x_seq_loop (n - 1) 2 1

lemma x_seq_step (idx : ℕ) (hidx : idx ≥ 2) : x_seq idx = 2 * x_seq (idx - 1) + Nat.lcm (x_seq (idx - 1)) idx := by
  have h_eq : idx = idx - 1 + 1 := (Nat.sub_add_cancel (by omega)).symm
  nth_rw 1 [h_eq]
  rw [x_seq]
  · have h_eq2 : idx - 1 + 1 = idx := Nat.sub_add_cancel (by omega)
    rw [h_eq2]
  · omega

lemma x_seq_loop_lemma (i : ℕ) :
  ∀ idx acc, idx ≥ 2 → acc = x_seq (idx - 1) → x_seq_loop i idx acc = x_seq (i + idx - 1) := by
  induction i with
  | zero =>
    intro idx acc hidx hacc
    simp [x_seq_loop, hacc]
  | succ k ih =>
    intro idx acc hidx hacc
    simp [x_seq_loop]
    have h_acc' : 2 * acc + Nat.lcm acc idx = x_seq idx := by
      rw [hacc]
      exact (x_seq_step idx hidx).symm
    have h_idx' : idx + 1 ≥ 2 := by omega
    have h_acc_eq : 2 * acc + Nat.lcm acc idx = x_seq (idx + 1 - 1) := by
      rw [h_acc']
      have : idx + 1 - 1 = idx := by omega
      rw [this]
    have h_ih := ih (idx + 1) (2 * acc + Nat.lcm acc idx) h_idx' h_acc_eq
    rw [h_ih]
    congr 1

lemma x_seq_eq_x_seq_tail (n : ℕ) : x_seq n = x_seq_tail n := by
  by_cases hn : n = 0
  · simp [hn, x_seq_tail]
    rfl
  · simp [x_seq_tail, hn]
    have h_loop := x_seq_loop_lemma (n - 1) 2 1 (by omega) (by rfl)
    rw [h_loop]
    congr 1; omega

lemma prime_in_range_test : ∀ r, r ≤ 263 → r > 103 → Nat.Prime r → r = 107 ∨ r = 109 ∨ r = 113 ∨ r = 127 ∨ r = 131 ∨ r = 137 ∨ r = 139 ∨ r = 149 ∨ r = 151 ∨ r = 157 ∨ r = 163 ∨ r = 167 ∨ r = 173 ∨ r = 179 ∨ r = 181 ∨ r = 191 ∨ r = 193 ∨ r = 197 ∨ r = 199 ∨ r = 211 ∨ r = 223 ∨ r = 227 ∨ r = 229 ∨ r = 233 ∨ r = 239 ∨ r = 241 ∨ r = 251 ∨ r = 257 ∨ r = 263 := by
  decide

