import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 4000000

open Nat

def x_seq : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => 2 * (x_seq n) + Nat.lcm (x_seq n) (n + 1)

lemma x_seq_mod_eq (n : ℕ) : x_seq (n + 1) % (n + 1) = (2 * x_seq n) % (n + 1) := by
  cases n with
  | zero => rfl
  | succ n' =>
    have h_eq : x_seq (n' + 1 + 1) = 2 * x_seq (n' + 1) + Nat.lcm (x_seq (n' + 1)) (n' + 1 + 1) := by
      rw [x_seq]
      omega
    rw [h_eq]
    have h_lcm : (n' + 1 + 1) ∣ Nat.lcm (x_seq (n' + 1)) (n' + 1 + 1) := Nat.dvd_lcm_right _ _
    rcases h_lcm with ⟨k, hk⟩
    rw [hk]
    exact Nat.add_mul_mod_self_left (2 * x_seq (n' + 1)) (n' + 1 + 1) k

lemma x_seq_pos (n : ℕ) (hn : n > 0) : x_seq n > 0 := by
  induction' n with n ih
  · contradiction
  · cases' n with n'
    · simp [x_seq]
    · rw [x_seq]
      · have h1 : n' + 1 > 0 := by omega
        have h2 : x_seq (n' + 1) > 0 := ih h1
        omega
      · omega
