import FormalConjectures.Util.ProblemImports

open Nat

def witness (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 4
  | 2 => 9
  | 3 => 8
  | _ => 1

def check_witness (n : ℕ) : Bool :=
  let w := witness n
  (w > 0) && ((w - 1) % Nat.totient w == n)

def check_all_witnesses : ℕ → Bool
  | 0 => true
  | n + 1 => check_all_witnesses n && check_witness n

lemma check_witness_of_check_all_witnesses {K : ℕ} (h : check_all_witnesses K = true) (n : ℕ) (hn : n < K) : check_witness n = true := by
  revert h n hn
  induction K with
  | zero =>
    intro h n hn
    omega
  | succ m ih =>
    intro h n hn
    simp [check_all_witnesses] at h
    have h1 : check_all_witnesses m = true := h.1
    have h2 : check_witness m = true := h.2
    have h_cases : n = m ∨ n < m := by omega
    rcases h_cases with rfl | h_lt
    · exact h2
    · exact ih h1 n h_lt

lemma witness_pos_and_mod (n : ℕ) (hn : n < 4) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  have h_check : check_all_witnesses 4 = true := by decide
  have h_cw := check_witness_of_check_all_witnesses h_check n hn
  unfold check_witness at h_cw
  rw [Bool.and_eq_true, Bool.beq_eq_decide_eq] at h_cw
  have h_pos : witness n > 0 := by
    have := h_cw.1
    exact decide_eq_true_iff.mp this
  have h_mod : (witness n - 1) % Nat.totient (witness n) = n := by
    have := h_cw.2
    exact of_decide_eq_true this
  exact ⟨h_pos, h_mod⟩
