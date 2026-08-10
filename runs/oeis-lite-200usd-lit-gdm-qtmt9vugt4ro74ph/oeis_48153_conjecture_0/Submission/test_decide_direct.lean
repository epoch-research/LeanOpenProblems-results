import FormalConjectures.Util.ProblemImports

open Finset

def sum_sq_div_loop (H : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc => sum_sq_div_loop H k (acc + (k ^ 2 / (2 * H)) % 2)

lemma sum_sq_div_loop_eq (H : ℕ) (n : ℕ) (acc : ℕ) :
    sum_sq_div_loop H n acc = acc + ∑ k ∈ range n, (k ^ 2 / (2 * H)) % 2 := by
  induction n generalizing acc with
  | zero => simp [sum_sq_div_loop]
  | succ n ih =>
    rw [sum_sq_div_loop]
    rw [ih]
    rw [sum_range_succ]
    omega

def P_bool_fast (H : ℕ) : Bool :=
  decide (sum_sq_div_loop H (2 * H) 0 ≤ H)

def test_all_fast : ℕ → Bool
  | 0 => P_bool_fast 0
  | n + 1 => P_bool_fast (n + 1) && test_all_fast n

lemma test_all_fast_spec (n : ℕ) : test_all_fast n = true → ∀ H ≤ n, ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 ≤ H := by
  induction n with
  | zero =>
    intro h H hH
    have : H = 0 := by omega
    subst this
    unfold test_all_fast at h
    unfold P_bool_fast at h
    have h_loop : sum_sq_div_loop 0 0 0 = ∑ k ∈ range 0, (k ^ 2 / (2 * 0)) % 2 := by
      rw [sum_sq_div_loop_eq]
      simp
    rw [← h_loop]
    exact of_decide_eq_true h
  | succ n ih =>
    intro h H hH
    unfold test_all_fast at h
    rw [Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩
    rcases eq_or_lt_of_le hH with rfl | h_lt
    · unfold P_bool_fast at h1
      have h_loop : sum_sq_div_loop (n + 1) (2 * (n + 1)) 0 = ∑ k ∈ range (2 * (n + 1)), (k ^ 2 / (2 * (n + 1))) % 2 := by
        rw [sum_sq_div_loop_eq]
        simp
      rw [← h_loop]
      exact of_decide_eq_true h1
    · have : H ≤ n := by omega
      exact ih h2 H this

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma sum_div_mod_two_le_decide_1000 : ∀ H, H ≤ 1000 → ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 ≤ H := by
  intro H hH
  apply test_all_fast_spec 1000 (by rfl) H hH
