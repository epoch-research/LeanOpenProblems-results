import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Real

-- Mock definitions for testing
axiom a : ℕ → ℤ
axiom a_fast : ℕ → ℤ
axiom a_eq_a_fast (n : ℕ) : a n = a_fast n
axiom a_fast_402256 : a_fast 402256 = -76

lemma N_gt_of_neg (N : ℕ) (hN : ∀ n : ℕ, n ≥ N → (a n : ℝ) > Real.sqrt (n : ℝ)) (M : ℕ) (hM : a_fast M < 0) : N > M := by
  by_contra h_le
  push_neg at h_le
  have h_val : a M = a_fast M := a_eq_a_fast M
  have h_lt : a M < 0 := by
    rw [h_val]
    exact hM
  have h_ge : (a M : ℝ) > Real.sqrt (M : ℝ) := by
    apply hN
    omega
  have h_sqrt_nonneg : Real.sqrt (M : ℝ) ≥ 0 := Real.sqrt_nonneg (M : ℝ)
  have h_real : (a M : ℝ) < 0 := by
    exact_mod_cast h_lt
  linarith

lemma exists_N_min (h : ∃ N, ∀ n ≥ N, (a n : ℝ) > Real.sqrt (n : ℝ)) :
    ∃ N_min, (∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ)) ∧ (∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ)) := by
  classical
  let N_min := Nat.find h
  have h1 : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ) := Nat.find_spec h
  have h2 : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ) := fun m hm => Nat.find_min h hm
  exact ⟨N_min, h1, h2⟩

lemma exists_counterexample (N_min : ℕ)
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (m : ℕ) (h : m < N_min) : ∃ n ≥ m, (a n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h_fail := h_min m h
  push_neg at h_fail
  exact h_fail

noncomputable def M_seq (N_min : ℕ) (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ)) : ℕ → ℕ
  | 0 => 402256
  | k + 1 =>
    let prev := M_seq N_min h_min k
    if h : prev + 1 < N_min then
      Classical.choose (exists_counterexample N_min h_min (prev + 1) h)
    else
      N_min - 1

lemma M_seq_spec (N_min : ℕ)
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (k : ℕ) (h : M_seq N_min h_min k + 1 < N_min) :
    M_seq N_min h_min (k+1) ≥ M_seq N_min h_min k + 1 ∧ (a (M_seq N_min h_min (k+1)) : ℝ) ≤ Real.sqrt (M_seq N_min h_min (k+1) : ℝ) := by
  have h_eq : M_seq N_min h_min (k+1) = Classical.choose (exists_counterexample N_min h_min (M_seq N_min h_min k + 1) h) := by
    rw [M_seq]
    rw [dif_pos h]
  rw [h_eq]
  exact Classical.choose_spec (exists_counterexample N_min h_min (M_seq N_min h_min k + 1) h)

lemma M_seq_lt (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_gt : N_min > 402257)
    (k : ℕ) : M_seq N_min h_min k < N_min := by
  induction k with
  | zero =>
    simp [M_seq]
    omega
  | succ k ih =>
    by_cases h : M_seq N_min h_min k + 1 < N_min
    · have h_spec := M_seq_spec N_min h_min k h
      by_contra h_ge
      push_neg at h_ge
      have h_gt_n : (a (M_seq N_min h_min (k+1)) : ℝ) > Real.sqrt (M_seq N_min h_min (k+1) : ℝ) := hN_min (M_seq N_min h_min (k+1)) h_ge
      have h_le_n := h_spec.2
      linarith
    · rw [M_seq]
      rw [dif_neg h]
      omega

lemma M_seq_ge (N_min : ℕ)
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_gt : N_min > 402257)
    (k : ℕ) (hk : k < N_min - 402256) : M_seq N_min h_min k ≥ 402256 + k := by
  induction k with
  | zero =>
    simp [M_seq]
  | succ k ih =>
    have hk_succ : k < N_min - 402256 := by omega
    have ih_val := ih hk_succ
    by_cases h : M_seq N_min h_min k + 1 < N_min
    · have h_spec := M_seq_spec N_min h_min k h
      omega
    · rw [M_seq]
      rw [dif_neg h]
      omega

lemma N_min_contradiction (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_gt : N_min > 402257) : False := by
  have h_ge_K : N_min - 402256 - 1 < N_min - 402256 := by omega
  have h_lt := M_seq_lt N_min hN_min h_min h_gt (N_min - 402256 - 1)
  have h_ge := M_seq_ge N_min h_min h_gt (N_min - 402256 - 1) h_ge_K
  have h_branch : M_seq N_min h_min (N_min - 402256 - 1) + 1 < N_min := by
    by_contra h_neg
    have h_eq : M_seq N_min h_min (N_min - 402256 - 1) = N_min - 1 := by omega
    have h_next : M_seq N_min h_min (N_min - 402256) = N_min - 1 := by
      have h_eq_succ : N_min - 402256 = (N_min - 402256 - 1) + 1 := by omega
      rw [h_eq_succ]
      rw [M_seq]
      rw [dif_neg h_neg]
    have h_lt_next := M_seq_lt N_min hN_min h_min h_gt (N_min - 402256)
    omega
  have h_arith : 402256 + (N_min - 402256 - 1) = N_min - 1 := by omega
  rw [h_arith] at h_ge
  have h_spec := M_seq_spec N_min h_min (N_min - 402256 - 1) h_branch
  have h_spec1 := h_spec.1
  have h_eq_succ : N_min - 402256 = (N_min - 402256 - 1) + 1 := by omega
  rw [← h_eq_succ] at h_spec1
  have h_lt_next := M_seq_lt N_min hN_min h_min h_gt (N_min - 402256)
  omega

theorem oeis_71532_conjecture_0.disproof : ¬ ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  rintro ⟨N, hN⟩
  have hN_Real : ∃ N, ∀ n ≥ N, (a n : ℝ) > Real.sqrt (n : ℝ) := ⟨N, hN⟩
  obtain ⟨N_min, hN_min, h_min⟩ := exists_N_min hN_Real
  have h_gt : N_min > 402257 := sorry
  exact N_min_contradiction N_min hN_min h_min h_gt
