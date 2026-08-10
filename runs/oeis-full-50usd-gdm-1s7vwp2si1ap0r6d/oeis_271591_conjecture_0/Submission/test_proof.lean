import FormalConjectures.Util.ProblemImports

open Nat

def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

-- Monotonicity of tribonacci
theorem tribonacci_mono (n : ℕ) : tribonacci n ≤ tribonacci (n + 1) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | n
  · decide
  · decide
  · decide
  · simp only [tribonacci]
    omega

theorem tribonacci_upper_bound (n : ℕ) (hn : n ≥ 5) : tribonacci (n + 1) ≤ 2 * tribonacci n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | _ | _ | n
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  rcases n with _ | _ | _ | n
  · decide
  · decide
  · decide
  · simp only [tribonacci]
    have h1 : tribonacci (n + 5) = tribonacci (n + 4) + tribonacci (n + 3) + tribonacci (n + 2) := by rfl
    have h2 : tribonacci (n + 6) = tribonacci (n + 5) + tribonacci (n + 4) + tribonacci (n + 3) := by rfl
    omega

theorem tribonacci_gt_one (n : ℕ) (hn : n ≥ 5) : tribonacci n > 1 := by
  have h : tribonacci 5 ≤ tribonacci n := by
    -- we can use induction or just use tribonacci_mono
    -- actually, let's prove it by induction on n starting at 5
    induction' n, hn using Nat.le_induction with k hk ih
    · rfl
    · have := tribonacci_mono k
      omega
  have h5 : tribonacci 5 = 4 := by rfl
  omega

def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  if h : T ≤ 1 then
    0
  else
    let j_smsb : ℕ := T.log2 - 1
    if T.testBit j_smsb then 1 else 0

lemma a_val (k : ℕ) : a k = 0 ∨ a k = 1 := by
  simp only [a]
  split_ifs
  · left; rfl
  · right; rfl
  · left; rfl


def is_maximal_run (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  (∀ i : ℕ, i < L → a (n + i) = v) ∧
  (a (n + L) ≠ v) ∧
  (a (n - 1) ≠ v)


instance (v n L : ℕ) : Decidable (is_maximal_run v n L) := by
  unfold is_maximal_run
  infer_instance

theorem check_up_to_20 : ∀ n ∈ List.range 20, ∀ L ∈ List.range 20, n ≥ 2 → n + L < 20 → is_maximal_run 0 n L → L = 4 ∨ L = 5 := by
  decide



theorem tribonacci_ratio_inductive_step (A B C : ℕ)
  (h1 : 9 * A ≤ 5 * B) (h2 : 8 * B ≤ 15 * A)
  (h3 : 9 * B ≤ 5 * C) (h4 : 8 * C ≤ 15 * B) :
  9 * C ≤ 5 * (C + B + A) ∧ 8 * (C + B + A) ≤ 15 * C := by
  omega


def ratio_bounds (n : ℕ) : Prop :=
  9 * tribonacci n ≤ 5 * tribonacci (n + 1) ∧
  8 * tribonacci (n + 1) ≤ 15 * tribonacci n

def ratio_bounds_two (n : ℕ) : Prop :=
  ratio_bounds n ∧ ratio_bounds (n + 1)

theorem tribonacci_ratio_bounds_two (n : ℕ) (hn : n ≥ 6) : ratio_bounds_two n := by
  induction' n, hn using Nat.le_induction with k hk ih
  · -- base case k = 6
    unfold ratio_bounds_two ratio_bounds
    decide
  · -- inductive step
    rcases ih with ⟨hk1, hk2⟩
    refine ⟨hk2, ?_⟩
    unfold ratio_bounds
    have h_rec : tribonacci (k + 3) = tribonacci (k + 2) + tribonacci (k + 1) + tribonacci k := by rfl
    have h_ind := tribonacci_ratio_inductive_step (tribonacci k) (tribonacci (k + 1)) (tribonacci (k + 2))
      hk1.1 hk1.2 hk2.1 hk2.2
    change 9 * tribonacci (k + 2) ≤ 5 * tribonacci (k + 3) ∧ 8 * tribonacci (k + 3) ≤ 15 * tribonacci (k + 2)
    rw [h_rec]
    exact h_ind

theorem tribonacci_ratio_bounds (n : ℕ) (hn : n ≥ 6) : ratio_bounds n := by
  have := tribonacci_ratio_bounds_two n hn
  exact this.1



theorem case_test (T0 T1 T2 T3 X : ℕ)
  (h_rec : T3 = T2 + T1 + T0)
  (hT0_l : 2 * X ≤ T0) (hT0_u : T0 < 3 * X)
  (hT1_l : 3 * X ≤ T1) (hT1_u : T1 < 4 * X)
  (hT2_l : 3 * X ≤ T2) (hT2_u : T2 < 4 * X)
  (hT3_l : 2 * X ≤ T3) (hT3_u : T3 < 3 * X) :
  False := by
  omega



lemma tribonacci_5_step (n : ℕ) : tribonacci (n + 5) = 4 * tribonacci (n + 2) + 3 * tribonacci (n + 1) + 2 * tribonacci n := by
  have h1 : tribonacci (n + 3) = tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n := by rfl
  have h2 : tribonacci (n + 4) = tribonacci (n + 3) + tribonacci (n + 2) + tribonacci (n + 1) := by rfl
  have h3 : tribonacci (n + 5) = tribonacci (n + 4) + tribonacci (n + 3) + tribonacci (n + 2) := by rfl
  omega


lemma testBit_def (m n : ℕ) : m.testBit n = (1 &&& m >>> n != 0) := rfl


lemma log2_test (A : ℕ) (h : 16 ≤ A) : 4 ≤ A.log2 := by
  have hA : A ≠ 0 := by omega
  change 2^4 ≤ A at h
  rw [← Nat.le_log2 hA] at h
  exact h

lemma K_step (T1 T2 K1 K2 : ℕ)
  (hT1_l : 2^(K1+1) ≤ T1) (hT1_u : T1 < 2^(K1+2))
  (hT2_l : 2^(K2+1) ≤ T2) (hT2_u : T2 < 2^(K2+2))
  (h_ratio_l : 9 * T1 ≤ 5 * T2) (h_ratio_u : 8 * T2 ≤ 15 * T1) :
  K2 = K1 ∨ K2 = K1 + 1 := by
  by_contra h_or
  push_neg at h_or
  by_cases hk : K2 < K1
  · have h_pow : 2^(K2 + 2) ≤ 2^(K1 + 1) := by
      apply Nat.pow_le_pow_right (by decide)
      omega
    omega
  · have h_pow : 2^(K1 + 3) ≤ 2^(K2 + 1) := by
      apply Nat.pow_le_pow_right (by decide)
      omega
    have h_pow1 : 2^(K1 + 2) = 4 * 2^K1 := by ring
    have h_pow2 : 2^(K1 + 3) = 8 * 2^K1 := by ring
    have h_pow3 : 2^(K2 + 2) = 2 * 2^(K2 + 1) := by ring
    omega



lemma testBit_eq_odd (m n : ℕ) : m.testBit n = (m / 2^n % 2 == 1) := by
  rfl
