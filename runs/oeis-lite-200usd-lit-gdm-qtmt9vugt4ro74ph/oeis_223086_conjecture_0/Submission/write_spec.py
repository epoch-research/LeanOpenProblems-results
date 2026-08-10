import os

bad_numbers = {
    87: 58,
    90: 60,
    93: 62,
    96: 64,
    99: 66,
    102: 68,
    105: 70,
    108: 72,
    111: 74,
    114: 76,
    117: 78,
    120: 80,
    123: 82,
    126: 84
}

cases_code = ""
for b, next_val in bad_numbers.items():
    cases_code += f"""          · have h_g_{b} : A006368_map_inv {b} = {next_val} := rfl
            have h_eq_n1 : A006368_map_inv^[n + 2] 85 = {next_val} := by
              rw [Function.iterate_succ' A006368_map_inv (n + 1)]
              exact h_g_{b} ▸ congr_arg A006368_map_inv h_eq_{b}
            have h_E : E_prime (A006368_map_inv^[n + 2] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt {next_val} (by decide)
            have h_E_85 := preimage_E_prime_iterate (n + 2) 85 h_E
            have h_not_E_85 : ¬ E_prime (A006368_map_inv^[2] 85) := (ih 1 (by omega) (by omega)).2
            have h_g_85_E_1 : E_prime (A006368_map_inv^[1] 85) := step_of_ge (by decide) h_E_85
            have h_g_85_E_2 : E_prime (A006368_map_inv^[2] 85) := step_of_ge (by decide) h_g_85_E_1
            exact h_not_E_85 h_g_85_E_2
"""

full_file = f"""import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000

open Nat

def A006368_map (k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (3 * k) / 2
  else if k % 4 = 1 then
    (3 * k + 1) / 4
  else -- k % 4 = 3
    (3 * k - 1) / 4

def A006368_map_inv (m : ℕ) : ℕ :=
  if m % 3 = 0 then
    2 * (m / 3)
  else if m % 3 = 1 then
    4 * (m / 3) + 1
  else
    4 * (m / 3) + 3

lemma A006368_map_left_inverse : Function.LeftInverse A006368_map_inv A006368_map := by
  intro x
  unfold A006368_map A006368_map_inv
  split_ifs <;> omega

lemma A006368_map_right_inverse : Function.RightInverse A006368_map_inv A006368_map := by
  intro x
  unfold A006368_map A006368_map_inv
  split_ifs <;> omega

lemma A006368_map_injective : Function.Injective A006368_map :=
  A006368_map_left_inverse.injective

lemma iterate_inv_step {{α : Type*}} (f g : α → α) (hinv : Function.LeftInverse g f) (x : α) (d k : ℕ) (hk : k ≤ d) :
  f^[d] x = x → f^[d - k] x = g^[k] x := by
  induction k with
  | zero =>
    intro h
    rw [Nat.sub_zero]
    exact h
  | succ k ih =>
    intro h
    have hle : k ≤ d := by omega
    have h_ih := ih hle h
    have h_eq : d - k = d - (k + 1) + 1 := by omega
    rw [h_eq] at h_ih
    rw [Function.iterate_succ' f (d - (k + 1))] at h_ih
    rw [Function.comp_apply] at h_ih
    have h_g := congr_arg g h_ih
    rw [hinv (f^[d - (k + 1)] x)] at h_g
    rw [Function.iterate_succ' g k]
    exact h_g

def a (n : ℕ) : ℕ :=
  Nat.iterate A006368_map (n - 1) 64

lemma iterate_comm {{α : Type*}} (f : α → α) (n : ℕ) (x : α) : f^[n + 1] x = f^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ]
    rfl

lemma g_ge_85 (m : ℕ) (h1 : m ≥ 85)
  (h2 : m ≠ 87 ∧ m ≠ 90 ∧ m ≠ 93 ∧ m ≠ 96 ∧ m ≠ 99 ∧ m ≠ 102 ∧ m ≠ 105 ∧ m ≠ 108 ∧ m ≠ 111 ∧ m ≠ 114 ∧ m ≠ 117 ∧ m ≠ 120 ∧ m ≠ 123 ∧ m ≠ 126) :
  A006368_map_inv m ≥ 85 := by
  unfold A006368_map_inv
  split_ifs with h_mod0 h_mod1
  · -- m % 3 = 0
    have : m ≥ 129 := by omega
    omega
  · -- m % 3 = 1
    omega
  · -- m % 3 = 2
    omega

lemma f_g_iterate (n : ℕ) (x : ℕ) : A006368_map^[n] (A006368_map_inv^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h_g_succ : A006368_map_inv^[n + 1] x = A006368_map_inv^[n] (A006368_map_inv x) := by
      rw [Function.iterate_succ]
      rfl
    rw [h_g_succ]
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
    rw [ih (A006368_map_inv x)]
    exact A006368_map_right_inverse x

inductive E_prime : ℕ → Prop where
  | lt (x : ℕ) (h1 : x < 85) : E_prime x
  | step (x : ℕ) (h : E_prime (A006368_map_inv x)) : E_prime x

lemma preimage_E_prime_iterate (k : ℕ) (x : ℕ) (h : E_prime (A006368_map_inv^[k] x)) : E_prime x := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ'] at h
    exact ih (E_prime.step _ h)

lemma step_of_ge {{x : ℕ}} (hx : x ≥ 85) (h : E_prime x) : E_prime (A006368_map_inv x) := by
  cases h with
  | lt y h1 => omega
  | step y h2 => exact h2

lemma E_prime_iff (y : ℕ) : E_prime y ↔ ∃ n, A006368_map_inv^[n] y < 85 := by
  constructor
  · intro h
    induction h with
    | lt x h1 =>
      use 0
      exact h1
    | step x h ih =>
      rcases ih with ⟨n, hn⟩
      use n + 1
      rw [iterate_comm]
      exact hn
  · intro h
    rcases h with ⟨n, hn⟩
    induction n generalizing y with
    | zero =>
      exact E_prime.lt y hn
    | succ n ih =>
      have hn2 : A006368_map_inv^[n] (A006368_map_inv y) < 85 := by
        rw [iterate_comm] at hn
        exact hn
      exact E_prime.step y (ih (A006368_map_inv y) hn2)

lemma g_and_not_E_pos (k : ℕ) (hk : k > 0) : A006368_map_inv^[k+1] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[k+1] 85) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have h_ge : A006368_map_inv^[k+1] 85 ≥ 85 := by
      by_contra h_lt
      push_neg at h_lt
      rw [Function.iterate_succ' A006368_map_inv k] at h_lt
      simp only [Function.comp_apply] at h_lt
      revert h_lt
      cases k with
      | zero =>
        intro h_lt
        omega
      | succ n =>
        intro h_lt
        have h_ge_n : A006368_map_inv^[n+1] 85 ≥ 85 := by
          by_cases hn : n = 0
          · subst hn; decide
          · exact (ih n (by omega) (by omega)).1
        by_cases hn0 : n = 0
        · subst hn0
          have h_not : A006368_map_inv^[1] 85 ≠ 87 ∧ A006368_map_inv^[1] 85 ≠ 90 ∧ A006368_map_inv^[1] 85 ≠ 93 ∧ A006368_map_inv^[1] 85 ≠ 96 ∧ A006368_map_inv^[1] 85 ≠ 99 ∧ A006368_map_inv^[1] 85 ≠ 102 ∧ A006368_map_inv^[1] 85 ≠ 105 ∧ A006368_map_inv^[1] 85 ≠ 108 ∧ A006368_map_inv^[1] 85 ≠ 111 ∧ A006368_map_inv^[1] 85 ≠ 114 ∧ A006368_map_inv^[1] 85 ≠ 117 ∧ A006368_map_inv^[1] 85 ≠ 120 ∧ A006368_map_inv^[1] 85 ≠ 123 ∧ A006368_map_inv^[1] 85 ≠ 126 := by decide
          have h_ge_2 := g_ge_85 (A006368_map_inv^[1] 85) h_ge_n h_not
          have h_eq : A006368_map_inv^[2] 85 = A006368_map_inv (A006368_map_inv^[1] 85) := rfl
          rw [← h_eq] at h_ge_2
          simp only [zero_add] at *
          omega
        · by_cases h_not : A006368_map_inv^[n+1] 85 = 87 ∨ A006368_map_inv^[n+1] 85 = 90 ∨ A006368_map_inv^[n+1] 85 = 93 ∨ A006368_map_inv^[n+1] 85 = 96 ∨ A006368_map_inv^[n+1] 85 = 99 ∨ A006368_map_inv^[n+1] 85 = 102 ∨ A006368_map_inv^[n+1] 85 = 105 ∨ A006368_map_inv^[n+1] 85 = 108 ∨ A006368_map_inv^[n+1] 85 = 111 ∨ A006368_map_inv^[n+1] 85 = 114 ∨ A006368_map_inv^[n+1] 85 = 117 ∨ A006368_map_inv^[n+1] 85 = 120 ∨ A006368_map_inv^[n+1] 85 = 123 ∨ A006368_map_inv^[n+1] 85 = 126
          rcases h_not with h_eq_87 | h_eq_90 | h_eq_93 | h_eq_96 | h_eq_99 | h_eq_102 | h_eq_105 | h_eq_108 | h_eq_111 | h_eq_114 | h_eq_117 | h_eq_120 | h_eq_123 | h_eq_126
{cases_code}          · have h_not_conj : A006368_map_inv^[n+1] 85 ≠ 87 ∧ A006368_map_inv^[n+1] 85 ≠ 90 ∧ A006368_map_inv^[n+1] 85 ≠ 93 ∧ A006368_map_inv^[n+1] 85 ≠ 96 ∧ A006368_map_inv^[n+1] 85 ≠ 99 ∧ A006368_map_inv^[n+1] 85 ≠ 102 ∧ A006368_map_inv^[n+1] 85 ≠ 105 ∧ A006368_map_inv^[n+1] 85 ≠ 108 ∧ A006368_map_inv^[n+1] 85 ≠ 111 ∧ A006368_map_inv^[n+1] 85 ≠ 114 ∧ A006368_map_inv^[n+1] 85 ≠ 117 ∧ A006368_map_inv^[n+1] 85 ≠ 120 ∧ A006368_map_inv^[n+1] 85 ≠ 123 ∧ A006368_map_inv^[n+1] 85 ≠ 126 := by
              push_neg at h_not
              exact h_not
            have h_ge_n1 := g_ge_85 (A006368_map_inv^[n+1] 85) h_ge_n h_not_conj
            omega
    refine ⟨h_ge, ?_⟩
    intro h_E
    have h_P_ind : ∀ z, E_prime z → ¬ (∃ i < k, A006368_map_inv^[i+1] 85 = z) := by
      intro z hz
      induction hz with
      | lt x h1 =>
        intro h_S
        rcases h_S with ⟨i, hi, h_eq⟩
        have h_ge_i : A006368_map_inv^[i+1] 85 ≥ 85 := by
          by_cases hi0 : i = 0
          · subst hi0; decide
          · exact (ih i hi (by omega)).1
        rw [h_eq] at h_ge_i
        omega
      | step x h ih_step =>
        intro h_S
        rcases h_S with ⟨i, hi, h_eq⟩
        by_cases h_i : i + 1 < k
        · have h_S_g : ∃ j < k, A006368_map_inv^[j+1] 85 = A006368_map_inv x := by
            use i + 1
            refine ⟨h_i, ?_⟩
            rw [Function.iterate_succ' A006368_map_inv (i+1)]
            simp only [Function.comp_apply]
            rw [h_eq]
          exact ih_step h_S_g
        · have h_eq_k : i + 1 = k := by omega
          have h_E_k1 : E_prime (A006368_map_inv^[k+1] 85) := by
            have : A006368_map_inv^[k+1] 85 = A006368_map_inv x := by
              rw [← h_eq_k]
              rw [Function.iterate_succ' A006368_map_inv (i+1)]
              simp only [Function.comp_apply]
              rw [h_eq]
            rw [this]
            exact h
          have h_E_85 := preimage_E_prime_iterate (k+1) 85 h_E_k1
          by_cases hk1 : k = 1
          · subst hk1
            have h_E_85_1 := preimage_E_prime_iterate 2 85 h_E_k1
            rw [E_prime_iff] at h_E_85_1
            rcases h_E_85_1 with ⟨M, hM⟩
            have h_M_pos : M > 0 := by
              by_contra h_zero
              have : M = 0 := by omega
              rw [this] at hM
              simp only [Function.iterate_zero, id_eq] at hM
              omega
            rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_M_pos) with ⟨d, hd⟩
            subst hd
            by_cases hd0 : d = 0
            · subst hd0; revert hM; decide
            · by_cases hd1 : d = 1
              · subst hd1; revert hM; decide
              · have h_pos_d : d > 0 := by omega
                have h_ge_pos := (g_and_not_E_pos d h_pos_d).1
                change A006368_map_inv^[d+1] 85 < 85 at hM
                omega
          · have h_k_gt_1 : 1 < k := by omega
            have h_E_2 : E_prime (A006368_map_inv^[2] 85) := by
              have h_E_1 := step_of_ge (by decide) h_E_85
              exact step_of_ge (by decide) h_E_1
            have h_not_E_2 : ¬ E_prime (A006368_map_inv^[2] 85) := (ih 1 h_k_gt_1 (by omega)).2
            exact h_not_E_2 h_E_2
    have h_E_85 := preimage_E_prime_iterate (k+1) 85 h_E
    have h_g_85_E : E_prime (A006368_map_inv^[1] 85) := by
      cases h_E_85 with
      | lt y hy => omega
      | step y hy => exact hy
    have h_exists : ∃ i < k, A006368_map_inv^[i+1] 85 = A006368_map_inv^[1] 85 := ⟨0, hk, rfl⟩
    exact h_P_ind (A006368_map_inv^[1] 85) h_g_85_E h_exists

theorem g_and_not_E (k : ℕ) : A006368_map_inv^[k+1] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[k+1] 85) := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨by decide, ?_⟩
    intro h_E
    have h_E_85 := preimage_E_prime_iterate 1 85 h_E
    rw [E_prime_iff] at h_E_85
    rcases h_E_85 with ⟨M, hM⟩
    have h_M_pos : M > 0 := by
      by_contra h_zero
      have : M = 0 := by omega
      rw [this] at hM
      simp only [Function.iterate_zero, id_eq] at hM
      omega
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_M_pos) with ⟨d, hd⟩
    subst hd
    by_cases hd0 : d = 0
    · subst hd0; revert hM; decide
    · have h_pos_d : d > 0 := by omega
      have h_ge_pos := (g_and_not_E_pos d h_pos_d).1
      change A006368_map_inv^[d+1] 85 < 85 at hM
      omega
  · have h_pos_k : k > 0 := by omega
    exact g_and_not_E_pos k h_pos_k

lemma g_iterate_85_ge_85 (k : ℕ) : A006368_map_inv^[k] 85 ≥ 85 := by
  cases k with
  | zero => simp
  | succ d => exact (g_and_not_E d).1

lemma iterate_64_inj (d : ℕ) : A006368_map^[d] 64 = 64 → d = 0 := by
  intro h
  cases d with
  | zero => rfl
  | succ d_prime =>
    have h_eq : A006368_map^[d_prime + 1 - (d_prime + 1)] 64 = A006368_map_inv^[d_prime + 1] 64 := by
      apply iterate_inv_step A006368_map A006368_map_inv A006368_map_left_inverse 64 (d_prime + 1) (d_prime + 1) (by omega) h
    rw [Nat.sub_self] at h_eq
    simp only [Function.iterate_zero, id_eq] at h_eq
    have h_eq2 : A006368_map_inv^[d_prime + 1] 64 = A006368_map_inv^[d_prime] (A006368_map_inv 64) := by
      exact iterate_comm A006368_map_inv d_prime 64
    have h_inv_64 : A006368_map_inv 64 = 85 := by
      unfold A006368_map_inv; rfl
    rw [h_inv_64] at h_eq2
    rw [h_eq2] at h_eq
    have h_ge := g_iterate_85_ge_85 d_prime
    rw [← h_eq] at h_ge
    omega

theorem oeis_223086_conjecture_0 :
  ∀ (i j : ℕ), 0 < i → 0 < j → a i = a j → i = j := by
  intro i j hi hj h
  rcases lt_trichotomy i j with hij | hij | hij
  · -- i < j
    have hd : j - i > 0 := Nat.sub_pos_of_lt hij
    have h_eq : A006368_map^[i-1] 64 = A006368_map^[i-1 + (j - i)] 64 := by
      unfold a at h
      have : i - 1 + (j - i) = j - 1 := by omega
      rw [this]
      exact h
    have h_eq2 : A006368_map^[i-1] 64 = A006368_map^[i-1] (A006368_map^[j-i] 64) := by
      rw [← Function.iterate_add_apply]
      exact h_eq
    have h_inj : Function.Injective (A006368_map^[i-1]) := by
      exact A006368_map_injective.iterate (i - 1)
    have h_same : 64 = A006368_map^[j-i] 64 := h_inj h_eq2
    have h_d_zero : j - i = 0 := iterate_64_inj (j - i) h_same.symm
    omega
  · exact hij
  · -- j < i
    have hd : i - j > 0 := Nat.sub_pos_of_lt hij
    have h_eq : A006368_map^[j-1] 64 = A006368_map^[j-1 + (i - j)] 64 := by
      unfold a at h
      have : j - 1 + (i - j) = i - 1 := by omega
      rw [this]
      exact h.symm
    have h_eq2 : A006368_map^[j-1] 64 = A006368_map^[j-1] (A006368_map^[i-j] 64) := by
      rw [← Function.iterate_add_apply]
      exact h_eq
    have h_inj : Function.Injective (A006368_map^[j-1]) := by
      exact A006368_map_injective.iterate (j - 1)
    have h_same : 64 = A006368_map^[i-j] 64 := h_inj h_eq2
    have h_d_zero : i - j = 0 := iterate_64_inj (i - j) h_same.symm
    omega
"""

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(full_file)

print("Spec.lean successfully generated and written!")
