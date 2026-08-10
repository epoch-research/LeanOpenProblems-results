import sys

critical_cases = {
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

cases_str = ""
for C, V in sorted(critical_cases.items()):
    cases_str += f"""          · -- x = {C}
            have h_g_{C} : A006368_map_inv {C} = {V} := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = {V} := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_{C} ▸ congr_arg A006368_map_inv h_eq_{C}
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt {V} (by decide)
            have h_E_85 := preimage_E_prime_iterate (n + 8) 85 h_E
            have h_not_E_85 : ¬ E_prime (A006368_map_inv^[1] 85) := by
              have h_ih_zero := ih 0 (by omega)
              have h_not_7 := h_ih_zero.2
              have h_not_6 := step_of_ge_not 239 (by decide) h_not_7
              have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
              have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
              have h_not_3 := step_of_ge_not 201 (by decide) h_not_4
              have h_not_2 := step_of_ge_not 151 (by decide) h_not_3
              exact step_of_ge_not 113 (by decide) h_not_2
            have h_g_85_E : E_prime (A006368_map_inv^[1] 85) := step_of_ge (by decide) h_E_85
            exact h_not_E_85 h_g_85_E
"""

content = f"""import FormalConjectures.Util.ProblemImports

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

lemma step_of_ge_not (x : ℕ) (hx : x ≥ 85) (h_not : ¬ E_prime (A006368_map_inv x)) : ¬ E_prime x := by
  intro h
  cases h with
  | lt y h1 => omega
  | step y h2 => exact h_not h2

lemma g_and_not_E_helper (k : ℕ) : A006368_map_inv^[k+7] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[k+7] 85) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have h_ge : A006368_map_inv^[k+7] 85 ≥ 85 := by
      by_contra h_lt
      push_neg at h_lt
      rw [Function.iterate_succ' A006368_map_inv (k+6)] at h_lt
      simp only [Function.comp_apply] at h_lt
      cases k with
      | zero =>
        -- g_6 85 = 239
        have h_g : A006368_map_inv^[6] 85 = 239 := by decide
        rw [h_g] at h_lt
        have h_g2 : A006368_map_inv 239 = 319 := by decide
        rw [h_g2] at h_lt
        omega
      | succ n =>
        have h_ge_n : A006368_map_inv^[n+7] 85 ≥ 85 := (ih n (by omega)).1
        by_cases h_not : A006368_map_inv^[n+7] 85 = 87 ∨ A006368_map_inv^[n+7] 85 = 90 ∨ A006368_map_inv^[n+7] 85 = 93 ∨ A006368_map_inv^[n+7] 85 = 96 ∨ A006368_map_inv^[n+7] 85 = 99 ∨ A006368_map_inv^[n+7] 85 = 102 ∨ A006368_map_inv^[n+7] 85 = 105 ∨ A006368_map_inv^[n+7] 85 = 108 ∨ A006368_map_inv^[n+7] 85 = 111 ∨ A006368_map_inv^[n+7] 85 = 114 ∨ A006368_map_inv^[n+7] 85 = 117 ∨ A006368_map_inv^[n+7] 85 = 120 ∨ A006368_map_inv^[n+7] 85 = 123 ∨ A006368_map_inv^[n+7] 85 = 126
        · rcases h_not with h_eq_87 | h_eq_90 | h_eq_93 | h_eq_96 | h_eq_99 | h_eq_102 | h_eq_105 | h_eq_108 | h_eq_111 | h_eq_114 | h_eq_117 | h_eq_120 | h_eq_123 | h_eq_126
{cases_str}
        · have h_not_conj : A006368_map_inv^[n+7] 85 ≠ 87 ∧ A006368_map_inv^[n+7] 85 ≠ 90 ∧ A006368_map_inv^[n+7] 85 ≠ 93 ∧ A006368_map_inv^[n+7] 85 ≠ 96 ∧ A006368_map_inv^[n+7] 85 ≠ 99 ∧ A006368_map_inv^[n+7] 85 ≠ 102 ∧ A006368_map_inv^[n+7] 85 ≠ 105 ∧ A006368_map_inv^[n+7] 85 ≠ 108 ∧ A006368_map_inv^[n+7] 85 ≠ 111 ∧ A006368_map_inv^[n+7] 85 ≠ 114 ∧ A006368_map_inv^[n+7] 85 ≠ 117 ∧ A006368_map_inv^[n+7] 85 ≠ 120 ∧ A006368_map_inv^[n+7] 85 ≠ 123 ∧ A006368_map_inv^[n+7] 85 ≠ 126 := by
            push_neg at h_not
            exact h_not
          have h_eq_add : n + 1 + 6 = n + 7 := by omega
          rw [h_eq_add] at h_lt
          have h_ge_n1 := g_ge_85 (A006368_map_inv^[n+7] 85) h_ge_n h_not_conj
          omega
    refine ⟨h_ge, ?_⟩
    intro h_E
    have h_P_ind : ∀ z, E_prime z → ¬ (∃ i < k + 7, A006368_map_inv^[i+1] 85 = z) := by
      intro z hz
      induction hz with
      | lt x h1 =>
        intro h_S
        rcases h_S with ⟨i, hi, h_eq⟩
        by_cases h_i : i = k + 6
        · rw [h_i] at h_eq
          rw [h_eq] at h_ge
          omega
        · have hi_lt : i < k + 6 := by omega
          have h_ge_i : A006368_map_inv^[i+1] 85 ≥ 85 := by
            by_cases hi_0 : i < 6
            · interval_cases i <;> decide
            · obtain ⟨m, rfl⟩ : ∃ m, i = m + 6 := ⟨i - 6, by omega⟩
              have h_eq_m : m < k := by omega
              have h_eq_s : m + 6 + 1 = m + 7 := by omega
              rw [h_eq_s]
              exact (ih m h_eq_m).1
          rw [h_eq] at h_ge_i
          omega
      | step x h ih_step =>
        intro h_S
        rcases h_S with ⟨i, hi, h_eq⟩
        by_cases h_i : i = k + 6
        · have h_eq_k2 : A006368_map_inv^[k+8] 85 = A006368_map_inv x := by
            rw [h_i] at h_eq
            rw [Function.iterate_succ' A006368_map_inv (k+7)]
            simp only [Function.comp_apply]
            rw [h_eq]
          have h_E_k2 : E_prime (A006368_map_inv^[k+8] 85) := by
            rw [h_eq_k2]
            exact h
          have h_E_85 := preimage_E_prime_iterate (k+8) 85 h_E_k2
          have h_g_85_E : E_prime (A006368_map_inv^[1] 85) := by
            cases h_E_85 with
            | lt y hy => omega
            | step y hy => exact hy
          have h_not_E_1 : ¬ E_prime (A006368_map_inv^[1] 85) := by
            have h_ih_zero := ih 0 (by omega)
            have h_not_7 := h_ih_zero.2
            have h_not_6 := step_of_ge_not 239 (by decide) h_not_7
            have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
            have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
            have h_not_3 := step_of_ge_not 201 (by decide) h_not_4
            have h_not_2 := step_of_ge_not 151 (by decide) h_not_3
            exact step_of_ge_not 113 (by decide) h_not_2
          exact h_not_E_1 h_g_85_E
        · have h_S_g : ∃ j < k + 7, A006368_map_inv^[j+1] 85 = A006368_map_inv x := by
            have hle : i + 1 < k + 7 := by omega
            use i + 1
            refine ⟨hle, ?_⟩
            rw [Function.iterate_succ' A006368_map_inv (i+1)]
            simp only [Function.comp_apply]
            rw [h_eq]
          exact ih_step h_S_g
    have h_E_85 := preimage_E_prime_iterate (k+7) 85 h_E
    have h_g_85_E : E_prime (A006368_map_inv^[1] 85) := by
      cases h_E_85 with
      | lt y hy => omega
      | step y hy => exact hy
    have h_exists : ∃ i < k + 7, A006368_map_inv^[i+1] 85 = A006368_map_inv^[1] 85 := by
      use 0
      refine ⟨by omega, rfl⟩
    exact h_P_ind (A006368_map_inv^[1] 85) h_g_85_E h_exists

theorem g_and_not_E (K : ℕ) : A006368_map_inv^[K+1] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[K+1] 85) := by
  by_cases hK : K ≥ 6
  · obtain ⟨k, rfl⟩ : ∃ k, K = k + 6 := ⟨K - 6, by omega⟩
    have h_eq : k + 6 + 1 = k + 7 := by omega
    rw [h_eq]
    exact g_and_not_E_helper k
  · interval_cases K
    · -- K = 0 (s(1) = 113)
      have h_not_7 := g_and_not_E_helper 0
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7.2
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
      have h_not_3 := step_of_ge_not 201 (by decide) h_not_4
      have h_not_2 := step_of_ge_not 151 (by decide) h_not_3
      have h_not_1 := step_of_ge_not 113 (by decide) h_not_2
      exact ⟨by decide, h_not_1⟩
    · -- K = 1 (s(2) = 151)
      have h_not_7 := g_and_not_E_helper 0
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7.2
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
      have h_not_3 := step_of_ge_not 201 (by decide) h_not_4
      have h_not_2 := step_of_ge_not 151 (by decide) h_not_3
      exact ⟨by decide, h_not_2⟩
    · -- K = 2 (s(3) = 201)
      have h_not_7 := g_and_not_E_helper 0
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7.2
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
      have h_not_3 := step_of_ge_not 201 (by decide) h_not_4
      exact ⟨by decide, h_not_3⟩
    · -- K = 3 (s(4) = 134)
      have h_not_7 := g_and_not_E_helper 0
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7.2
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
      exact ⟨by decide, h_not_4⟩
    · -- K = 4 (s(5) = 179)
      have h_not_7 := g_and_not_E_helper 0
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7.2
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      exact ⟨by decide, h_not_5⟩
    · -- K = 5 (s(6) = 239)
      have h_not_7 := g_and_not_E_helper 0
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7.2
      exact ⟨by decide, h_not_6⟩

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
    f.write(content)
print("SUCCESS")
