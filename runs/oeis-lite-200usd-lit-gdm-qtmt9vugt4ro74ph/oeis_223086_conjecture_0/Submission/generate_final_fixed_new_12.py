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
    cases_str += f"""          · have h_eq_n1 : A006368_map_inv^[n + 2] 85 = {V} := by
              rw [Function.iterate_succ' A006368_map_inv (n + 1)]
              simp only [Function.comp_apply]
              rw [h_eq_{C}]
              rfl
            have h_E : E_prime (A006368_map_inv^[n + 2] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt {V} (by decide)
            have h_E_85 := preimage_E_prime_iterate (n + 2) 85 h_E
            have h_g_85_E_1 : E_prime (A006368_map_inv^[1] 85) := step_of_ge (by decide) h_E_85
            have h_g_85_E_2 : E_prime (A006368_map_inv^[2] 85) := step_of_ge (by decide) h_g_85_E_1
            have h_g_85_E_3 : E_prime (A006368_map_inv^[3] 85) := step_of_ge (by decide) h_g_85_E_2
            have h_g_85_E_4 : E_prime (A006368_map_inv^[4] 85) := step_of_ge (by decide) h_g_85_E_3
            have h_g_85_E_5 : E_prime (A006368_map_inv^[5] 85) := step_of_ge (by decide) h_g_85_E_4
            have h_g_85_E_6 : E_prime (A006368_map_inv^[6] 85) := step_of_ge (by decide) h_g_85_E_5
            have h_not_E_85 : ¬ E_prime (A006368_map_inv^[6] 85) := (ih 5 (by omega) (by omega)).2
            exact h_not_E_85 h_g_85_E_6
"""

content = f"""import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option linter.unusedTactic false

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

lemma g_and_not_E_pos (k : ℕ) : k > 5 → A006368_map_inv^[k+1] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[k+1] 85) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have h_ge : A006368_map_inv^[k+1] 85 ≥ 85 := by
      by_contra h_lt
      push_neg at h_lt
      rcases Nat.exists_eq_succ_of_ne_zero (by omega) with ⟨n, rfl⟩
      have h_ge_n : A006368_map_inv^[n+1] 85 ≥ 85 := by
        by_cases hn : n > 5
        · exact (ih n (by omega) hn).1
        · have : n = 5 := by omega
          subst this
          decide
      by_cases hn5 : n = 5
      · subst hn5
        have h_not : A006368_map_inv^[6] 85 ≠ 87 ∧ A006368_map_inv^[6] 85 ≠ 90 ∧ A006368_map_inv^[6] 85 ≠ 93 ∧ A006368_map_inv^[6] 85 ≠ 96 ∧ A006368_map_inv^[6] 85 ≠ 99 ∧ A006368_map_inv^[6] 85 ≠ 102 ∧ A006368_map_inv^[6] 85 ≠ 105 ∧ A006368_map_inv^[6] 85 ≠ 108 ∧ A006368_map_inv^[6] 85 ≠ 111 ∧ A006368_map_inv^[6] 85 ≠ 114 ∧ A006368_map_inv^[6] 85 ≠ 117 ∧ A006368_map_inv^[6] 85 ≠ 120 ∧ A006368_map_inv^[6] 85 ≠ 123 ∧ A006368_map_inv^[6] 85 ≠ 126 := by decide
        have h_ge_2 := g_ge_85 (A006368_map_inv^[6] 85) h_ge_n h_not
        have h_eq : A006368_map_inv^[7] 85 = A006368_map_inv (A006368_map_inv^[6] 85) := rfl
        rw [h_eq] at h_lt
        exact (by decide : ¬ A006368_map_inv (A006368_map_inv^[6] 85) < 85) h_lt
      · -- n > 5
        by_cases h_not : A006368_map_inv^[n+1] 85 = 87 ∨ A006368_map_inv^[n+1] 85 = 90 ∨ A006368_map_inv^[n+1] 85 = 93 ∨ A006368_map_inv^[n+1] 85 = 96 ∨ A006368_map_inv^[n+1] 85 = 99 ∨ A006368_map_inv^[n+1] 85 = 102 ∨ A006368_map_inv^[n+1] 85 = 105 ∨ A006368_map_inv^[n+1] 85 = 108 ∨ A006368_map_inv^[n+1] 85 = 111 ∨ A006368_map_inv^[n+1] 85 = 114 ∨ A006368_map_inv^[n+1] 85 = 117 ∨ A006368_map_inv^[n+1] 85 = 120 ∨ A006368_map_inv^[n+1] 85 = 123 ∨ A006368_map_inv^[n+1] 85 = 126
        · rcases h_not with h_eq_87 | h_eq_90 | h_eq_93 | h_eq_96 | h_eq_99 | h_eq_102 | h_eq_105 | h_eq_108 | h_eq_111 | h_eq_114 | h_eq_117 | h_eq_120 | h_eq_123 | h_eq_126
{cases_str}        · have h_not_conj : A006368_map_inv^[n+1] 85 ≠ 87 ∧ A006368_map_inv^[n+1] 85 ≠ 90 ∧ A006368_map_inv^[n+1] 85 ≠ 93 ∧ A006368_map_inv^[n+1] 85 ≠ 96 ∧ A006368_map_inv^[n+1] 85 ≠ 99 ∧ A006368_map_inv^[n+1] 85 ≠ 102 ∧ A006368_map_inv^[n+1] 85 ≠ 105 ∧ A006368_map_inv^[n+1] 85 ≠ 108 ∧ A006368_map_inv^[n+1] 85 ≠ 111 ∧ A006368_map_inv^[n+1] 85 ≠ 114 ∧ A006368_map_inv^[n+1] 85 ≠ 117 ∧ A006368_map_inv^[n+1] 85 ≠ 120 ∧ A006368_map_inv^[n+1] 85 ≠ 123 ∧ A006368_map_inv^[n+1] 85 ≠ 126 := by
              push_neg at h_not
              exact h_not
            have h_ge_2 := g_ge_85 (A006368_map_inv^[n+1] 85) h_ge_n h_not_conj
            have h_eq : A006368_map_inv^[n+2] 85 = A006368_map_inv (A006368_map_inv^[n+1] 85) := rfl
            rw [h_eq] at h_lt
            omega
    refine ⟨h_ge, ?_⟩
    intro h_E
    have h_E_85 := preimage_E_prime_iterate (k+1) 85 h_E
    have h_g_85_E_1 : E_prime (A006368_map_inv^[1] 85) := step_of_ge (by decide) h_E_85
    have h_g_85_E_2 : E_prime (A006368_map_inv^[2] 85) := step_of_ge (by decide) h_g_85_E_1
    have h_g_85_E_3 : E_prime (A006368_map_inv^[3] 85) := step_of_ge (by decide) h_g_85_E_2
    have h_g_85_E_4 : E_prime (A006368_map_inv^[4] 85) := step_of_ge (by decide) h_g_85_E_3
    have h_g_85_E_5 : E_prime (A006368_map_inv^[5] 85) := step_of_ge (by decide) h_g_85_E_4
    have h_g_85_E_6 : E_prime (A006368_map_inv^[6] 85) := step_of_ge (by decide) h_g_85_E_5
    have h_not_E_85 : ¬ E_prime (A006368_map_inv^[6] 85) := (ih 5 (by omega) (by omega)).2
    exact h_not_E_85 h_g_85_E_6

theorem g_and_not_E (k : ℕ) : A006368_map_inv^[k+1] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[k+1] 85) := by
  by_cases hk : k ≤ 5
  · interval_cases k
    · -- k = 0 (s(1) = 113)
      have h_not_7 := g_and_not_E_pos 6 (by decide)
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
      have h_not_3 := step_of_ge_not 201 (by decide) h_not_4
      have h_not_2 := step_of_ge_not 151 (by decide) h_not_3
      have h_not_1 := step_of_ge_not 113 (by decide) h_not_2
      exact ⟨by decide, h_not_1⟩
    · -- k = 1 (s(2) = 151)
      have h_not_7 := g_and_not_E_pos 6 (by decide)
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
      have h_not_3 := step_of_ge_not 201 (by decide) h_not_4
      have h_not_2 := step_of_ge_not 151 (by decide) h_not_3
      exact ⟨by decide, h_not_2⟩
    · -- k = 2 (s(3) = 201)
      have h_not_7 := g_and_not_E_pos 6 (by decide)
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
      have h_not_3 := step_of_ge_not 201 (by decide) h_not_4
      exact ⟨by decide, h_not_3⟩
    · -- k = 3 (s(4) = 134)
      have h_not_7 := g_and_not_E_pos 6 (by decide)
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      have h_not_4 := step_of_ge_not 134 (by decide) h_not_5
      exact ⟨by decide, h_not_4⟩
    · -- k = 4 (s(5) = 179)
      have h_not_7 := g_and_not_E_pos 6 (by decide)
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7
      have h_not_5 := step_of_ge_not 179 (by decide) h_not_6
      exact ⟨by decide, h_not_5⟩
    · -- k = 5 (s(6) = 239)
      have h_not_7 := g_and_not_E_pos 6 (by decide)
      have h_eq : A006368_map_inv^[7] 85 = 319 := by decide
      rw [h_eq] at h_not_7
      have h_not_6 := step_of_ge_not 239 (by decide) h_not_7
      exact ⟨by decide, h_not_6⟩
  · have h_pos_k : k > 5 := by omega
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
    f.write(content)
print("Generated Spec.lean successfully!")
