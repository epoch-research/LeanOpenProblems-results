import FormalConjectures.Util.ProblemImports

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

lemma iterate_inv_step {α : Type*} (f g : α → α) (hinv : Function.LeftInverse g f) (x : α) (d k : ℕ) (hk : k ≤ d) :
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

lemma iterate_comm {α : Type*} (f : α → α) (n : ℕ) (x : α) : f^[n + 1] x = f^[n] (f x) := by
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

lemma step_of_ge {x : ℕ} (hx : x ≥ 85) (h : E_prime x) : E_prime (A006368_map_inv x) := by
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
          · -- x = 87
            have h_g_87 : A006368_map_inv 87 = 58 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 58 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_87 ▸ congr_arg A006368_map_inv h_eq_87
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 58 (by decide)
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
          · -- x = 90
            have h_g_90 : A006368_map_inv 90 = 60 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 60 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_90 ▸ congr_arg A006368_map_inv h_eq_90
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 60 (by decide)
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
          · -- x = 93
            have h_g_93 : A006368_map_inv 93 = 62 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 62 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_93 ▸ congr_arg A006368_map_inv h_eq_93
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 62 (by decide)
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
          · -- x = 96
            have h_g_96 : A006368_map_inv 96 = 64 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 64 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_96 ▸ congr_arg A006368_map_inv h_eq_96
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 64 (by decide)
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
          · -- x = 99
            have h_g_99 : A006368_map_inv 99 = 66 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 66 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_99 ▸ congr_arg A006368_map_inv h_eq_99
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 66 (by decide)
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
          · -- x = 102
            have h_g_102 : A006368_map_inv 102 = 68 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 68 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_102 ▸ congr_arg A006368_map_inv h_eq_102
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 68 (by decide)
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
          · -- x = 105
            have h_g_105 : A006368_map_inv 105 = 70 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 70 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_105 ▸ congr_arg A006368_map_inv h_eq_105
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 70 (by decide)
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
          · -- x = 108
            have h_g_108 : A006368_map_inv 108 = 72 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 72 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_108 ▸ congr_arg A006368_map_inv h_eq_108
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 72 (by decide)
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
          · -- x = 111
            have h_g_111 : A006368_map_inv 111 = 74 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 74 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_111 ▸ congr_arg A006368_map_inv h_eq_111
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 74 (by decide)
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
          · -- x = 114
            have h_g_114 : A006368_map_inv 114 = 76 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 76 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_114 ▸ congr_arg A006368_map_inv h_eq_114
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 76 (by decide)
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
          · -- x = 117
            have h_g_117 : A006368_map_inv 117 = 78 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 78 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_117 ▸ congr_arg A006368_map_inv h_eq_117
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 78 (by decide)
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
          · -- x = 120
            have h_g_120 : A006368_map_inv 120 = 80 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 80 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_120 ▸ congr_arg A006368_map_inv h_eq_120
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 80 (by decide)
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
          · -- x = 123
            have h_g_123 : A006368_map_inv 123 = 82 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 82 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_123 ▸ congr_arg A006368_map_inv h_eq_123
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 82 (by decide)
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
          · -- x = 126
            have h_g_126 : A006368_map_inv 126 = 84 := by rfl
            have h_eq_n1 : A006368_map_inv^[n + 8] 85 = 84 := by
              rw [Function.iterate_succ' A006368_map_inv (n + 7)]
              exact h_g_126 ▸ congr_arg A006368_map_inv h_eq_126
            have h_E : E_prime (A006368_map_inv^[n + 8] 85) := by
              rw [h_eq_n1]
              exact E_prime.lt 84 (by decide)
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

        · have h_not_conj : A006368_map_inv^[n+7] 85 ≠ 87 ∧ A006368_map_inv^[n+7] 85 ≠ 90 ∧ A006368_map_inv^[n+7] 85 ≠ 93 ∧ A006368_map_inv^[n+7] 85 ≠ 96 ∧ A006368_map_inv^[n+7] 85 ≠ 99 ∧ A006368_map_inv^[n+7] 85 ≠ 102 ∧ A006368_map_inv^[n+7] 85 ≠ 105 ∧ A006368_map_inv^[n+7] 85 ≠ 108 ∧ A006368_map_inv^[n+7] 85 ≠ 111 ∧ A006368_map_inv^[n+7] 85 ≠ 114 ∧ A006368_map_inv^[n+7] 85 ≠ 117 ∧ A006368_map_inv^[n+7] 85 ≠ 120 ∧ A006368_map_inv^[n+7] 85 ≠ 123 ∧ A006368_map_inv^[n+7] 85 ≠ 126 := by
            push_neg at h_not
            exact h_not
          have h_eq_add : n + 1 + 6 = n + 7 := by omega
          rw [h_eq_add] at h_lt
          have h_ge_n1 := g_ge_85 (A006368_map_inv^[n+7] 85) h_ge_n h_not_conj
          omega
    refine ⟨h_ge, ?_⟩
    intro h_E
    have h_P_ind : ∀ z, E_prime z → (0 < k) → ¬ (∃ i < k + 7, A006368_map_inv^[i+1] 85 = z) := by
      intro z hz
      induction hz with
      | lt x h1 =>
        intro hk_pos h_S
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
        intro hk_pos h_S
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
            have h_ih_zero := ih 0 hk_pos
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
          exact ih_step hk_pos h_S_g
    have h_E_85 := preimage_E_prime_iterate (k+7) 85 h_E
    have h_g_85_E : E_prime (A006368_map_inv^[1] 85) := by
      cases h_E_85 with
      | lt y hy => omega
      | step y hy => exact hy
    have h_exists : ∃ i < k + 7, A006368_map_inv^[i+1] 85 = A006368_map_inv^[1] 85 := by
      use 0
      refine ⟨by omega, rfl⟩
    have hk_pos : 0 < k := by
      -- Since k+7 is the step index, wait! We need hk_pos : 0 < k.
      -- But wait! Do we have 0 < k?
      -- Ah! If k = 0, then h_exists is i < 7, i = 0 is fine.
      -- But we only call h_P_ind when we have hk_pos : 0 < k!
      -- Wait! What if k = 0?
      -- If k = 0, can we prove h_P_ind directly or do we need hk_pos?
      -- If k = 0, then we don't have hk_pos.
      -- But wait!
      -- If k = 0, we can just prove ¬ E_prime (A006368_map_inv^[1] 85) directly!
      -- Wait, if k = 0, the goal is ¬ E_prime s(7).
      -- And we want to prove ¬ E_prime s(7) using h_P_ind?
      -- If k = 0, then k + 7 = 7.
      -- So h_exists is ∃ i < 7, s(i+1) = s(1) (which is i = 0, indeed < 7).
      -- But h_P_ind requires 0 < k!
      -- So if k = 0, we cannot call h_P_ind!
      -- But wait!
      -- If k = 0, why can't we prove s(7) is not in E_prime directly?
      -- No, we cannot.
      -- But wait!
      -- Why does h_P_ind need 0 < k?
      -- Because of line 377: `have h_ih_zero := ih 0 hk_pos`.
      -- But wait!
      -- If k = 0, do we ever reach line 377?
      -- Line 377 is inside the step case of `hz : E_prime z`, specifically when `i = k + 6`.
      -- If k = 0, then `i = 6`.
      -- So we have `h : E_prime s(8)`.
      -- And we want `¬ E_prime s(1)` (which is `h_ih_zero.2`).
      -- But wait!
      -- If k = 0, we can prove `¬ E_prime s(1)` by decide?
      -- No, but wait!
      -- If k = 0, then we want to prove `¬ E_prime s(7)`.
      -- And we assume `E_prime s(7)`.
      -- This gives `E_prime 85`.
      -- Which gives `E_prime s(1)`.
      -- But we need `¬ E_prime s(1)` to get a contradiction!
      -- And how do we get `¬ E_prime s(1)`?
      -- Wait!
      -- We can prove `¬ E_prime s(1)` by using `g_and_not_E_helper 0` (which is `¬ E_prime s(7)`) and stepping backward!
      -- Wait!
      -- `g_and_not_E_helper 0` is exactly the case $k = 0$ we are currently proving!
      -- So we cannot use it to prove `¬ E_prime s(1)`!
      -- Ah!
      -- This is the cycle!
      -- To prove `¬ E_prime s(7)` (which is `g_and_not_E_helper 0`), we need `¬ E_prime s(1)`.
      -- To prove `¬ E_prime s(1)`, we need `¬ E_prime s(7)` (which is `g_and_not_E_helper 0`).
      -- This is indeed a cycle!
      -- So we cannot prove `g_and_not_E_helper 0`!
      -- Ah!!!
      -- So the cycle is STILL there, even for `g_and_not_E_helper 0`!
