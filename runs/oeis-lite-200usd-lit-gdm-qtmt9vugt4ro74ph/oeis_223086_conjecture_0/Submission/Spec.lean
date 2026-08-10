import FormalConjectures.Util.ProblemImports

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

def Is_Backward_85 (x : ℕ) : Bool :=
  x = 85 || x = 113 || x = 151 || x = 201 || x = 134 || x = 179 || x = 239 || x = 319 || x = 425 || x = 567 || x = 378 || x = 252 || x = 168 || x = 112 || x = 149 || x = 199

inductive E_prime : ℕ → Prop where
  | lt (x : ℕ) (h1 : x < 85) (h2 : x ≠ 64) : E_prime x
  | step (x : ℕ) (h : E_prime (A006368_map_inv x)) (h_neq : Is_Backward_85 x = false) : E_prime x
  | base_96 : E_prime 96

lemma not_E_prime_of_is_backward {x : ℕ} (h_back : Is_Backward_85 x = true) : ¬ E_prime x := by
  intro h
  induction h with
  | lt x h1 h2 =>
    interval_cases x <;> (revert h_back; decide)
  | step x h h_neq ih =>
    rw [h_neq] at h_back
    contradiction
  | base_96 =>
    revert h_back
    decide

lemma is_backward_iterate (k : ℕ) (hk : k < 16) : Is_Backward_85 (A006368_map_inv^[k] 85) = true := by
  interval_cases k <;> decide

lemma map_inv_eq_of_eq_inv {x y : ℕ} (h : A006368_map_inv x = y) : x = A006368_map y := by
  have h_eq := congr_arg A006368_map h
  rw [A006368_map_right_inverse x] at h_eq
  exact h_eq

theorem g_and_not_E (k : ℕ) : A006368_map_inv^[k] 85 ≥ 85 ∧ ¬ E_prime (A006368_map_inv^[k] 85) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 16
    · have h_ge : A006368_map_inv^[k] 85 ≥ 85 := by
        interval_cases k <;> decide
      have h_back : Is_Backward_85 (A006368_map_inv^[k] 85) = true := is_backward_iterate k hk
      have h_not_E := not_E_prime_of_is_backward h_back
      exact ⟨h_ge, h_not_E⟩
    · -- k ≥ 16
      have h_prev : k - 1 < k := by omega
      have h_ge_prev := (ih (k - 1) h_prev).1
      have h_not_E_prev := (ih (k - 1) h_prev).2
      have h_ge_k : A006368_map_inv^[k] 85 ≥ 85 := by
        have h_eq : A006368_map_inv^[k] 85 = A006368_map_inv (A006368_map_inv^[k-1] 85) := by
          have h_sub : k = (k - 1) + 1 := by omega
          rw [h_sub]
          rw [Function.iterate_succ']
          rfl
        rw [h_eq]
        by_cases h_not : A006368_map_inv^[k-1] 85 = 87 ∨ A006368_map_inv^[k-1] 85 = 90 ∨ A006368_map_inv^[k-1] 85 = 93 ∨ A006368_map_inv^[k-1] 85 = 96 ∨ A006368_map_inv^[k-1] 85 = 99 ∨ A006368_map_inv^[k-1] 85 = 102 ∨ A006368_map_inv^[k-1] 85 = 105 ∨ A006368_map_inv^[k-1] 85 = 108 ∨ A006368_map_inv^[k-1] 85 = 111 ∨ A006368_map_inv^[k-1] 85 = 114 ∨ A006368_map_inv^[k-1] 85 = 117 ∨ A006368_map_inv^[k-1] 85 = 120 ∨ A006368_map_inv^[k-1] 85 = 123 ∨ A006368_map_inv^[k-1] 85 = 126
        · rcases h_not with h_eq_87 | h_eq_90 | h_eq_93 | h_eq_96 | h_eq_99 | h_eq_102 | h_eq_105 | h_eq_108 | h_eq_111 | h_eq_114 | h_eq_117 | h_eq_120 | h_eq_123 | h_eq_126
          · -- 87
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_87
              subst h_eq_87
              have h_eq_n1 : A006368_map_inv 87 = 58 := rfl
              have h_E : E_prime (A006368_map_inv 87) := h_eq_n1 ▸ E_prime.lt 58 (by decide) (by decide)
              exact E_prime.step 87 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 90
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_90
              subst h_eq_90
              have h_eq_n1 : A006368_map_inv 90 = 60 := rfl
              have h_E : E_prime (A006368_map_inv 90) := h_eq_n1 ▸ E_prime.lt 60 (by decide) (by decide)
              exact E_prime.step 90 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 93
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_93
              subst h_eq_93
              have h_eq_n1 : A006368_map_inv 93 = 62 := rfl
              have h_E : E_prime (A006368_map_inv 93) := h_eq_n1 ▸ E_prime.lt 62 (by decide) (by decide)
              exact E_prime.step 93 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 96
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_96
              subst h_eq_96
              exact E_prime.base_96
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 99
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_99
              subst h_eq_99
              have h_eq_n1 : A006368_map_inv 99 = 66 := rfl
              have h_E : E_prime (A006368_map_inv 99) := h_eq_n1 ▸ E_prime.lt 66 (by decide) (by decide)
              exact E_prime.step 99 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 102
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_102
              subst h_eq_102
              have h_eq_n1 : A006368_map_inv 102 = 68 := rfl
              have h_E : E_prime (A006368_map_inv 102) := h_eq_n1 ▸ E_prime.lt 68 (by decide) (by decide)
              exact E_prime.step 102 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 105
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_105
              subst h_eq_105
              have h_eq_n1 : A006368_map_inv 105 = 70 := rfl
              have h_E : E_prime (A006368_map_inv 105) := h_eq_n1 ▸ E_prime.lt 70 (by decide) (by decide)
              exact E_prime.step 105 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 108
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_108
              subst h_eq_108
              have h_eq_n1 : A006368_map_inv 108 = 72 := rfl
              have h_E : E_prime (A006368_map_inv 108) := h_eq_n1 ▸ E_prime.lt 72 (by decide) (by decide)
              exact E_prime.step 108 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 111
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_111
              subst h_eq_111
              have h_eq_n1 : A006368_map_inv 111 = 74 := rfl
              have h_E : E_prime (A006368_map_inv 111) := h_eq_n1 ▸ E_prime.lt 74 (by decide) (by decide)
              exact E_prime.step 111 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 114
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_114
              subst h_eq_114
              have h_eq_n1 : A006368_map_inv 114 = 76 := rfl
              have h_E : E_prime (A006368_map_inv 114) := h_eq_n1 ▸ E_prime.lt 76 (by decide) (by decide)
              exact E_prime.step 114 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 117
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_117
              subst h_eq_117
              have h_eq_n1 : A006368_map_inv 117 = 78 := rfl
              have h_E : E_prime (A006368_map_inv 117) := h_eq_n1 ▸ E_prime.lt 78 (by decide) (by decide)
              exact E_prime.step 117 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 120
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_120
              subst h_eq_120
              have h_eq_n1 : A006368_map_inv 120 = 80 := rfl
              have h_E : E_prime (A006368_map_inv 120) := h_eq_n1 ▸ E_prime.lt 80 (by decide) (by decide)
              exact E_prime.step 120 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 123
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_123
              subst h_eq_123
              have h_eq_n1 : A006368_map_inv 123 = 82 := rfl
              have h_E : E_prime (A006368_map_inv 123) := h_eq_n1 ▸ E_prime.lt 82 (by decide) (by decide)
              exact E_prime.step 123 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
          · -- 126
            have h_E_n1 : E_prime (A006368_map_inv^[k - 1] 85) := by
              generalize h_val : A006368_map_inv^[k - 1] 85 = val
              rw [h_val] at h_eq_126
              subst h_eq_126
              have h_eq_n1 : A006368_map_inv 126 = 84 := rfl
              have h_E : E_prime (A006368_map_inv 126) := h_eq_n1 ▸ E_prime.lt 84 (by decide) (by decide)
              exact E_prime.step 126 h_E (by decide)
            exact False.elim (h_not_E_prev h_E_n1)
        · have h_not_conj : A006368_map_inv^[k-1] 85 ≠ 87 ∧ A006368_map_inv^[k-1] 85 ≠ 90 ∧ A006368_map_inv^[k-1] 85 ≠ 93 ∧ A006368_map_inv^[k-1] 85 ≠ 96 ∧ A006368_map_inv^[k-1] 85 ≠ 99 ∧ A006368_map_inv^[k-1] 85 ≠ 102 ∧ A006368_map_inv^[k-1] 85 ≠ 105 ∧ A006368_map_inv^[k-1] 85 ≠ 108 ∧ A006368_map_inv^[k-1] 85 ≠ 111 ∧ A006368_map_inv^[k-1] 85 ≠ 114 ∧ A006368_map_inv^[k-1] 85 ≠ 117 ∧ A006368_map_inv^[k-1] 85 ≠ 120 ∧ A006368_map_inv^[k-1] 85 ≠ 123 ∧ A006368_map_inv^[k-1] 85 ≠ 126 := by
            push_neg at h_not
            exact h_not
          have h_ge_n1 := g_ge_85 (A006368_map_inv^[k-1] 85) h_ge_prev h_not_conj
          exact h_ge_n1

      refine ⟨h_ge_k, ?_⟩
      intro h_E_k
      have h_neq : Is_Backward_85 (A006368_map_inv^[k-1] 85) = false := by
        by_contra hc
        have h_true : Is_Backward_85 (A006368_map_inv^[k-1] 85) = true := by
          cases h_bool : Is_Backward_85 (A006368_map_inv^[k-1] 85)
          · exfalso; exact hc h_bool
          · rfl
        have h_or : A006368_map_inv^[k-1] 85 = 85 ∨ A006368_map_inv^[k-1] 85 = 113 ∨ A006368_map_inv^[k-1] 85 = 151 ∨ A006368_map_inv^[k-1] 85 = 201 ∨ A006368_map_inv^[k-1] 85 = 134 ∨ A006368_map_inv^[k-1] 85 = 179 ∨ A006368_map_inv^[k-1] 85 = 239 ∨ A006368_map_inv^[k-1] 85 = 319 ∨ A006368_map_inv^[k-1] 85 = 425 ∨ A006368_map_inv^[k-1] 85 = 567 ∨ A006368_map_inv^[k-1] 85 = 378 ∨ A006368_map_inv^[k-1] 85 = 252 ∨ A006368_map_inv^[k-1] 85 = 168 ∨ A006368_map_inv^[k-1] 85 = 112 ∨ A006368_map_inv^[k-1] 85 = 149 ∨ A006368_map_inv^[k-1] 85 = 199 := by
          unfold Is_Backward_85 at h_true
          simp only [Bool.or_eq_true, decide_eq_true_iff] at h_true
          omega
        rcases h_or with h_eq_85 | h_eq_113 | h_eq_151 | h_eq_201 | h_eq_134 | h_eq_179 | h_eq_239 | h_eq_319 | h_eq_425 | h_eq_567 | h_eq_378 | h_eq_252 | h_eq_168 | h_eq_112 | h_eq_149 | h_eq_199
        · -- 85
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_85
          rw [Function.iterate_succ'] at h_eq_85
          have h_inv := map_inv_eq_of_eq_inv h_eq_85
          have h_ge_k2 := (ih (k-2) (by omega)).1
          rw [h_inv] at h_ge_k2
          revert h_ge_k2; decide
        · -- 113
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_113
          rw [Function.iterate_succ'] at h_eq_113
          have h_inv := map_inv_eq_of_eq_inv h_eq_113
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_ge_k3 := (ih (k-3) (by omega)).1
          rw [h_inv2] at h_ge_k3
          revert h_ge_k3; decide
        · -- 151
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_151
          rw [Function.iterate_succ'] at h_eq_151
          have h_inv := map_inv_eq_of_eq_inv h_eq_151
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_ge_k4 := (ih (k-4) (by omega)).1
          rw [h_inv3] at h_ge_k4
          revert h_ge_k4; decide
        · -- 201
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_201
          rw [Function.iterate_succ'] at h_eq_201
          have h_inv := map_inv_eq_of_eq_inv h_eq_201
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_ge_k5 := (ih (k-5) (by omega)).1
          rw [h_inv4] at h_ge_k5
          revert h_ge_k5; decide
        · -- 134
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_134
          rw [Function.iterate_succ'] at h_eq_134
          have h_inv := map_inv_eq_of_eq_inv h_eq_134
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_ge_k6 := (ih (k-6) (by omega)).1
          rw [h_inv5] at h_ge_k6
          revert h_ge_k6; decide
        · -- 179
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_179
          rw [Function.iterate_succ'] at h_eq_179
          have h_inv := map_inv_eq_of_eq_inv h_eq_179
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_ge_k7 := (ih (k-7) (by omega)).1
          rw [h_inv6] at h_ge_k7
          revert h_ge_k7; decide
        · -- 239
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_239
          rw [Function.iterate_succ'] at h_eq_239
          have h_inv := map_inv_eq_of_eq_inv h_eq_239
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_ge_k8 := (ih (k-8) (by omega)).1
          rw [h_inv7] at h_ge_k8
          revert h_ge_k8; decide
        · -- 319
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_319
          rw [Function.iterate_succ'] at h_eq_319
          have h_inv := map_inv_eq_of_eq_inv h_eq_319
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_ge_k9 := (ih (k-9) (by omega)).1
          rw [h_inv8] at h_ge_k9
          revert h_ge_k9; decide
        · -- 425
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_425
          rw [Function.iterate_succ'] at h_eq_425
          have h_inv := map_inv_eq_of_eq_inv h_eq_425
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_sub9 : k - 9 = (k - 10) + 1 := by omega
          rw [h_sub9] at h_inv8
          rw [Function.iterate_succ'] at h_inv8
          have h_inv9 := map_inv_eq_of_eq_inv h_inv8
          have h_ge_k10 := (ih (k-10) (by omega)).1
          rw [h_inv9] at h_ge_k10
          revert h_ge_k10; decide
        · -- 567
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_567
          rw [Function.iterate_succ'] at h_eq_567
          have h_inv := map_inv_eq_of_eq_inv h_eq_567
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_sub9 : k - 9 = (k - 10) + 1 := by omega
          rw [h_sub9] at h_inv8
          rw [Function.iterate_succ'] at h_inv8
          have h_inv9 := map_inv_eq_of_eq_inv h_inv8
          have h_sub10 : k - 10 = (k - 11) + 1 := by omega
          rw [h_sub10] at h_inv9
          rw [Function.iterate_succ'] at h_inv9
          have h_inv10 := map_inv_eq_of_eq_inv h_inv9
          have h_ge_k11 := (ih (k-11) (by omega)).1
          rw [h_inv10] at h_ge_k11
          revert h_ge_k11; decide
        · -- 378
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_378
          rw [Function.iterate_succ'] at h_eq_378
          have h_inv := map_inv_eq_of_eq_inv h_eq_378
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_sub9 : k - 9 = (k - 10) + 1 := by omega
          rw [h_sub9] at h_inv8
          rw [Function.iterate_succ'] at h_inv8
          have h_inv9 := map_inv_eq_of_eq_inv h_inv8
          have h_sub10 : k - 10 = (k - 11) + 1 := by omega
          rw [h_sub10] at h_inv9
          rw [Function.iterate_succ'] at h_inv9
          have h_inv10 := map_inv_eq_of_eq_inv h_inv9
          have h_sub11 : k - 11 = (k - 12) + 1 := by omega
          rw [h_sub11] at h_inv10
          rw [Function.iterate_succ'] at h_inv10
          have h_inv11 := map_inv_eq_of_eq_inv h_inv10
          have h_ge_k12 := (ih (k-12) (by omega)).1
          rw [h_inv11] at h_ge_k12
          revert h_ge_k12; decide
        · -- 252
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_252
          rw [Function.iterate_succ'] at h_eq_252
          have h_inv := map_inv_eq_of_eq_inv h_eq_252
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_sub9 : k - 9 = (k - 10) + 1 := by omega
          rw [h_sub9] at h_inv8
          rw [Function.iterate_succ'] at h_inv8
          have h_inv9 := map_inv_eq_of_eq_inv h_inv8
          have h_sub10 : k - 10 = (k - 11) + 1 := by omega
          rw [h_sub10] at h_inv9
          rw [Function.iterate_succ'] at h_inv9
          have h_inv10 := map_inv_eq_of_eq_inv h_inv9
          have h_sub11 : k - 11 = (k - 12) + 1 := by omega
          rw [h_sub11] at h_inv10
          rw [Function.iterate_succ'] at h_inv10
          have h_inv11 := map_inv_eq_of_eq_inv h_inv10
          have h_sub12 : k - 12 = (k - 13) + 1 := by omega
          rw [h_sub12] at h_inv11
          rw [Function.iterate_succ'] at h_inv11
          have h_inv12 := map_inv_eq_of_eq_inv h_inv11
          have h_ge_k13 := (ih (k-13) (by omega)).1
          rw [h_inv12] at h_ge_k13
          revert h_ge_k13; decide
        · -- 168
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_168
          rw [Function.iterate_succ'] at h_eq_168
          have h_inv := map_inv_eq_of_eq_inv h_eq_168
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_sub9 : k - 9 = (k - 10) + 1 := by omega
          rw [h_sub9] at h_inv8
          rw [Function.iterate_succ'] at h_inv8
          have h_inv9 := map_inv_eq_of_eq_inv h_inv8
          have h_sub10 : k - 10 = (k - 11) + 1 := by omega
          rw [h_sub10] at h_inv9
          rw [Function.iterate_succ'] at h_inv9
          have h_inv10 := map_inv_eq_of_eq_inv h_inv9
          have h_sub11 : k - 11 = (k - 12) + 1 := by omega
          rw [h_sub11] at h_inv10
          rw [Function.iterate_succ'] at h_inv10
          have h_inv11 := map_inv_eq_of_eq_inv h_inv10
          have h_sub12 : k - 12 = (k - 13) + 1 := by omega
          rw [h_sub12] at h_inv11
          rw [Function.iterate_succ'] at h_inv11
          have h_inv12 := map_inv_eq_of_eq_inv h_inv11
          have h_sub13 : k - 13 = (k - 14) + 1 := by omega
          rw [h_sub13] at h_inv12
          rw [Function.iterate_succ'] at h_inv12
          have h_inv13 := map_inv_eq_of_eq_inv h_inv12
          have h_ge_k14 := (ih (k-14) (by omega)).1
          rw [h_inv13] at h_ge_k14
          revert h_ge_k14; decide
        · -- 112
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_112
          rw [Function.iterate_succ'] at h_eq_112
          have h_inv := map_inv_eq_of_eq_inv h_eq_112
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_sub9 : k - 9 = (k - 10) + 1 := by omega
          rw [h_sub9] at h_inv8
          rw [Function.iterate_succ'] at h_inv8
          have h_inv9 := map_inv_eq_of_eq_inv h_inv8
          have h_sub10 : k - 10 = (k - 11) + 1 := by omega
          rw [h_sub10] at h_inv9
          rw [Function.iterate_succ'] at h_inv9
          have h_inv10 := map_inv_eq_of_eq_inv h_inv9
          have h_sub11 : k - 11 = (k - 12) + 1 := by omega
          rw [h_sub11] at h_inv10
          rw [Function.iterate_succ'] at h_inv10
          have h_inv11 := map_inv_eq_of_eq_inv h_inv10
          have h_sub12 : k - 12 = (k - 13) + 1 := by omega
          rw [h_sub12] at h_inv11
          rw [Function.iterate_succ'] at h_inv11
          have h_inv12 := map_inv_eq_of_eq_inv h_inv11
          have h_sub13 : k - 13 = (k - 14) + 1 := by omega
          rw [h_sub13] at h_inv12
          rw [Function.iterate_succ'] at h_inv12
          have h_inv13 := map_inv_eq_of_eq_inv h_inv12
          have h_sub14 : k - 14 = (k - 15) + 1 := by omega
          rw [h_sub14] at h_inv13
          rw [Function.iterate_succ'] at h_inv13
          have h_inv14 := map_inv_eq_of_eq_inv h_inv13
          have h_ge_k15 := (ih (k-15) (by omega)).1
          rw [h_inv14] at h_ge_k15
          revert h_ge_k15; decide
        · -- 149
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_149
          rw [Function.iterate_succ'] at h_eq_149
          have h_inv := map_inv_eq_of_eq_inv h_eq_149
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_sub9 : k - 9 = (k - 10) + 1 := by omega
          rw [h_sub9] at h_inv8
          rw [Function.iterate_succ'] at h_inv8
          have h_inv9 := map_inv_eq_of_eq_inv h_inv8
          have h_sub10 : k - 10 = (k - 11) + 1 := by omega
          rw [h_sub10] at h_inv9
          rw [Function.iterate_succ'] at h_inv9
          have h_inv10 := map_inv_eq_of_eq_inv h_inv9
          have h_sub11 : k - 11 = (k - 12) + 1 := by omega
          rw [h_sub11] at h_inv10
          rw [Function.iterate_succ'] at h_inv10
          have h_inv11 := map_inv_eq_of_eq_inv h_inv10
          have h_sub12 : k - 12 = (k - 13) + 1 := by omega
          rw [h_sub12] at h_inv11
          rw [Function.iterate_succ'] at h_inv11
          have h_inv12 := map_inv_eq_of_eq_inv h_inv11
          have h_sub13 : k - 13 = (k - 14) + 1 := by omega
          rw [h_sub13] at h_inv12
          rw [Function.iterate_succ'] at h_inv12
          have h_inv13 := map_inv_eq_of_eq_inv h_inv12
          have h_sub14 : k - 14 = (k - 15) + 1 := by omega
          rw [h_sub14] at h_inv13
          rw [Function.iterate_succ'] at h_inv13
          have h_inv14 := map_inv_eq_of_eq_inv h_inv13
          have h_sub15 : k - 15 = (k - 16) + 1 := by omega
          rw [h_sub15] at h_inv14
          rw [Function.iterate_succ'] at h_inv14
          have h_inv15 := map_inv_eq_of_eq_inv h_inv14
          have h_ge_k16 := (ih (k-16) (by omega)).1
          rw [h_inv15] at h_ge_k16
          revert h_ge_k16; decide
        · -- 199
          have h_sub : k - 1 = (k - 2) + 1 := by omega
          rw [h_sub] at h_eq_199
          rw [Function.iterate_succ'] at h_eq_199
          have h_inv := map_inv_eq_of_eq_inv h_eq_199
          have h_sub2 : k - 2 = (k - 3) + 1 := by omega
          rw [h_sub2] at h_inv
          rw [Function.iterate_succ'] at h_inv
          have h_inv2 := map_inv_eq_of_eq_inv h_inv
          have h_sub3 : k - 3 = (k - 4) + 1 := by omega
          rw [h_sub3] at h_inv2
          rw [Function.iterate_succ'] at h_inv2
          have h_inv3 := map_inv_eq_of_eq_inv h_inv2
          have h_sub4 : k - 4 = (k - 5) + 1 := by omega
          rw [h_sub4] at h_inv3
          rw [Function.iterate_succ'] at h_inv3
          have h_inv4 := map_inv_eq_of_eq_inv h_inv3
          have h_sub5 : k - 5 = (k - 6) + 1 := by omega
          rw [h_sub5] at h_inv4
          rw [Function.iterate_succ'] at h_inv4
          have h_inv5 := map_inv_eq_of_eq_inv h_inv4
          have h_sub6 : k - 6 = (k - 7) + 1 := by omega
          rw [h_sub6] at h_inv5
          rw [Function.iterate_succ'] at h_inv5
          have h_inv6 := map_inv_eq_of_eq_inv h_inv5
          have h_sub7 : k - 7 = (k - 8) + 1 := by omega
          rw [h_sub7] at h_inv6
          rw [Function.iterate_succ'] at h_inv6
          have h_inv7 := map_inv_eq_of_eq_inv h_inv6
          have h_sub8 : k - 8 = (k - 9) + 1 := by omega
          rw [h_sub8] at h_inv7
          rw [Function.iterate_succ'] at h_inv7
          have h_inv8 := map_inv_eq_of_eq_inv h_inv7
          have h_sub9 : k - 9 = (k - 10) + 1 := by omega
          rw [h_sub9] at h_inv8
          rw [Function.iterate_succ'] at h_inv8
          have h_inv9 := map_inv_eq_of_eq_inv h_inv8
          have h_sub10 : k - 10 = (k - 11) + 1 := by omega
          rw [h_sub10] at h_inv9
          rw [Function.iterate_succ'] at h_inv9
          have h_inv10 := map_inv_eq_of_eq_inv h_inv9
          have h_sub11 : k - 11 = (k - 12) + 1 := by omega
          rw [h_sub11] at h_inv10
          rw [Function.iterate_succ'] at h_inv10
          have h_inv11 := map_inv_eq_of_eq_inv h_inv10
          have h_sub12 : k - 12 = (k - 13) + 1 := by omega
          rw [h_sub12] at h_inv11
          rw [Function.iterate_succ'] at h_inv11
          have h_inv12 := map_inv_eq_of_eq_inv h_inv11
          have h_sub13 : k - 13 = (k - 14) + 1 := by omega
          rw [h_sub13] at h_inv12
          rw [Function.iterate_succ'] at h_inv12
          have h_inv13 := map_inv_eq_of_eq_inv h_inv12
          have h_sub14 : k - 14 = (k - 15) + 1 := by omega
          rw [h_sub14] at h_inv13
          rw [Function.iterate_succ'] at h_inv13
          have h_inv14 := map_inv_eq_of_eq_inv h_inv13
          have h_sub15 : k - 15 = (k - 16) + 1 := by omega
          rw [h_sub15] at h_inv14
          rw [Function.iterate_succ'] at h_inv14
          have h_inv15 := map_inv_eq_of_eq_inv h_inv14
          have h_sub16 : k - 16 = (k - 17) + 1 := by omega
          rw [h_sub16] at h_inv15
          rw [Function.iterate_succ'] at h_inv15
          have h_inv16 := map_inv_eq_of_eq_inv h_inv15
          have h_ge_k17 : A006368_map_inv^[k-17] 85 ≥ 85 := by
            by_cases hk17 : k = 16
            · rw [hk17]
              decide
            · have h_prev : k - 17 < k := by omega
              exact (ih (k-17) h_prev).1
          rw [h_inv16] at h_ge_k17
          revert h_ge_k17; decide
      have h_E_prev : E_prime (A006368_map_inv^[k-1] 85) := by
        have h_eq_inv : A006368_map_inv^[k] 85 = A006368_map_inv (A006368_map_inv^[k-1] 85) := by
          have h_sub : k = (k - 1) + 1 := by omega
          rw [h_sub]
          rw [Function.iterate_succ']
          rfl
        have h_E_inv : E_prime (A006368_map_inv (A006368_map_inv^[k-1] 85)) := by
          rw [← h_eq_inv]
          exact h_E_k
        exact E_prime.step (A006368_map_inv^[k-1] 85) h_E_inv h_neq
      exact h_not_E_prev h_E_prev

lemma g_iterate_85_ge_85 (k : ℕ) : A006368_map_inv^[k] 85 ≥ 85 := by
  exact (g_and_not_E k).1

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
