code = """import FormalConjectures.Util.ProblemImports

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

lemma map_ge_85_is_bad (x : ℕ) (hx : x < 85) (hy : A006368_map x ≥ 85) :
  A006368_map x = 87 ∨ A006368_map x = 90 ∨ A006368_map x = 93 ∨ A006368_map x = 96 ∨ A006368_map x = 99 ∨ A006368_map x = 102 ∨ A006368_map x = 105 ∨ A006368_map x = 108 ∨ A006368_map x = 111 ∨ A006368_map x = 114 ∨ A006368_map x = 117 ∨ A006368_map x = 120 ∨ A006368_map x = 123 ∨ A006368_map x = 126 := by
  revert hx hy
  decide

lemma bad_map_lt_85 {y : ℕ} (hy : y = 87 ∨ y = 90 ∨ y = 93 ∨ y = 96 ∨ y = 99 ∨ y = 102 ∨ y = 105 ∨ y = 108 ∨ y = 111 ∨ y = 114 ∨ y = 117 ∨ y = 120 ∨ y = 123 ∨ y = 126) :
  A006368_map y < 85 := by
  rcases hy with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem map_iterate_not_85 (n : ℕ) : ∀ x < 85, A006368_map^[n] x ≠ 85 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx h_eq
    cases n with
    | zero =>
      simp only [Function.iterate_zero, id_eq] at h_eq
      omega
    | succ n_prime =>
      by_cases hn : n_prime = 0
      · subst hn
        simp only [Function.iterate_one] at h_eq
        have h_eq_inv := congr_arg A006368_map_inv h_eq
        rw [A006368_map_left_inverse x] at h_eq_inv
        have h_inv : A006368_map_inv 85 = 113 := rfl
        rw [h_inv] at h_eq_inv
        omega
      · have hn_gt : n_prime > 0 := by omega
        by_cases hy : A006368_map x < 85
        · have h_eq2 : A006368_map^[n_prime] (A006368_map x) = 85 := by
            rw [← Function.iterate_succ'] at h_eq
            exact h_eq
          exact ih n_prime (by omega) (A006368_map x) hy h_eq2
        · push_neg at hy
          have h_bad := map_ge_85_is_bad x hx hy
          have h_lt_85 := bad_map_lt_85 h_bad
          have h_eq2 : A006368_map^[n_prime - 1] (A006368_map^[2] x) = 85 := by
            have h_eq3 : A006368_map^[n_prime + 1] x = 85 := h_eq
            have h_eq4 : n_prime + 1 = n_prime - 1 + 2 := by omega
            rw [h_eq4] at h_eq3
            rw [Function.iterate_add_apply] at h_eq3
            exact h_eq3
          have h_lt : n_prime - 1 < n_prime + 1 := by omega
          exact ih (n_prime - 1) h_lt (A006368_map^[2] x) h_lt_85 h_eq2

lemma g_iterate_85_ge_85 (k : ℕ) : A006368_map_inv^[k] 85 ≥ 85 := by
  by_contra h_lt
  push_neg at h_lt
  have h_eq : A006368_map^[k] (A006368_map_inv^[k] 85) = 85 := f_g_iterate k 85
  have h_not_85 := map_iterate_not_85 k (A006368_map_inv^[k] 85) h_lt
  exact h_not_85 h_eq

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
    f.write(code)

print("ELEGANT WRITER COMPLETED!")
