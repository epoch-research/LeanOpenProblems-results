import FormalConjectures.Util.ProblemImports

open Nat

def A006368_map_inv (m : ℕ) : ℕ :=
  if m % 3 = 0 then
    2 * (m / 3)
  else if m % 3 = 1 then
    4 * (m / 3) + 1
  else
    4 * (m / 3) + 3

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

def Is_Backward_85 (x : ℕ) : Bool :=
  x = 85 || x = 113 || x = 151 || x = 201 || x = 134 || x = 179 || x = 239 || x = 319 || x = 425 || x = 567 || x = 378 || x = 252 || x = 168 || x = 112 || x = 149

inductive E_prime : ℕ → Type where
  | lt (x : ℕ) (h1 : x < 85) (h2 : x ≠ 64) : E_prime x
  | step (x : ℕ) (h : E_prime (A006368_map_inv x)) (h_neq : Is_Backward_85 x = false) : E_prime x
  | base_96 : E_prime 96

def E_prime.size : {x : ℕ} → E_prime x → ℕ
  | _, lt .. => 1
  | _, step _ h _ => 1 + h.size
  | _, base_96 => 1

theorem not_E_prime_trajectory (z : ℕ) (hz : E_prime z) : ∀ k, (∀ m, k ≤ m → m ≤ k + hz.size → A006368_map_inv^[m+7] 85 ≥ 85) → A006368_map_inv^[k+7] 85 = z → False := by
  induction hz with
  | lt x h1 h2 =>
    intro k h_ge h_eq
    have h_ge_k := h_ge k (by omega) (by dsimp [E_prime.size] at h_ge; omega)
    rw [h_eq] at h_ge_k
    omega
  | step x h_next h_neq ih =>
    intro k h_ge h_eq
    have h_ge_next : ∀ m, k + 1 ≤ m → m ≤ k + 1 + h_next.size → A006368_map_inv^[m+7] 85 ≥ 85 := by
      intro m hm_le hm_ge
      apply h_ge m
      · omega
      · have h_sz : (E_prime.step x h_next h_neq).size = 1 + h_next.size := rfl
        omega
    have h_eq_next : A006368_map_inv^[k+8] 85 = A006368_map_inv x := by
      have h_step : A006368_map_inv^[k+8] 85 = A006368_map_inv (A006368_map_inv^[k+7] 85) := by
        rw [Function.iterate_succ']
        rfl
      rw [h_step, h_eq]
    exact ih (k + 1) h_ge_next h_eq_next
  | base_96 =>
    intro k h_ge h_eq
    have h_ge_next := h_ge (k + 1) (by omega) (by dsimp [E_prime.size] at h_ge; omega)
    have h_eq_next : A006368_map_inv^[k+8] 85 = A006368_map_inv 96 := by
      have h_step : A006368_map_inv^[k+8] 85 = A006368_map_inv (A006368_map_inv^[k+7] 85) := by
        rw [Function.iterate_succ']
        rfl
      rw [h_step, h_eq]
    have h_inv_96 : A006368_map_inv 96 = 64 := rfl
    rw [h_inv_96] at h_eq_next
    rw [h_eq_next] at h_ge_next
    omega
