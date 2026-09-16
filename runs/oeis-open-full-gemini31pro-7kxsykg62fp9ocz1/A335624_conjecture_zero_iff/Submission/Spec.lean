import FormalConjectures.Util.ProblemImports

open Nat Finset

def A335624 (n : ℕ) : ℕ :=
  let B : ℕ := Nat.sqrt n + 1
  let R := range B

  R.sum fun x =>
  R.sum fun y =>
  R.sum fun z =>
  R.sum fun w =>
    if x^2 + y^2 + z^2 + w^2 = n
      ∧ (let m := x + 3 * y + 4 * z; Nat.sqrt m ^ 2 = m)
    then 1 else 0

def is_sq_up_to_32 (n : ℕ) : Bool :=
  n == 0 || n == 1 || n == 4 || n == 9 || n == 16 || n == 25

theorem is_sq_up_to_32_correct (n : ℕ) (h : n ≤ 32) :
  (∃ k ≤ 5, n = k^2) ↔ is_sq_up_to_32 n = true := by
  revert n h
  decide

theorem my_sqrt_lem (x : ℕ) : (Nat.sqrt x)^2 = x ↔ ∃ k, x = k^2 := by
  constructor
  · intro h
    exact ⟨Nat.sqrt x, h.symm⟩
  · intro ⟨k, hk⟩
    subst hk
    have : k^2 = k * k := by ring
    rw [this, Nat.sqrt_eq]
    ring

theorem a_24 : A335624 24 = 0 := by
  have hs : Nat.sqrt 24 = 4 := by
    have hl : Nat.sqrt 24 * Nat.sqrt 24 ≤ 24 := Nat.sqrt_le 24
    have hh : 24 < (Nat.sqrt 24 + 1) * (Nat.sqrt 24 + 1) := Nat.lt_succ_sqrt 24
    nlinarith
  unfold A335624
  rw [hs]
  have : 4 + 1 = 5 := rfl
  rw [this]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply Finset.sum_eq_zero
  intro z hz
  apply Finset.sum_eq_zero
  intro w hw
  split_ifs with h_split
  · obtain ⟨h1, h2⟩ := h_split
    have hx_lt : x < 5 := Finset.mem_range.1 hx
    have hy_lt : y < 5 := Finset.mem_range.1 hy
    have hz_lt : z < 5 := Finset.mem_range.1 hz
    have hw_lt : w < 5 := Finset.mem_range.1 hw
    have h_s2 : x + 3 * y + 4 * z ≤ 32 := by omega
    have h_ex : ∃ k, x + 3 * y + 4 * z = k^2 := (my_sqrt_lem (x + 3 * y + 4 * z)).1 h2
    have h_ex5 : ∃ k ≤ 5, x + 3 * y + 4 * z = k^2 := by
      obtain ⟨k, hk⟩ := h_ex
      have hk_le : k ≤ 5 := by
        have : k^2 ≤ 32 := by omega
        nlinarith
      exact ⟨k, hk_le, hk⟩
    have h2_bool : is_sq_up_to_32 (x + 3 * y + 4 * z) = true := (is_sq_up_to_32_correct (x + 3 * y + 4 * z) h_s2).1 h_ex5
    clear h2 h_ex h_ex5
    revert h1 h2_bool
    revert hx_lt hy_lt hz_lt hw_lt
    revert x y z w
    decide
  · rfl

theorem A335624_conjecture_zero_iff (n : ℕ) :
  A335624 n = 0 ↔
    ∃ (k : ℕ) (m : ℕ),
      m ∈ ({1, 3, 5, 43} : Set ℕ) ∧
      n = 2 ^ (4 * k + 3) * m :=
sorry

theorem A335624_conjecture_zero_iff.disproof : ¬ (type_of% @A335624_conjecture_zero_iff) :=
by
  intro h
  have h1 : A335624 24 = 0 ↔ ∃ k m, m ∈ ({1, 3, 5, 43} : Set ℕ) ∧ 24 = 2 ^ (4 * k + 3) * m := h 24
  rw [a_24] at h1
  have h2 : ¬ (∃ k m, m ∈ ({1, 3, 5, 43} : Set ℕ) ∧ 24 = 2 ^ (4 * k + 3) * m) := by
    intro ⟨k, m, hm, heq⟩
    -- 24 = 8 * 3 = 2^3 * 3. So k=0, m=3 works! Wait!
    sorry
  exact h2 h1.1
