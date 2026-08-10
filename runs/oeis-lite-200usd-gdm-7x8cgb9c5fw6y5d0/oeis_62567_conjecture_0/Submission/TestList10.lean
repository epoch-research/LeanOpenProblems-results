import FormalConjectures.Util.ProblemImports

open Nat

def weighted_sum_helper (idx : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => idx * x + weighted_sum_helper (idx + 1) xs

def weighted_sum (L : List ℕ) : ℕ :=
  weighted_sum_helper 0 L

theorem weighted_sum_helper_shift (idx : ℕ) (L : List ℕ) :
    weighted_sum_helper (idx + 1) L = weighted_sum_helper idx L + L.sum := by
  induction L generalizing idx with
  | nil => rfl
  | cons x xs ih =>
    simp [weighted_sum_helper, List.sum_cons]
    rw [ih (idx + 1)]
    have h_dist : (idx + 1) * x = idx * x + x := by ring
    rw [h_dist]
    omega

theorem weighted_sum_helper_add (idx : ℕ) (L1 L2 : List ℕ) :
    weighted_sum_helper idx (L1 ++ L2) = weighted_sum_helper idx L1 + weighted_sum_helper (idx + L1.length) L2 := by
  induction L1 generalizing idx with
  | nil => simp [weighted_sum_helper]
  | cons y ys ih =>
    simp [weighted_sum_helper]
    rw [ih (idx + 1)]
    have h_add : idx + 1 + ys.length = idx + (ys.length + 1) := by omega
    rw [h_add]
    ring

theorem weighted_sum_add (L1 L2 : List ℕ) :
    weighted_sum (L1 ++ L2) = weighted_sum L1 + weighted_sum L2 + L1.length * L2.sum := by
  unfold weighted_sum
  rw [weighted_sum_helper_add 0 L1 L2]
  have h_shift : ∀ idx, weighted_sum_helper idx L2 = weighted_sum_helper 0 L2 + idx * L2.sum := by
    intro idx
    induction idx with
    | zero => simp
    | succ idx ih =>
      rw [weighted_sum_helper_shift idx L2]
      rw [ih]
      ring
  have h_add : 0 + L1.length = L1.length := by omega
  rw [h_add, h_shift L1.length]
  ring

theorem weighted_sum_reverse (L : List ℕ) :
    weighted_sum L.reverse + weighted_sum L = (L.length - 1) * L.sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse_cons]
    rw [weighted_sum_add xs.reverse [x]]
    simp only [weighted_sum] at *
    simp [weighted_sum_helper, List.sum_cons]
    cases h_len : xs.length with
    | zero =>
      have h_xs : xs = [] := by
        cases xs
        · rfl
        · contradiction
      subst h_xs
      simp [weighted_sum_helper]
    | succ n =>
      have h_sub : xs.length - 1 = n := by omega
      have ih' : weighted_sum_helper 0 xs.reverse + weighted_sum_helper 0 xs = n * xs.sum := by
        rw [h_sub] at ih
        exact ih
      have h_shift1 : weighted_sum_helper 1 xs = weighted_sum_helper 0 xs + xs.sum := by
        exact weighted_sum_helper_shift 0 xs
      have h_group : weighted_sum_helper 0 xs.reverse + (n + 1) * x + weighted_sum_helper 1 xs = (weighted_sum_helper 0 xs.reverse + weighted_sum_helper 0 xs) + (n + 1) * x + xs.sum := by
        rw [h_shift1]
        ring
      rw [h_group, ih']
      ring
