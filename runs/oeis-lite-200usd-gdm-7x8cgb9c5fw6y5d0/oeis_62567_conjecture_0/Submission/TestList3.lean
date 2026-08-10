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
  | nil => rfl
  | cons y ys ih =>
    simp [weighted_sum_helper]
    rw [ih (idx + 1)]
    have h_add : idx + 1 + ys.length = idx + (1 + ys.length) := by omega
    rw [h_add]
    rfl

theorem weighted_sum_add (L1 L2 : List ℕ) :
    weighted_sum (L1 ++ L2) = weighted_sum L1 + weighted_sum L2 + L1.length * L2.sum := by
  unfold weighted_sum
  rw [weighted_sum_helper_add 0 L1 L2]
  -- Now we have: weighted_sum_helper 0 L1 + weighted_sum_helper L1.length L2
  -- We want to prove: weighted_sum_helper L1.length L2 = weighted_sum L2 + L1.length * L2.sum
  -- Let's prove: weighted_sum_helper idx L = weighted_sum L + idx * L.sum by induction on idx using shift
  have h_shift : ∀ idx, weighted_sum_helper idx L2 = weighted_sum L2 + idx * L2.sum := by
    intro idx
    induction idx with
    | zero => simp [weighted_sum]
    | succ idx ih =>
      rw [weighted_sum_helper_shift idx L2]
      rw [ih]
      ring
  rw [h_shift L1.length]
  ring

theorem weighted_sum_reverse (L : List ℕ) :
    weighted_sum L.reverse + weighted_sum L = (L.length - 1) * L.sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    -- L = x :: xs
    -- L.reverse = xs.reverse ++ [x]
    simp [List.reverse_cons]
    rw [weighted_sum_add xs.reverse [x]]
    simp [weighted_sum, weighted_sum_helper, List.sum_cons]
    -- by ih: weighted_sum xs.reverse + weighted_sum xs = (xs.length - 1) * xs.sum
    -- We want: weighted_sum xs.reverse + (0 + 0 + xs.length * x) + (0 * x + weighted_sum_helper 1 xs) = (xs.length + 1 - 1) * (x + xs.sum)
    -- Since xs.length - 1 is Nat tsub, let's cases on xs.length
    cases h_len : xs.length with
    | zero =>
      -- xs.length = 0, so xs = []
      have h_xs : xs = [] := by
        cases xs
        · rfl
        · contradiction
      subst h_xs
      rfl
    | succ n =>
      -- xs.length = n + 1
      -- Then xs.length - 1 = n
      -- xs.length + 1 - 1 = n + 1
      -- We can rewrite ih
      have h_sub : xs.length - 1 = n := by omega
      have ih' : weighted_sum xs.reverse + weighted_sum xs = n * xs.sum := by
        rw [h_sub] at ih
        exact ih
      -- Let's rewrite weighted_sum_helper 1 xs = weighted_sum xs + xs.sum
      have h_shift1 : weighted_sum_helper 1 xs = weighted_sum xs + xs.sum := by
        exact weighted_sum_helper_shift 0 xs
      rw [h_shift1]
      -- Now we have: weighted_sum xs.reverse + (xs.length * x) + (weighted_sum xs + xs.sum)
      -- Let's rearrange using ih':
      -- (weighted_sum xs.reverse + weighted_sum xs) + xs.length * x + xs.sum
      -- = n * xs.sum + xs.length * x + xs.sum
      -- Since xs.length = n + 1:
      -- = n * xs.sum + (n + 1) * x + xs.sum
      -- = (n + 1) * xs.sum + (n + 1) * x
      -- = (n + 1) * (x + xs.sum)
      have h_rearr : weighted_sum xs.reverse + (xs.length * x) + (weighted_sum xs + xs.sum) = (weighted_sum xs.reverse + weighted_sum xs) + xs.length * x + xs.sum := by ring
      rw [h_rearr, ih']
      have h_xs_len : xs.length = n + 1 := h_len
      rw [h_xs_len]
      ring
