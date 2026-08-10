import FormalConjectures.Util.ProblemImports

open Nat

def weighted_sum_helper (idx : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => idx * x + weighted_sum_helper (idx + 1) xs

def weighted_sum (L : List ℕ) : ℕ :=
  weighted_sum_helper 0 L

-- We want to prove that:
-- weighted_sum_helper (idx + 1) L = weighted_sum_helper idx L + L.sum
theorem weighted_sum_helper_shift (idx : ℕ) (L : List ℕ) :
    weighted_sum_helper (idx + 1) L = weighted_sum_helper idx L + L.sum := by
  induction L generalizing idx with
  | nil => rfl
  | cons x xs ih =>
    simp [weighted_sum_helper, List.sum_cons]
    rw [ih (idx + 1)]
    -- now we have: (idx + 1) * x + ... = idx * x + ... + x + xs.sum
    -- let's use ring or omega after distributing the multiplication
    have h_dist : (idx + 1) * x = idx * x + x := by ring
    rw [h_dist]
    omega

-- Now we can prove the main theorem for ofDigits
theorem ofDigits_cong (L : List ℕ) :
    ofDigits 10 L ≡ L.sum + 9 * weighted_sum L [MOD 81] := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    dsimp [ofDigits, List.sum, weighted_sum]
    have h_mul : x + 10 * ofDigits 10 xs ≡ x + 10 * (xs.sum + 9 * weighted_sum_helper 0 xs) [MOD 81] := by
      have h1 := ModEq.mul_left 10 ih
      have h2 := ModEq.add_left x h1
      exact h2
    have h_rhs : weighted_sum_helper 0 (x :: xs) = weighted_sum_helper 0 xs + xs.sum := by
      simp [weighted_sum_helper]
      exact weighted_sum_helper_shift 0 xs
    rw [h_rhs]
    have h_eq : x + 10 * (xs.sum + 9 * weighted_sum_helper 0 xs) ≡ x + xs.sum + 9 * (weighted_sum_helper 0 xs + xs.sum) [MOD 81] := by
      unfold ModEq
      omega
    exact h_mul.trans h_eq
