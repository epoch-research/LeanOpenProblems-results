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
    -- LHS: weighted_sum_helper (idx+1) (x :: xs) = (idx+1) * x + weighted_sum_helper (idx+2) xs
    -- RHS: weighted_sum_helper idx (x :: xs) + (x :: xs).sum = idx * x + weighted_sum_helper (idx+1) xs + x + xs.sum
    dsimp [weighted_sum_helper, List.sum]
    rw [ih (idx + 1)]
    omega

-- Now we can prove the main theorem for ofDigits
theorem ofDigits_cong (L : List ℕ) :
    ofDigits 10 L ≡ L.sum + 9 * weighted_sum L [MOD 81] := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    -- ofDigits 10 (x :: xs) = x + 10 * ofDigits 10 xs
    dsimp [ofDigits, List.sum, weighted_sum]
    -- by ih: ofDigits 10 xs ≡ xs.sum + 9 * weighted_sum xs [MOD 81]
    -- LHS = x + 10 * ofDigits 10 xs
    have h_mul : x + 10 * ofDigits 10 xs ≡ x + 10 * (xs.sum + 9 * weighted_sum_helper 0 xs) [MOD 81] := by
      -- we can use ModEq.add and ModEq.mul
      -- Since ih is: ofDigits 10 xs ≡ xs.sum + 9 * weighted_sum xs [MOD 81]
      -- we multiply ih by 10 and add x
      have h1 := ModEq.mul_left 10 ih
      have h2 := ModEq.add_left x h1
      exact h2
    -- Now we just need to show that:
    -- x + 10 * (xs.sum + 9 * weighted_sum_helper 0 xs) ≡ (x + xs.sum) + 9 * weighted_sum_helper 0 (x :: xs) [MOD 81]
    -- Let's unfold weighted_sum_helper on the RHS:
    -- weighted_sum_helper 0 (x :: xs) = 0 * x + weighted_sum_helper 1 xs = weighted_sum_helper 1 xs
    -- And weighted_sum_helper 1 xs = weighted_sum_helper 0 xs + xs.sum
    have h_rhs : weighted_sum_helper 0 (x :: xs) = weighted_sum_helper 0 xs + xs.sum := by
      dsimp [weighted_sum_helper]
      exact weighted_sum_helper_shift 0 xs
    rw [h_rhs]
    -- Now we want:
    -- x + 10 * (xs.sum + 9 * W) ≡ x + xs.sum + 9 * (W + xs.sum) [MOD 81]
    -- LHS = x + 10 * xs.sum + 90 * W
    -- RHS = x + xs.sum + 9 * W + 9 * xs.sum = x + 10 * xs.sum + 9 * W
    -- Since 90 * W ≡ 9 * W [MOD 81] because 90*W - 9*W = 81*W
    have h_eq : x + 10 * (xs.sum + 9 * weighted_sum_helper 0 xs) ≡ x + xs.sum + 9 * (weighted_sum_helper 0 xs + xs.sum) [MOD 81] := by
      unfold ModEq
      omega
    exact h_mul.trans h_eq
