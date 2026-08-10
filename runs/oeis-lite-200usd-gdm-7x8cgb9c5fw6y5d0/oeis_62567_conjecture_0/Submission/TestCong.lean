import FormalConjectures.Util.ProblemImports

open Nat

theorem ten_pow_cong (i : ℕ) : 10^i ≡ 1 + 9 * i [MOD 81] := by
  induction i with
  | zero =>
    rfl
  | succ i ih =>
    -- 10^(i+1) = 10^i * 10
    rw [pow_succ]
    -- We want to show (10^i * 10) ≡ 1 + 9 * (i + 1) [MOD 81]
    -- Since ih : 10^i ≡ 1 + 9 * i [MOD 81], we can multiply both sides by 10
    have h_mul : 10^i * 10 ≡ (1 + 9 * i) * 10 [MOD 81] := by
      exact ModEq.mul_right 10 ih
    -- Now we just need to show (1 + 9 * i) * 10 ≡ 1 + 9 * (i + 1) [MOD 81]
    have h_trans : (1 + 9 * i) * 10 ≡ 1 + 9 * (i + 1) [MOD 81] := by
      -- (1 + 9*i) * 10 = 10 + 90*i
      -- 1 + 9*(i+1) = 1 + 9*i + 9 = 10 + 9*i
      -- Since 90*i ≡ 9*i [MOD 81] (because 90*i - 9*i = 81*i)
      -- Let's prove this by omega or ring or simple modeq
      unfold ModEq
      omega
    exact ih.mul_right 10 |>.trans h_trans
