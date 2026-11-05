import Submission.SquarefreeRoth

/-! Rational reverse-dyadic cell targets for the four-point count. -/
namespace SquarefreeTwoNinths

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma target_scaling (t : ℚ) (d r : ℕ) :
    (4*t^2*(9/10 : ℚ)^d)^r * (2 : ℚ)^d =
      4^r*t^(2*r)*((2 : ℚ)*(9/10 : ℚ)^r)^d := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  rw [show d*r = r*d by exact Nat.mul_comm d r, pow_mul]
  rw [mul_pow]
  ring

lemma four_dyadic_target (N H P t d : ℕ)
    (ht : 0 < t) (hP : 0 < P) (hH : H ≤ t^3) (hN : N ≤ t^9)
    (hscale : 2^d*P ≤ t^3) :
    4^6*N*P ≤ ⌈4*(t : ℚ)^2*(9/10 : ℚ)^d⌉₊^6 ∧
      4^3*H*P ≤ ⌈4*(t : ℚ)^2*(9/10 : ℚ)^d⌉₊^3 ∧
      (⌈4*(t : ℚ)^2*(9/10 : ℚ)^d⌉₊ : ℚ) ≤
        2*(4*(t : ℚ)^2*(9/10 : ℚ)^d) := by
  let a := 4*(t : ℚ)^2*(9/10 : ℚ)^d
  let K := ⌈a⌉₊
  have ha : 0 < a := by dsimp [a]; positivity
  have hpow : (0 : ℚ) < (2 : ℚ)^d := by positivity
  have hs : (2 : ℚ)^d*(P : ℚ) ≤ (t : ℚ)^3 := by exact_mod_cast hscale
  have hNq : (N : ℚ) ≤ (t : ℚ)^9 := by exact_mod_cast hN
  have hHq : (H : ℚ) ≤ (t : ℚ)^3 := by exact_mod_cast hH
  have hsix : 4^6*(N : ℚ)*P ≤ a^6 := by
    apply (mul_le_mul_iff_left₀ hpow).mp
    calc
      4^6*(N : ℚ)*P*(2 : ℚ)^d = 4^6*(N : ℚ)*((2 : ℚ)^d*P) := by ring
      _ ≤ 4^6*(t : ℚ)^9*(t : ℚ)^3 := by gcongr
      _ = 4^6*(t : ℚ)^12 := by ring
      _ ≤ 4^6*(t : ℚ)^12*((2 : ℚ)*(9/10 : ℚ)^6)^d := by
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
      _ = a^6*(2 : ℚ)^d := by dsimp [a]; rw [target_scaling]
  have hthree : 4^3*(H : ℚ)*P ≤ a^3 := by
    apply (mul_le_mul_iff_left₀ hpow).mp
    calc
      4^3*(H : ℚ)*P*(2 : ℚ)^d = 4^3*(H : ℚ)*((2 : ℚ)^d*P) := by ring
      _ ≤ 4^3*(t : ℚ)^3*(t : ℚ)^3 := by gcongr
      _ = 4^3*(t : ℚ)^6 := by ring
      _ ≤ 4^3*(t : ℚ)^6*((2 : ℚ)*(9/10 : ℚ)^3)^d := by
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
      _ = a^3*(2 : ℚ)^d := by dsimp [a]; rw [target_scaling]
  have ha1 : 1 ≤ a := by
    have ht1 : (1 : ℚ) ≤ t := by exact_mod_cast ht
    have hp1 : (1 : ℚ) ≤ P := by exact_mod_cast hP
    have hlow : (1 : ℚ) ≤ 4^6*(t : ℚ)^9*P := by
      have ht9 : (1 : ℚ) ≤ (t : ℚ)^9 := one_le_pow₀ ht1
      nlinarith
    have htsix : 4^6*(t : ℚ)^9*P ≤ a^6 := by
      apply (mul_le_mul_iff_left₀ hpow).mp
      calc
        4^6*(t : ℚ)^9*P*(2 : ℚ)^d = 4^6*(t : ℚ)^9*((2 : ℚ)^d*P) := by ring
        _ ≤ 4^6*(t : ℚ)^9*(t : ℚ)^3 := by gcongr
        _ = 4^6*(t : ℚ)^12 := by ring
        _ ≤ 4^6*(t : ℚ)^12*((2 : ℚ)*(9/10 : ℚ)^6)^d := by
          exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
        _ = a^6*(2 : ℚ)^d := by dsimp [a]; rw [target_scaling]
    exact (pow_le_pow_iff_left₀ (by norm_num : (0 : ℚ) ≤ 1) ha.le (by decide : (6 : ℕ) ≠ 0)).mp
      (by simpa using hlow.trans htsix)
  have hc : a ≤ (K : ℚ) := Nat.le_ceil a
  have hc' : (K : ℚ) < a+1 := Nat.ceil_lt_add_one ha.le
  refine ⟨?_, ?_, ?_⟩
  · change 4^6*N*P ≤ K^6
    have h := hsix.trans (pow_le_pow_left₀ ha.le hc 6)
    exact_mod_cast h
  · change 4^3*H*P ≤ K^3
    have h := hthree.trans (pow_le_pow_left₀ ha.le hc 3)
    exact_mod_cast h
  · change (K : ℚ) ≤ 2*a
    linarith

lemma geometric_sum_le_ten (L : ℕ) :
    (∑ k ∈ Finset.range L, (9/10 : ℚ)^k) ≤ 10 := by
  have hid : (∑ k ∈ Finset.range L, (9/10 : ℚ)^k) = 10*(1-(9/10 : ℚ)^L) := by
    induction L with
    | zero => norm_num
    | succ L ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [hid]
  have hp : (0 : ℚ) ≤ (9/10 : ℚ)^L := by positivity
  linarith

end SquarefreeTwoNinths
