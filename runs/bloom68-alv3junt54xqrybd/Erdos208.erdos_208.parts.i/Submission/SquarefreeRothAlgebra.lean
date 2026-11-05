import FormalConjecturesUtil

/-! Exact algebra for the large-square-divisor determinant argument. -/
namespace SquarefreeRothAlgebra

lemma witness_q_decreases_real
    (N H x y q₁ q₂ : ℝ)
    (hH : 0 ≤ H) (hx : H < x) (hgap : x + 1 ≤ y)
    (hq₁ : 1 ≤ q₁)
    (hn₁ : N < q₁ * x ^ 2) (hn₂ : q₂ * y ^ 2 ≤ N + H) :
    q₂ < q₁ := by
  have hx0 : 0 < x := lt_of_le_of_lt hH hx
  have hy0 : 0 < y := by linarith
  have hsum : 0 < y + x := by linarith
  have hsep0 : 0 ≤ (y - x - 1) * (y + x) :=
    mul_nonneg (by linarith) hsum.le
  have hsep : H < y ^ 2 - x ^ 2 := by nlinarith
  by_contra h
  have hq : 0 ≤ q₂ - q₁ := by linarith
  have hprod₁ : 0 ≤ (q₂ - q₁) * y ^ 2 := mul_nonneg hq (sq_nonneg y)
  have hprod₂ : 0 ≤ (q₁ - 1) * (y ^ 2 - x ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma strict_determinant_core
    (N H x y z q₁ q₂ q₃ : ℝ)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hyH : H < y) (hs : 1 ≤ z - y) (hu : 1 ≤ q₁ - q₂)
    (hn₁ : N < q₁ * x ^ 2) (hn₂ : q₂ * y ^ 2 ≤ N + H)
    (hn₃ : N < q₃ * z ^ 2) :
    0 < (z - y) * q₁ - (z - x) * q₂ + (y - x) * q₃ := by
  let D := (z - y) * q₁ - (z - x) * q₂ + (y - x) * q₃
  let S := x * y + x * z + y * z
  let L := (z - y) * (y + z) * (q₂ * y ^ 2 - q₁ * x ^ 2) -
    (y - x) * (x + y) * (q₃ * z ^ 2 - q₂ * y ^ 2)
  have hy : 0 < y := hx.trans hxy
  have hz : 0 < z := hy.trans hyz
  have ht : 0 < z - x := sub_pos.mpr (hxy.trans hyz)
  have hA : 0 < (z - y) * (y + z) := mul_pos (sub_pos.mpr hyz) (by linarith)
  have hB : 0 < (y - x) * (x + y) := mul_pos (sub_pos.mpr hxy) (by linarith)
  have hdel₁ : q₂ * y ^ 2 - q₁ * x ^ 2 < H := by linarith
  have hdel₂ : q₂ * y ^ 2 - q₃ * z ^ 2 < H := by linarith
  have hbound₁ := mul_lt_mul_of_pos_left hdel₁ hA
  have hbound₂ := mul_lt_mul_of_pos_left hdel₂ hB
  have hcoeff : (z - y) * (y + z) + (y - x) * (x + y) =
      (z - x) * (x + z) := by ring
  have hL : L < H * (z - x) * (x + z) := by
    calc
      L = (z - y) * (y + z) * (q₂ * y ^ 2 - q₁ * x ^ 2) +
          (y - x) * (x + y) * (q₂ * y ^ 2 - q₃ * z ^ 2) := by dsimp [L]; ring
      _ < H * ((z - y) * (y + z) + (y - x) * (x + y)) := by linarith
      _ = H * (z - x) * (x + z) := by rw [hcoeff]; ring
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hcurv : H * (x + z) < S := by
    have h := mul_pos (sub_pos.mpr hyH) (show 0 < x + z by linarith)
    have h' := mul_pos hx hz
    dsimp [S]
    nlinarith
  have hus : 1 ≤ (q₁ - q₂) * (z - y) := by
    have := mul_nonneg (show 0 ≤ q₁ - q₂ - 1 by linarith)
      (show 0 ≤ z - y - 1 by linarith)
    nlinarith
  by_contra hD
  have hD' : D ≤ 0 := by dsimp [D]; linarith
  have herror : 0 ≤ (-D) * (x + y) * z ^ 2 := by
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg z)
  have hidentity : L = (q₁ - q₂) * (z - y) * (z - x) * S -
      D * (x + y) * z ^ 2 := by dsimp [L, D, S]; ring
  have hlow : (z - x) * S ≤ L := by
    have hmul := mul_le_mul_of_nonneg_right hus (mul_nonneg ht.le hS.le)
    rw [hidentity]
    nlinarith
  have hhigh : H * (z - x) * (x + z) < (z - x) * S := by
    have := mul_lt_mul_of_pos_left hcurv ht
    nlinarith
  linarith

/-- All ordered triples of integer large-square witnesses are strictly convex. -/
theorem witness_determinant_positive
    (N H x y z q₁ q₂ q₃ : ℕ)
    (hH : 0 < H) (hx : H < x) (hxy : x < y) (hyz : y < z)
    (hq₁ : 0 < q₁) (_hq₂ : 0 < q₂) (_hq₃ : 0 < q₃)
    (hn₁ : N < q₁ * x ^ 2) (_hn₁' : q₁ * x ^ 2 ≤ N + H)
    (hn₂ : N < q₂ * y ^ 2) (hn₂' : q₂ * y ^ 2 ≤ N + H)
    (hn₃ : N < q₃ * z ^ 2) (_hn₃' : q₃ * z ^ 2 ≤ N + H) :
    0 < ((z : ℤ) - y) * q₁ - ((z : ℤ) - x) * q₂ + ((y : ℤ) - x) * q₃ := by
  have hqr : (q₂ : ℝ) < q₁ := witness_q_decreases_real N H x y q₁ q₂
    (by positivity) (by exact_mod_cast hx)
    (by exact_mod_cast (show x + 1 ≤ y by omega))
    (by exact_mod_cast hq₁) (by exact_mod_cast hn₁) (by exact_mod_cast hn₂')
  have hqn : q₂ < q₁ := by exact_mod_cast hqr
  have hu : (1 : ℝ) ≤ (q₁ : ℝ) - q₂ := by
    have h : (q₂ : ℝ) + 1 ≤ q₁ := by exact_mod_cast (show q₂ + 1 ≤ q₁ by omega)
    linarith
  have hs : (1 : ℝ) ≤ (z : ℝ) - y := by
    have h : (y : ℝ) + 1 ≤ z := by exact_mod_cast (show y + 1 ≤ z by omega)
    linarith
  have h := strict_determinant_core N H x y z q₁ q₂ q₃
    (by exact_mod_cast (show 0 < x by omega)) (by exact_mod_cast hxy)
    (by exact_mod_cast hyz) (by exact_mod_cast (show H < y by omega)) hs hu
    (by exact_mod_cast hn₁) (by exact_mod_cast hn₂') (by exact_mod_cast hn₃)
  exact_mod_cast h

lemma inverse_square_crossproduct (x y z : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (z - y) / x ^ 2 - (z - x) / y ^ 2 + (y - x) / z ^ 2 =
      (y - x) * (z - y) * (z - x) * (x * y + x * z + y * z) /
        (x ^ 2 * y ^ 2 * z ^ 2) := by
  field_simp
  ring

lemma cubic_chord_identity (x y z a b : ℚ) :
    (z - x) * ((a - b * y) * y ^ 2) -
      (z - y) * ((a - b * x) * x ^ 2) -
      (y - x) * ((a - b * z) * z ^ 2) =
    (y - x) * (z - y) * (z - x) * (b * (x + z) - (a - b * y)) := by ring

#print axioms witness_determinant_positive
#print axioms inverse_square_crossproduct
#print axioms cubic_chord_identity
lemma witness_basic_bounds (N H d q : ℕ)
    (hH : 0 < H) (hd : H < d) (hq : 0 < q)
    (hn : q * d ^ 2 ≤ N + H) :
    H ^ 2 < N ∧ d < N ∧ 3 * H ≤ N := by
  have hq1 : 1 ≤ q := by omega
  have hdH : H + 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hdsq : (H + 1) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hdH 2
  have hdsq' : d ^ 2 ≤ q * d ^ 2 := by nlinarith
  constructor
  · nlinarith
  constructor
  · have hpow : 0 ≤ (d : ℤ) * (d - 2) :=
      mul_nonneg (by positivity) (by
        have : (2 : ℤ) ≤ d := by exact_mod_cast hd2
        omega)
    have hnreal : (q : ℤ) * (d : ℤ) ^ 2 ≤ N + H := by exact_mod_cast hn
    have hsqreal : (d : ℤ) ^ 2 ≤ (q : ℤ) * (d : ℤ) ^ 2 := by exact_mod_cast hdsq'
    have hdreal : (H : ℤ) < d := by exact_mod_cast hd
    have : (d : ℤ) < N := by nlinarith
    exact_mod_cast this
  · have hH1 : 1 ≤ H := by omega
    have hmul : H ≤ H ^ 2 := by nlinarith
    nlinarith

lemma rational_window_error_condition (N H P K : ℕ)
    (hH : 0 < H) (hP : H ≤ P) (hN : 64 * H < N)
    (hmain : N ≤ P * K ^ 3) :
    4 * H < P * K := by
  have hPpos : 0 < P := lt_of_lt_of_le hH hP
  by_contra h
  have hsmall : P * K ≤ 4 * H := by omega
  have hcube : (P * K) ^ 3 ≤ (4 * H) ^ 3 := Nat.pow_le_pow_left hsmall 3
  have hsq : H ^ 2 ≤ P ^ 2 := Nat.pow_le_pow_left hP 2
  have hchain : N * P ^ 2 ≤ (P * K) ^ 3 := by
    calc
      N * P ^ 2 ≤ (P * K ^ 3) * P ^ 2 := Nat.mul_le_mul_right _ hmain
      _ = (P * K) ^ 3 := by ring
  have hmid : (4 * H) ^ 3 ≤ 64 * H * P ^ 2 := by
    have h := Nat.mul_le_mul_left (64 * H) hsq
    nlinarith
  have hlast : 64 * H * P ^ 2 < N * P ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hN (pow_pos hPpos _)
  omega

lemma survivor_contradiction (H S : ℝ) (hH : 0 < H)
    (hlo : H / 12 ≤ S) (hhi : S ≤ 20 * (H / 256)) : False := by
  linarith

#print axioms witness_basic_bounds
#print axioms rational_window_error_condition
#print axioms survivor_contradiction
end SquarefreeRothAlgebra
