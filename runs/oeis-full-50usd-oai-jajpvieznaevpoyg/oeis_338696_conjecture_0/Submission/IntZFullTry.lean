import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

noncomputable def A338696 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun x =>
    let x_cube := x ^ 3
    (range (n + 1)).sum fun y =>
      let y_sq := y ^ 2
      if x_cube + y_sq ≤ n then
        let k := n - (x_cube + y_sq)
        let m := 3 * k + 1
        if m.sqrt * m.sqrt = m then 1 else 0
      else 0

-- import helpers by copying minimal declarations? skip, just test convert goals in examples
example {n x y t : ℕ}
    (h : x ^ 3 + y ^ 2 + (((Int.ofNat t) * (3 * (Int.ofNat t) + 2)).toNat) = n) :
    x ^ 3 + y ^ 2 + t * (3*t+2) = n := by
  convert h using 2
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg]
  · norm_num
  · show (0 : ℤ) ≤ (t : ℤ) * (3 * (t : ℤ) + 2)
    nlinarith [show (0 : ℤ) ≤ t by exact_mod_cast Nat.zero_le t]

example {n x y t : ℕ}
    (h : x ^ 3 + y ^ 2 + (((Int.negSucc t) * (3 * (Int.negSucc t) + 2)).toNat) = n) :
    x ^ 3 + y ^ 2 + (t+1) * (3*(t+1)-2) = n := by
  convert h using 2
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg]
  · have h2 : 2 ≤ 3 * (t + 1) := by nlinarith
    rw [Int.negSucc_eq]
    norm_num [Nat.cast_sub h2]
    ring
  · rw [Int.negSucc_eq]
    show (0 : ℤ) ≤ (-(↑t + 1)) * (3 * (-(↑t + 1)) + 2)
    nlinarith [show (0 : ℤ) ≤ t by exact_mod_cast Nat.zero_le t]
