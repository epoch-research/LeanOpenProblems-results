import Mathlib

open Nat

/-- The triangular number `T(x) = x(x+1)/2`. -/
def triangular (x : ℕ) : ℕ := x * (x + 1) / 2

/-- `8·T(x) + 1 = (2x+1)²`. -/
lemma eight_tri_add_one (x : ℕ) : 8 * triangular x + 1 = (2 * x + 1) ^ 2 := by
  unfold triangular
  have h2 : 2 ∣ x * (x + 1) := even_mul_succ_self x
  have : x * (x + 1) / 2 * 2 = x * (x + 1) := Nat.div_mul_cancel h2
  nlinarith [this]

/-- Basic division/modulo decomposition summed over three numbers. -/
lemma div_add_div_add_div_of_sum {m a b c n t : ℕ} (hm : 0 < m)
    (hsum : a + b + c = m * (n + t))
    (hmod : a % m + b % m + c % m = t * m) :
    a / m + b / m + c / m = n := by
  have da : a = m * (a / m) + a % m := (Nat.div_add_mod a m).symm ▸ by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod a m).symm
  have db : b = m * (b / m) + b % m := by rw [Nat.mul_comm]; exact (Nat.div_add_mod b m).symm
  have dc : c = m * (c / m) + c % m := by rw [Nat.mul_comm]; exact (Nat.div_add_mod c m).symm
  -- a+b+c = m*(a/m+b/m+c/m) + (a%m+b%m+c%m)
  have key : m * (n + t) = m * (a / m + b / m + c / m) + t * m := by
    calc m * (n + t) = a + b + c := hsum.symm
      _ = (m * (a / m) + a % m) + (m * (b / m) + b % m) + (m * (c / m) + c % m) := by
            rw [da, db, dc]
      _ = m * (a / m + b / m + c / m) + (a % m + b % m + c % m) := by ring
      _ = m * (a / m + b / m + c / m) + t * m := by rw [hmod]
  have : m * (n + t) = m * (a / m + b / m + c / m + t) := by rw [key]; ring
  have h2 : n + t = a / m + b / m + c / m + t := Nat.eq_of_mul_eq_mul_left hm this
  omega

/-- **The reduction.** The conjecture follows from the (congruence-constrained) three-square
statement `H`. Here `a, b, c` play the role of the `x, y, z`; the hypothesis says
`(2a+1)² + (2b+1)² + (2c+1)² = 8m(n+t)+3` (three odd squares) with the residue-sum equal to
`t·m` for some `t ∈ {0,1,2}`. -/
theorem reduction
    (H : ∀ (m : ℕ), 0 < m → ∀ (n : ℕ), ∃ a b c t : ℕ, t ≤ 2 ∧
        (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 + (2 * c + 1) ^ 2 = 8 * m * (n + t) + 3 ∧
        triangular a % m + triangular b % m + triangular c % m = t * m)
    (m : ℕ) (hm : m > 0) (n : ℕ) :
    ∃ x y z : ℕ, n = triangular x / m + triangular y / m + triangular z / m := by
  obtain ⟨a, b, c, t, _ht, hsq, hmod⟩ := H m hm n
  refine ⟨a, b, c, ?_⟩
  -- Convert the sum of odd squares to a sum of triangular numbers.
  have ea := eight_tri_add_one a
  have eb := eight_tri_add_one b
  have ec := eight_tri_add_one c
  -- 8*(T a + T b + T c) + 3 = 8*m*(n+t)+3
  have hT : triangular a + triangular b + triangular c = m * (n + t) := by
    have : 8 * (triangular a + triangular b + triangular c) + 3 = 8 * (m * (n + t)) + 3 := by
      have expand : (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 + (2 * c + 1) ^ 2
          = 8 * (triangular a + triangular b + triangular c) + 3 := by
        rw [← ea, ← eb, ← ec]; ring
      rw [expand] at hsq
      rw [hsq]; ring
    omega
  have := div_add_div_add_div_of_sum hm hT hmod
  omega
