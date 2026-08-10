import FormalConjectures.Util.ProblemImports

open Nat

/--
A340737: Numerators of a sequence of fractions converging to $e$.
$$a(1) = 3, a(2) = 5$$
For $n > 2$:
$$a(n) = \begin{cases} \left(\frac{n+2}{2}\right) a(n-1) - a(n-2) - \left(\frac{n-2}{2}\right) a(n-3) & \text{if } n \text{ is even} \\ 2 a(n-1) + n a(n-2) & \text{if } n \text{ is odd} \end{cases}$$
-/
noncomputable def A340737 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Required for total function, O(1,1) suggests 0 is not relevant.
  | 1 => 3
  | 2 => 5
  | n' + 3 => -- n $\ge$ 3
    let n := n' + 3

    let a_nm1 := A340737 (n - 1)
    let a_nm2 := A340737 (n - 2)
    let a_nm3 := A340737 (n - 3)

    if n % 2 = 0 then
      -- n is even, n $\ge$ 4
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2

      -- $a(n) = c_1 \cdot a(n-1) - a(n-2) - c_2 \cdot a(n-3)$.
      -- We use Int.ofNat for safe subtraction, as the result is known to be positive.
      Int.toNat (Int.ofNat c1 * Int.ofNat a_nm1 - Int.ofNat a_nm2 - Int.ofNat c2 * Int.ofNat a_nm3)
    else
      -- n is odd, n $\ge$ 3
      2 * a_nm1 + n * a_nm2
termination_by n

/--
A340738: Denominators of a sequence of fractions converging to $e$.
This sequence is defined by the same recurrence relation as A340737 but with initial values $b(1)=1, b(2)=2$.
$$b(1) = 1, b(2) = 2$$
For $n > 2$:
$$b(n) = \begin{cases} \left(\frac{n+2}{2}\right) b(n-1) - b(n-2) - \left(\frac{n-2}{2}\right) b(n-3) & \text{if } n \text{ is even} \\ 2 b(n-1) + n b(n-2) & \text{if } n \text{ is odd} \end{cases}$$
-/
noncomputable def A340738 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n' + 3 => -- n $\ge$ 3
    let n := n' + 3

    let b_nm1 := A340738 (n - 1)
    let b_nm2 := A340738 (n - 2)
    let b_nm3 := A340738 (n - 3)

    if n % 2 = 0 then
      -- n is even, n $\ge$ 4
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2

      -- $b(n) = c_1 \cdot b(n-1) - b(n-2) - c_2 \cdot b(n-3)$.
      -- We use Int.ofNat for safe subtraction.
      Int.toNat (Int.ofNat c1 * Int.ofNat b_nm1 - Int.ofNat b_nm2 - Int.ofNat c2 * Int.ofNat b_nm3)
    else
      -- n is odd, n $\ge$ 3
      2 * b_nm1 + n * b_nm2
termination_by n



example (m : ℕ) : A340737 (2*m + 3) = 2 * A340737 (2*m + 2) + (2*m + 3) * A340737 (2*m + 1) := by
  rw [A340737]
  simp only
  have hodd : (2 * m + 3) % 2 ≠ 0 := by omega
  simp


example (m : ℕ) :
    A340737 (2*m + 4) = Int.toNat (Int.ofNat ((2*m + 6)/2) * Int.ofNat (A340737 (2*m+3)) - Int.ofNat (A340737 (2*m+2)) - Int.ofNat ((2*m+2)/2) * Int.ofNat (A340737 (2*m+1))) := by
  rw [A340737]
  have heven : (2 * m + 4) % 2 = 0 := by omega
  simp [heven]
  congr <;> omega



noncomputable def prevA (m : ℕ) : ℕ := if m = 0 then 1 else A340737 (2*m - 1)

lemma A_odd_step (m : ℕ) : A340737 (2*m + 3) = 2 * A340737 (2*m + 2) + (2*m + 3) * A340737 (2*m + 1) := by
  rw [A340737]
  have hodd : (2 * m + 3) % 2 ≠ 0 := by omega
  simp [hodd]

lemma A_even_bridge (m : ℕ) : 2 * A340737 (2*m + 2) = (2*m + 3) * A340737 (2*m + 1) + prevA m := by
  induction m with
  | zero => norm_num [prevA, A340737]
  | succ m ih =>
      have hodd := A_odd_step m
      -- unfold the even term A(2*m+4)
      rw [show 2 * (m+1) + 2 = 2*m + 4 by ring]
      rw [A340737]
      have heven : (2 * m + 4) % 2 = 0 := by omega
      simp [heven, prevA]
      let z : ℤ := (((2 * ↑m + 1 + 3) / 2 + 1) * ↑(A340737 (2 * m + 3)) - ↑(A340737 (2 * m + 2)) -
          (↑m + 1) * ↑(A340737 (2 * m + 1)))
      change 2 * z.toNat = (2 * (m + 1) + 3) * A340737 (2 * (m + 1) + 1) + A340737 (2 * (m + 1) - 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      have hoddI : (A340737 (2 * m + 3) : ℤ) = 2 * (A340737 (2 * m + 2) : ℤ) + (2 * m + 3 : ℕ) * (A340737 (2 * m + 1) : ℤ) := by
        exact_mod_cast hodd
      have hz2 : 2 * z = ((2 * m + 5) * A340737 (2 * m + 3) + A340737 (2 * m + 1) : ℕ) := by
        dsimp [z]
        have hdiv : (2 * (m : ℤ) + 1 + 3) / 2 = (m : ℤ) + 2 := by omega
        rw [hdiv, hoddI]
        norm_num
        ring
      have hznon : 0 ≤ z := by
        have hrhs_non : (0 : ℤ) ≤ ((2 * m + 5) * A340737 (2 * m + 3) + A340737 (2 * m + 1) : ℕ) := by positivity
        nlinarith
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_mul, Int.toNat_of_nonneg hznon]
      exact hz2

example (m : ℕ) : A340737 (2*m + 5) = (4*m + 10) * A340737 (2*m + 3) + A340737 (2*m + 1) := by
  rw [A340737]
  have hodd : (2 * m + 2 + 3) % 2 ≠ 0 := by omega
  simp [hodd]
  rw [A340737]
  have heven : (2 * m + 4) % 2 = 0 := by omega
  simp [heven]
  -- now arithmetic, but `Int.toNat` remains
  trace_state
  sorry
