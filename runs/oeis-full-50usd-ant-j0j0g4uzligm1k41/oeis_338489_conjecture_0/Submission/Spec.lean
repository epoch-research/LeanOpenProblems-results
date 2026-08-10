import FormalConjectures.Util.ProblemImports
open Nat Int

/--
A338489: Let $t$ be the closest triangular number to $n!$ (in case $n=2$, the only case where we have a tie, take the larger $t$); then $a(n) = n! - t$.
-/
def a (n : ℕ) : ℤ :=
  -- T(k) is the k-th triangular number k * (k + 1) / 2
  let T (k : ℕ) : ℕ := k * (k + 1) / 2
  let N_nat := n.factorial

  -- The index $k_0$ such that $T_{k_0} \le N! < T_{k_0+1}$
  -- $k_0 = \lfloor (\sqrt{8 \cdot N! + 1} - 1) / 2 \rfloor$.
  -- We use Nat.sqrt, which computes the floor of the square root.
  let k0_numerator : ℕ := (8 * N_nat + 1).sqrt.pred
  let k0 : ℕ := k0_numerator / 2

  let T_k0_nat := T k0
  let T_k1_nat := T (k0 + 1)

  let N : ℤ := N_nat
  let T_k0 : ℤ := T_k0_nat
  let T_k1 : ℤ := T_k1_nat

  -- Calculate distances. Int.abs is used.
  let d0 := abs (N - T_k0)
  let d1 := abs (N - T_k1)

  -- Determine the closest triangular number t
  let t : ℤ :=
    if d0 < d1 then
      T_k0
    else if d1 < d0 then
      T_k1
    else -- d0 = d1, a tie
      if n = 2 then
        -- Tie-breaker for n=2: take the larger t
        max T_k0 T_k1
      else
        -- For other ties, T_k0 is an arbitrary selection.
        -- However, the sequence definition states n=2 is the *only* case for a tie.
        T_k0

  N - t

/-- A natural number is triangular if it is of the form $k(k+1)/2$ for some natural number $k$. -/
def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

/--
It is conjectured that 0! = 1, 1! = 1, 3! = 6 and 5! = 120 are the only numbers
that are both factorial (A000142) and triangular (A000217) numbers.
This is equivalent to asserting that $n!$ is triangular if and only if $n \in \{0, 1, 3, 5\}$.
-/
theorem oeis_338489_conjecture_0 :
    ∀ n : ℕ, is_triangular n.factorial ↔ n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 5 := by
  intro n
  constructor
  · intro h
    -- Forward direction. The equation `is_triangular (n!)` is equivalent to
    -- `8 * n! + 1` being a perfect square, which is a Brocard–Ramanujan-type
    -- Diophantine problem. The cases `n ≤ 5` are finite checks; the case
    -- `n ≥ 6` is the genuinely open core.
    rcases n with _|_|_|_|_|_|m
    · tauto
    · tauto
    · -- n = 2 : `2` is not triangular.
      exfalso; obtain ⟨k, hk⟩ := h
      rw [show Nat.factorial 2 = 2 from rfl] at hk
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · interval_cases k <;> omega
      · have : 3 ≤ k * (k + 1) / 2 := by
          calc 3 = 2 * (2 + 1) / 2 := by norm_num
            _ ≤ k * (k + 1) / 2 := Nat.div_le_div_right (Nat.mul_le_mul hge (by omega))
        omega
    · tauto
    · -- n = 4 : `24` is not triangular.
      exfalso; obtain ⟨k, hk⟩ := h
      rw [show Nat.factorial 4 = 24 from rfl] at hk
      rcases Nat.lt_or_ge k 7 with hlt | hge
      · interval_cases k <;> omega
      · have : 28 ≤ k * (k + 1) / 2 := by
          calc 28 = 7 * (7 + 1) / 2 := by norm_num
            _ ≤ k * (k + 1) / 2 := Nat.div_le_div_right (Nat.mul_le_mul hge (by omega))
        omega
    · tauto
    · -- n = m + 6 : the open Brocard–Ramanujan-type core. This asserts that
      -- `8 * (m+6)! + 1` is never a perfect square, equivalent in difficulty to
      -- Brocard's problem, for which no unconditional proof is known.
      sorry
  · intro h
    rcases h with h | h | h | h <;> subst h
    · exact ⟨1, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨15, by decide⟩
