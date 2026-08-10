import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A084046: Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such number exists.
I.e., smallest prime of the form $k^n - n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- S_n is the set of primes p such that p + n is an n-th power, i.e., p = k^n - n.
  let S_n : Set ℕ := { p | Nat.Prime p ∧ ∃ k : ℕ, k ^ n = p + n }
  -- sInf S_n returns the smallest element of S_n. For Nat, sInf ∅ = 0, fitting the problem statement.
  sInf S_n

/-- The conjecture is FALSE.  Counterexample: `k = 27`.
We have `a 27 = 0` because for every `j`,
`j^27 - 27 = (j^9)^3 - 3^3 = (j^9 - 3) * (j^18 + 3 j^9 + 9)`,
and for `j ≥ 2` both factors exceed `1`, so `j^27 - 27` is never prime.
But `27` is not an even square. -/
theorem a084046_conjecture_0.disproof :
  ¬ (∀ k : ℕ, a k = 0 → ∃ m : ℕ, k = (2 * m) ^ 2) := by
  intro h
  -- Step 1: show `a 27 = 0`.
  have h27 : a 27 = 0 := by
    show sInf {p | Nat.Prime p ∧ ∃ k : ℕ, k ^ 27 = p + 27} = 0
    rw [Nat.sInf_eq_zero]
    right
    rw [Set.eq_empty_iff_forall_notMem]
    rintro p ⟨hp, k, hk⟩
    -- `k ≥ 2`
    have hk2 : 2 ≤ k := by
      by_contra hc
      have hk1 : k ≤ 1 := by omega
      have hle : k ^ 27 ≤ 1 := by
        calc k ^ 27 ≤ 1 ^ 27 := Nat.pow_le_pow_left hk1 27
          _ = 1 := by norm_num
      omega
    -- `k^9 ≥ 512`
    have ha9 : 512 ≤ k ^ 9 := by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ k ^ 9 := Nat.pow_le_pow_left hk2 9
    set b := k ^ 9 - 3 with hb
    have hbk : k ^ 9 = b + 3 := by omega
    have hb509 : 509 ≤ b := by omega
    set F := (b + 3) ^ 2 + 3 * (b + 3) + 9 with hF
    have hFge : 9 ≤ F := by rw [hF]; exact Nat.le_add_left 9 _
    have hcube : k ^ 27 = (k ^ 9) ^ 3 := by ring
    have e1 : (b + 3) ^ 3 = p + 27 := by rw [← hbk, ← hcube]; exact hk
    have key : (b + 3) ^ 3 = b * F + 27 := by rw [hF]; ring
    have hpF : p = b * F := by
      have := e1.symm.trans key
      omega
    rw [hpF] at hp
    rw [Nat.prime_mul_iff] at hp
    rcases hp with ⟨-, hF1⟩ | ⟨-, hb1⟩
    · omega
    · omega
  -- Step 2: derive the contradiction from the conjecture applied to `27`.
  obtain ⟨m, hm⟩ := h 27 h27
  have h4 : (4 : ℕ) ∣ 27 := ⟨m ^ 2, by rw [hm]; ring⟩
  exact absurd h4 (by decide)
