import FormalConjectures.Util.ProblemImports

open Finset Nat Set

/--
A355228: $a(n)$ is the smallest integer $m$ such that there exist $n$ of its distinct divisors $(d_1, d_2, \dots, d_n)$ with the property that $m = d_1 + d_2 + \dots + d_n = \operatorname{lcm}(d_1, d_2, \dots, d_n)$, or 0 if no such number $m$ exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidates $m$ for the given $n$.
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      -- There exists a set D of n distinct elements
      ∃ D : Finset ℕ,
        -- D must be a subset of m's positive divisors.
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        -- The sum of elements in D must equal m.
        D.sum id = m ∧
        -- The LCM of elements in D must equal m.
        D.lcm id = m }

  -- sInf of a set of natural numbers returns the minimum element.
  -- Nat.sInf of the empty set is 0, correctly handling the non-existence case a(2)=0.
  sInf candidates

-- A081512: Smallest number $m$ such that $m$ is the sum of $n$ distinct divisors $d_1, \dots, d_n$ of $m$.
noncomputable def a081512 (n : ℕ) : ℕ :=
  let candidates : Set ℕ :=
    { m : ℕ | 0 < m ∧
      ∃ D : Finset ℕ,
        D ⊆ Nat.divisors m ∧
        D.card = n ∧
        D.sum id = m }
  sInf candidates

set_option maxRecDepth 100000

/--
A355228 a(n) >= A081512(n) because in A081512, it is not required that m = lcm(d_1, d_2, ..., d_n).
Currently, the strict inequality happens for n = 4 and n = 5; are there other such cases?

This conjecture states that the set of natural numbers $n$ for which the strict inequality $a(n) > a_081512(n)$ holds is exactly $\{4, 5\}$.
-/
theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  constructor
  · -- Forward direction: `a n > a081512 n → n = 4 ∨ n = 5`.
    --
    -- Equivalently (contrapositive), for every `n ∉ {4,5}` the least number that is a sum of
    -- `n` distinct divisors also admits such a representation whose lcm equals it.
    -- The cases `n ≤ 3` are finite/decidable, but the case `n ≥ 6` is exactly the OEIS
    -- open question "are there other such cases?".  As of writing it is UNRESOLVED: the
    -- quantity `a081512 n` (OEIS A081512) has no known closed form, and the claim depends on
    -- the detailed arithmetic of each minimal witness (there is provably no uniform/local
    -- argument — e.g. structures like `M = 56, n = 6` satisfy every local hypothesis of the
    -- natural minimality reduction yet fail lcm-representability, and are excluded only by the
    -- global value `a081512 6 = 24`).  Verified true for all `n ≤ 84`.
    sorry
  · -- Backward direction: `n = 4 ∨ n = 5 → a n > a081512 n`.  This IS provable.
    rintro (rfl | rfl)
    · -- n = 4:  a081512 4 ≤ 12  <  13 ≤ a 4.
      have hub : a081512 4 ≤ 12 := by
        apply Nat.sInf_le
        refine ⟨by norm_num, {1, 2, 3, 6}, ?_, ?_, ?_⟩ <;> decide
      have hmem : (a 4) ∈ { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
          D ⊆ Nat.divisors m ∧ D.card = 4 ∧ D.sum id = m ∧ D.lcm id = m } := by
        apply Nat.sInf_mem
        exact ⟨18, by norm_num, {1, 2, 6, 9}, by decide, by decide, by decide, by decide⟩
      have hdec : ∀ m ≤ 12, ¬ ∃ D ∈ (Nat.divisors m).powerset,
          D.card = 4 ∧ D.sum id = m ∧ D.lcm id = m := by decide
      have hlb : 13 ≤ a 4 := by
        by_contra h
        push_neg at h
        obtain ⟨_, D, hD, hc, hs, hl⟩ := hmem
        exact hdec (a 4) (by omega) ⟨D, Finset.mem_powerset.mpr hD, hc, hs, hl⟩
      omega
    · -- n = 5:  a081512 5 ≤ 24  <  25 ≤ a 5.
      have hub : a081512 5 ≤ 24 := by
        apply Nat.sInf_le
        refine ⟨by norm_num, {1, 2, 3, 6, 12}, ?_, ?_, ?_⟩ <;> decide
      have hmem : (a 5) ∈ { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
          D ⊆ Nat.divisors m ∧ D.card = 5 ∧ D.sum id = m ∧ D.lcm id = m } := by
        apply Nat.sInf_mem
        exact ⟨28, by norm_num, {1, 2, 4, 7, 14}, by decide, by decide, by decide, by decide⟩
      have hdec : ∀ m ≤ 24, ¬ ∃ D ∈ (Nat.divisors m).powerset,
          D.card = 5 ∧ D.sum id = m ∧ D.lcm id = m := by decide
      have hlb : 25 ≤ a 5 := by
        by_contra h
        push_neg at h
        obtain ⟨_, D, hD, hc, hs, hl⟩ := hmem
        exact hdec (a 5) (by omega) ⟨D, Finset.mem_powerset.mpr hD, hc, hs, hl⟩
      omega
