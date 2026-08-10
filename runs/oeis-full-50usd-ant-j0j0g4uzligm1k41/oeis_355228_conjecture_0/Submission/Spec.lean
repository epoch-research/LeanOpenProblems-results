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

set_option maxRecDepth 20000 in
/-- No `m < 13` is simultaneously the sum and lcm of `4` of its distinct divisors. -/
private theorem no4 : ∀ m < 13,
    ¬ (0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = 4 ∧ D.sum id = m ∧ D.lcm id = m) := by
  decide

set_option maxRecDepth 20000 in
/-- No `m < 25` is simultaneously the sum and lcm of `5` of its distinct divisors. -/
private theorem no5 : ∀ m < 25,
    ¬ (0 < m ∧ ∃ D ∈ (Nat.divisors m).powerset, D.card = 5 ∧ D.sum id = m ∧ D.lcm id = m) := by
  decide

/-- `n = 4`:  `a 4 = 18 > 12 = a081512 4`. -/
private theorem strict4 : a 4 > a081512 4 := by
  have hle : a081512 4 ≤ 12 := by
    apply Nat.sInf_le
    exact ⟨by norm_num, {1, 2, 3, 6}, by decide, by decide, by decide⟩
  have hne :
      ((fun n => { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
          D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m }) 4).Nonempty :=
    ⟨18, by norm_num, {1, 2, 6, 9}, by decide, by decide, by decide, by decide⟩
  have hlb : ∀ m ∈ ((fun n => { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m }) 4), 13 ≤ m := by
    rintro m ⟨hm, D, hD, hc, hs, hl⟩
    by_contra hcon; push_neg at hcon
    exact no4 m hcon ⟨hm, D, Finset.mem_powerset.mpr hD, hc, hs, hl⟩
  have h13 : (13 : ℕ) ≤ a 4 := hlb _ (Nat.sInf_mem hne)
  omega

/-- `n = 5`:  `a 5 = 28 > 24 = a081512 5`. -/
private theorem strict5 : a 5 > a081512 5 := by
  have hle : a081512 5 ≤ 24 := by
    apply Nat.sInf_le
    exact ⟨by norm_num, {1, 2, 3, 6, 12}, by decide, by decide, by decide⟩
  have hne :
      ((fun n => { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
          D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m }) 5).Nonempty :=
    ⟨28, by norm_num, {1, 2, 4, 7, 14}, by decide, by decide, by decide, by decide⟩
  have hlb : ∀ m ∈ ((fun n => { m : ℕ | 0 < m ∧ ∃ D : Finset ℕ,
      D ⊆ Nat.divisors m ∧ D.card = n ∧ D.sum id = m ∧ D.lcm id = m }) 5), 25 ≤ m := by
    rintro m ⟨hm, D, hD, hc, hs, hl⟩
    by_contra hcon; push_neg at hcon
    exact no5 m hcon ⟨hm, D, Finset.mem_powerset.mpr hD, hc, hs, hl⟩
  have h25 : (25 : ℕ) ≤ a 5 := hlb _ (Nat.sInf_mem hne)
  omega

/--
A355228 a(n) >= A081512(n) because in A081512, it is not required that m = lcm(d_1, d_2, ..., d_n).
Currently, the strict inequality happens for n = 4 and n = 5; are there other such cases?

This conjecture states that the set of natural numbers $n$ for which the strict inequality $a(n) > a_081512(n)$ holds is exactly $\{4, 5\}$.
-/
theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  constructor
  · -- Forward direction: the genuinely open part of the OEIS conjecture.
    -- It asserts `a n = a081512 n` for every `n ∉ {4, 5}`; there is no closed form for these
    -- sequences and no uniform argument is currently known.
    intro h
    sorry
  · rintro (rfl | rfl)
    · exact strict4
    · exact strict5

