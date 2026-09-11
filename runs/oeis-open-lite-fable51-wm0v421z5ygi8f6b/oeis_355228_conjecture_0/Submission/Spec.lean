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


/-! ### Partial results (verified small cases)

The two `sInf`-definitions can be evaluated for a specific `n` by exhibiting a witness
`M` together with a proof that no `m < M` is a candidate; the latter is decidable
(finite search over `Finset.powersetCard`). -/

lemma a081512_eq_of (n M : ℕ) (hM : 0 < M)
    (hmem : ∃ D ∈ (Nat.divisors M).powersetCard n, D.sum id = M)
    (hlt : ∀ m < M, ¬ ∃ D ∈ (Nat.divisors m).powersetCard n, D.sum id = m) :
    a081512 n = M := by
  unfold a081512
  apply le_antisymm
  · apply Nat.sInf_le
    obtain ⟨D, hD, hs⟩ := hmem
    rw [Finset.mem_powersetCard] at hD
    exact ⟨hM, D, hD.1, hD.2, hs⟩
  · apply le_csInf
    · obtain ⟨D, hD, hs⟩ := hmem
      rw [Finset.mem_powersetCard] at hD
      exact ⟨M, hM, D, hD.1, hD.2, hs⟩
    · rintro m ⟨_, D, hD, hc, hs⟩
      by_contra h
      push_neg at h
      exact hlt m h ⟨D, Finset.mem_powersetCard.mpr ⟨hD, hc⟩, hs⟩

lemma a_eq_of (n M : ℕ) (hM : 0 < M)
    (hmem : ∃ D ∈ (Nat.divisors M).powersetCard n, D.sum id = M ∧ D.lcm id = M)
    (hlt : ∀ m < M, ¬ ∃ D ∈ (Nat.divisors m).powersetCard n, D.sum id = m ∧ D.lcm id = m) :
    a n = M := by
  unfold a
  apply le_antisymm
  · apply Nat.sInf_le
    obtain ⟨D, hD, hs⟩ := hmem
    rw [Finset.mem_powersetCard] at hD
    exact ⟨hM, D, hD.1, hD.2, hs.1, hs.2⟩
  · apply le_csInf
    · obtain ⟨D, hD, hs⟩ := hmem
      rw [Finset.mem_powersetCard] at hD
      exact ⟨M, hM, D, hD.1, hD.2, hs.1, hs.2⟩
    · rintro m ⟨_, D, hD, hc, hs, hl⟩
      by_contra h
      push_neg at h
      exact hlt m h ⟨D, Finset.mem_powersetCard.mpr ⟨hD, hc⟩, hs, hl⟩

lemma a081512_four : a081512 4 = 12 := a081512_eq_of 4 12 (by norm_num) (by decide) (by decide)
lemma a_four : a 4 = 18 := a_eq_of 4 18 (by norm_num) (by decide) (by decide)
lemma a081512_five : a081512 5 = 24 := a081512_eq_of 5 24 (by norm_num) (by decide) (by decide)
lemma a_five : a 5 = 28 := a_eq_of 5 28 (by norm_num) (by decide) (by decide)
lemma a081512_six : a081512 6 = 24 := a081512_eq_of 6 24 (by norm_num) (by decide) (by decide)
lemma a_six : a 6 = 24 := a_eq_of 6 24 (by norm_num) (by decide) (by decide)

/-- The strict inequality does hold for `n = 4`. -/
lemma strict_four : a 4 > a081512 4 := by rw [a_four, a081512_four]; norm_num

/-- The strict inequality does hold for `n = 5`. -/
lemma strict_five : a 5 > a081512 5 := by rw [a_five, a081512_five]; norm_num

/-- ... and fails for `n = 6`. -/
lemma not_strict_six : ¬ (a 6 > a081512 6) := by rw [a_six, a081512_six]; norm_num

/--
A355228 a(n) >= A081512(n) because in A081512, it is not required that m = lcm(d_1, d_2, ..., d_n).
Currently, the strict inequality happens for n = 4 and n = 5; are there other such cases?

This conjecture states that the set of natural numbers $n$ for which the strict inequality $a(n) > a_081512(n)$ holds is exactly $\{4, 5\}$.
-/
theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  sorry

theorem oeis_355228_conjecture_0.disproof : ¬ (type_of% @oeis_355228_conjecture_0) := sorry
