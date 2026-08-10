import FormalConjectures.Util.ProblemImports

open Finset Nat Set

set_option maxRecDepth 10000

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

/-- Helper: compute a sInf when we have a member that is also a lower bound. -/
theorem sInf_eq_of {S : Set ℕ} {k : ℕ} (hmem : k ∈ S) (hlb : ∀ m ∈ S, k ≤ m) :
    sInf S = k :=
  le_antisymm (Nat.sInf_le hmem) (hlb _ (Nat.sInf_mem ⟨k, hmem⟩))

theorem a081512_4 : a081512 4 = 12 := by
  apply sInf_eq_of (k := 12)
  · exact ⟨by norm_num, {1,2,3,6}, by decide, by decide, by decide⟩
  · rintro m ⟨hm, hex⟩; by_contra h; push_neg at h; interval_cases m <;> revert hex <;> decide

theorem a081512_5 : a081512 5 = 24 := by
  apply sInf_eq_of (k := 24)
  · exact ⟨by norm_num, {1,2,3,6,12}, by decide, by decide, by decide⟩
  · rintro m ⟨hm, hex⟩; by_contra h; push_neg at h; interval_cases m <;> revert hex <;> decide

theorem a_4 : a 4 = 18 := by
  apply sInf_eq_of (k := 18)
  · exact ⟨by norm_num, {1,2,6,9}, by decide, by decide, by decide, by decide⟩
  · rintro m ⟨hm, hex⟩; by_contra h; push_neg at h; interval_cases m <;> revert hex <;> decide

theorem a_5 : a 5 = 28 := by
  apply sInf_eq_of (k := 28)
  · exact ⟨by norm_num, {1,2,4,7,14}, by decide, by decide, by decide, by decide⟩
  · rintro m ⟨hm, hex⟩; by_contra h; push_neg at h; interval_cases m <;> revert hex <;> decide

/-- No two distinct divisors of `m` sum to `m`. -/
theorem no_two_sum (m : ℕ) (D : Finset ℕ) (hD : D ⊆ Nat.divisors m)
    (hcard : D.card = 2) (hsum : D.sum id = m) : False := by
  rw [Finset.card_eq_two] at hcard
  obtain ⟨d1, d2, hne, rfl⟩ := hcard
  rw [Finset.sum_pair hne] at hsum
  simp only [id] at hsum
  have h1 : d1 ∈ Nat.divisors m := hD (by simp)
  have h2 : d2 ∈ Nat.divisors m := hD (by simp)
  rw [Nat.mem_divisors] at h1 h2
  obtain ⟨hd1, _⟩ := h1
  obtain ⟨hd2, _⟩ := h2
  have e1 : d1 ∣ d1 + d2 := hsum ▸ hd1
  have e2 : d2 ∣ d1 + d2 := hsum ▸ hd2
  have hd1d2 : d1 ∣ d2 := (Nat.dvd_add_right (dvd_refl d1)).mp e1
  have hd2d1 : d2 ∣ d1 := (Nat.dvd_add_left (dvd_refl d2)).mp e2
  exact hne (Nat.dvd_antisymm hd1d2 hd2d1)

theorem a_2 : a 2 = 0 := by
  rw [a, Nat.sInf_eq_zero]; right
  rw [Set.eq_empty_iff_forall_notMem]
  rintro m ⟨hm, D, hD, hcard, hsum, _⟩
  exact no_two_sum m D hD hcard hsum

theorem a081512_2 : a081512 2 = 0 := by
  rw [a081512, Nat.sInf_eq_zero]; right
  rw [Set.eq_empty_iff_forall_notMem]
  rintro m ⟨hm, D, hD, hcard, hsum⟩
  exact no_two_sum m D hD hcard hsum

theorem a_0 : a 0 = 0 := by
  rw [a, Nat.sInf_eq_zero]; right
  rw [Set.eq_empty_iff_forall_notMem]
  rintro m ⟨hm, D, _, hcard, hsum, _⟩
  rw [Finset.card_eq_zero] at hcard; subst hcard
  simp only [Finset.sum_empty] at hsum; omega

theorem a081512_0 : a081512 0 = 0 := by
  rw [a081512, Nat.sInf_eq_zero]; right
  rw [Set.eq_empty_iff_forall_notMem]
  rintro m ⟨hm, D, _, hcard, hsum⟩
  rw [Finset.card_eq_zero] at hcard; subst hcard
  simp only [Finset.sum_empty] at hsum; omega

theorem a_1 : a 1 = 1 := by
  apply sInf_eq_of (k := 1)
  · exact ⟨by norm_num, {1}, by decide, by decide, by decide, by decide⟩
  · rintro m ⟨hm, _⟩; omega

theorem a081512_1 : a081512 1 = 1 := by
  apply sInf_eq_of (k := 1)
  · exact ⟨by norm_num, {1}, by decide, by decide, by decide⟩
  · rintro m ⟨hm, _⟩; omega

theorem a_3 : a 3 = 6 := by
  apply sInf_eq_of (k := 6)
  · exact ⟨by norm_num, {1,2,3}, by decide, by decide, by decide, by decide⟩
  · rintro m ⟨hm, hex⟩; by_contra h; push_neg at h; interval_cases m <;> revert hex <;> decide

theorem a081512_3 : a081512 3 = 6 := by
  apply sInf_eq_of (k := 6)
  · exact ⟨by norm_num, {1,2,3}, by decide, by decide, by decide⟩
  · rintro m ⟨hm, hex⟩; by_contra h; push_neg at h; interval_cases m <;> revert hex <;> decide

/-- **Open part** (OEIS A355228 conjecture, `n ≥ 6` direction):
the smallest integer that is a sum of `n` distinct divisors of itself is, for `n ≥ 6`,
also expressible as such a sum whose lcm equals the integer. -/
theorem a_le_a081512_ge6 (n : ℕ) (hn : 6 ≤ n) : a n ≤ a081512 n := sorry

/--
A355228 a(n) >= A081512(n) because in A081512, it is not required that m = lcm(d_1, d_2, ..., d_n).
Currently, the strict inequality happens for n = 4 and n = 5; are there other such cases?

This conjecture states that the set of natural numbers $n$ for which the strict inequality $a(n) > a_081512(n)$ holds is exactly $\{4, 5\}$.
-/
theorem oeis_355228_conjecture_0 (n : ℕ) :
  (a n > a081512 n) ↔ (n = 4 ∨ n = 5) := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨h4, h5⟩ := hcon
    have hle : a n ≤ a081512 n := by
      rcases lt_or_ge n 6 with hlt | hge
      · interval_cases n
        · exact le_of_eq (by rw [a_0, a081512_0])
        · exact le_of_eq (by rw [a_1, a081512_1])
        · exact le_of_eq (by rw [a_2, a081512_2])
        · exact le_of_eq (by rw [a_3, a081512_3])
        · exact absurd rfl h4
        · exact absurd rfl h5
      · exact a_le_a081512_ge6 n hge
    omega
  · rintro (rfl | rfl)
    · rw [a_4, a081512_4]; norm_num
    · rw [a_5, a081512_5]; norm_num

