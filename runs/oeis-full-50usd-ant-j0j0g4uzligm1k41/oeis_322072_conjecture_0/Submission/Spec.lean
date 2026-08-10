import FormalConjectures.Util.ProblemImports

open BigOperators

/--
The sequence A322072: Row sums of the triangle A322071.
$$a(n) = \sum_{k=1}^n \left\lfloor \frac{2n^k}{k^k} \right\rfloor$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 n) fun k : ℕ =>
    let num : ℕ := 2 * n ^ k
    let den : ℕ := k ^ k
    let term_q : ℚ := (num : ℚ) / (den : ℚ)
    (Rat.floor term_q).toNat

/-- Computable copy of `a` (definitionally equal), enabling `native_decide` evaluation. -/
def a' (n : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 n) fun k : ℕ =>
    let num : ℕ := 2 * n ^ k
    let den : ℕ := k ^ k
    let term_q : ℚ := (num : ℚ) / (den : ℚ)
    (Rat.floor term_q).toNat

theorem a_eq_a' : a = a' := rfl

/--
OEIS A322072 Conjecture: The difference $a(n + 1) - a(n)$ between two consecutive terms is not a perfect square except for $n = 1, 5$ and $6$.
-/
theorem oeis_322072_conjecture_0 {n : ℕ} (hn : 1 ≤ n) :
  (∃ m : ℕ, a (n + 1) - a n = m ^ 2) ↔ n = 1 ∨ n = 5 ∨ n = 6 := by
  rw [a_eq_a']
  constructor
  · intro hex
    rcases Nat.lt_or_ge n 7 with h6 | h6
    · interval_cases n
      · left; rfl
      · exfalso; obtain ⟨m, hm⟩ := hex
        rw [show a' (2+1) - a' 2 = 6 from by native_decide] at hm
        have : m ≤ 2 := by nlinarith [hm]
        interval_cases m <;> omega
      · exfalso; obtain ⟨m, hm⟩ := hex
        rw [show a' (3+1) - a' 3 = 10 from by native_decide] at hm
        have : m ≤ 3 := by nlinarith [hm]
        interval_cases m <;> omega
      · exfalso; obtain ⟨m, hm⟩ := hex
        rw [show a' (4+1) - a' 4 = 15 from by native_decide] at hm
        have : m ≤ 3 := by nlinarith [hm]
        interval_cases m <;> omega
      · right; left; rfl
      · right; right; rfl
    · sorry
  · rintro (rfl | rfl | rfl)
    · exact ⟨2, by native_decide⟩
    · exact ⟨5, by native_decide⟩
    · exact ⟨6, by native_decide⟩
