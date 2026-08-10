import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000


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

def a_fast (n : ℕ) : ℕ :=
  ((List.range n).map (fun i =>
    let k := i + 1
    let num : ℕ := 2 * n ^ k
    let den : ℕ := k ^ k
    num / den
  )).sum

theorem sum_Icc_eq_range (n : ℕ) (f : ℕ → ℕ) :
  Finset.sum (Finset.Icc 1 n) f = ((List.range n).map (fun i => f (i + 1))).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos n) f]
    rw [ih]
    rw [List.range_succ, List.map_append, List.sum_append]
    rfl

theorem a_eq_a_fast (n : ℕ) : a n = a_fast n := by
  dsimp [a, a_fast]
  have h1 : Finset.sum (Finset.Icc 1 n) (fun k => (Rat.floor (((2 * n ^ k : ℕ) : ℚ) / ((k ^ k : ℕ) : ℚ))).toNat) =
           Finset.sum (Finset.Icc 1 n) (fun k => (2 * n ^ k) / (k ^ k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg Int.toNat (Rat.floor_natCast_div_natCast (2 * n ^ k) (k ^ k))
  rw [h1]
  exact sum_Icc_eq_range n (fun k => (2 * n ^ k) / (k ^ k))

theorem direction_back {n : ℕ} (h : n = 1 ∨ n = 5 ∨ n = 6) :
  ∃ m : ℕ, a (n + 1) - a n = m ^ 2 := by
  rcases h with rfl | rfl | rfl
  · use 2
    rw [a_eq_a_fast 2, a_eq_a_fast 1]
    rfl
  · use 5
    rw [a_eq_a_fast 6, a_eq_a_fast 5]
    rfl
  · use 6
    rw [a_eq_a_fast 7, a_eq_a_fast 6]
    rfl

lemma not_square_6 (m : ℕ) : m ^ 2 ≠ 6 := by
  intro h
  have : m < 3 := by
    by_contra h2
    have : m ≥ 3 := by omega
    have : m ^ 2 ≥ 9 := by nlinarith
    omega
  interval_cases m <;> omega

lemma not_square_10 (m : ℕ) : m ^ 2 ≠ 10 := by
  intro h
  have : m < 4 := by
    by_contra h2
    have : m ≥ 4 := by omega
    have : m ^ 2 ≥ 16 := by nlinarith
    omega
  interval_cases m <;> omega

lemma not_square_15 (m : ℕ) : m ^ 2 ≠ 15 := by
  intro h
  have : m < 4 := by
    by_contra h2
    have : m ≥ 4 := by omega
    have : m ^ 2 ≥ 16 := by nlinarith
    omega
  interval_cases m <;> omega

theorem is_square_iff_bounded (X : ℕ) : (∃ m : ℕ, m ^ 2 = X) ↔ (∃ m ≤ X, m ^ 2 = X) := by
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_, rfl⟩
    by_cases hm : m = 0
    · subst hm; rfl
    · calc m ≤ m * m := Nat.le_mul_self m
        _ = m ^ 2 := by ring
  · rintro ⟨m, _, h⟩
    exact ⟨m, h⟩

theorem direction_forward_le_12 {n : ℕ} (hn : 1 ≤ n) (hn12 : n ≤ 12) (h : ∃ m : ℕ, a (n + 1) - a n = m ^ 2) :
  n = 1 ∨ n = 5 ∨ n = 6 := by
  interval_cases n
  · left; rfl
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 3, a_eq_a_fast 2] at hm
    have h_diff : a_fast 3 - a_fast 2 = 6 := by rfl
    rw [h_diff] at hm
    exact not_square_6 m hm.symm
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 4, a_eq_a_fast 3] at hm
    have h_diff : a_fast 4 - a_fast 3 = 10 := by rfl
    rw [h_diff] at hm
    exact not_square_10 m hm.symm
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 5, a_eq_a_fast 4] at hm
    have h_diff : a_fast 5 - a_fast 4 = 15 := by rfl
    rw [h_diff] at hm
    exact not_square_15 m hm.symm
  · right; left; rfl
  · right; right; rfl
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 8, a_eq_a_fast 7] at hm
    have h_sq : ∃ m ≤ a_fast 8 - a_fast 7, m ^ 2 = a_fast 8 - a_fast 7 := by
      rw [← is_square_iff_bounded]
      exact ⟨m, hm.symm⟩
    have h_not : ¬ ∃ m ≤ a_fast 8 - a_fast 7, m ^ 2 = a_fast 8 - a_fast 7 := by decide
    exact h_not h_sq
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 9, a_eq_a_fast 8] at hm
    have h_sq : ∃ m ≤ a_fast 9 - a_fast 8, m ^ 2 = a_fast 9 - a_fast 8 := by
      rw [← is_square_iff_bounded]
      exact ⟨m, hm.symm⟩
    have h_not : ¬ ∃ m ≤ a_fast 9 - a_fast 8, m ^ 2 = a_fast 9 - a_fast 8 := by decide
    exact h_not h_sq
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 10, a_eq_a_fast 9] at hm
    have h_sq : ∃ m ≤ a_fast 10 - a_fast 9, m ^ 2 = a_fast 10 - a_fast 9 := by
      rw [← is_square_iff_bounded]
      exact ⟨m, hm.symm⟩
    have h_not : ¬ ∃ m ≤ a_fast 10 - a_fast 9, m ^ 2 = a_fast 10 - a_fast 9 := by decide
    exact h_not h_sq
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 11, a_eq_a_fast 10] at hm
    have h_sq : ∃ m ≤ a_fast 11 - a_fast 10, m ^ 2 = a_fast 11 - a_fast 10 := by
      rw [← is_square_iff_bounded]
      exact ⟨m, hm.symm⟩
    have h_not : ¬ ∃ m ≤ a_fast 11 - a_fast 10, m ^ 2 = a_fast 11 - a_fast 10 := by decide
    exact h_not h_sq
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 12, a_eq_a_fast 11] at hm
    have h_sq : ∃ m ≤ a_fast 12 - a_fast 11, m ^ 2 = a_fast 12 - a_fast 11 := by
      rw [← is_square_iff_bounded]
      exact ⟨m, hm.symm⟩
    have h_not : ¬ ∃ m ≤ a_fast 12 - a_fast 11, m ^ 2 = a_fast 12 - a_fast 11 := by decide
    exact h_not h_sq
  · exfalso
    rcases h with ⟨m, hm⟩
    rw [a_eq_a_fast 13, a_eq_a_fast 12] at hm
    have h_sq : ∃ m ≤ a_fast 13 - a_fast 12, m ^ 2 = a_fast 13 - a_fast 12 := by
      rw [← is_square_iff_bounded]
      exact ⟨m, hm.symm⟩
    have h_not : ¬ ∃ m ≤ a_fast 13 - a_fast 12, m ^ 2 = a_fast 13 - a_fast 12 := by decide
    exact h_not h_sq

/--
OEIS A322072 Conjecture: The difference $a(n + 1) - a(n)$ between two consecutive terms is not a perfect square except for $n = 1, 5$ and $6$.
-/
theorem oeis_322072_conjecture_0 {n : ℕ} (hn : 1 ≤ n) :
  (∃ m : ℕ, a (n + 1) - a n = m ^ 2) ↔ n = 1 ∨ n = 5 ∨ n = 6 := by
  constructor
  · intro h
    by_cases hn12 : n ≤ 12
    · exact direction_forward_le_12 hn hn12 h
    · -- n ≥ 13 case:
      sorry
  · intro h
    exact direction_back h

