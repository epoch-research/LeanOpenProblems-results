import FormalConjectures.Util.ProblemImports

open List Nat Finset Classical WithBot

/--
A241898: $a(n)$ is the largest integer such that $n = a(n)^2 + \dots$ is a decomposition of $n$ into a sum of at most four nondecreasing squares.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let P (k : ℕ) : Prop :=
    k > 0 ∧
    ∃ s : List ℕ,
      s.length > 0 ∧ s.length ≤ 4 ∧
      (s.map (fun b => b ^ 2)).sum = n ∧
      s.Sorted (· ≤ ·) ∧
      s.head? = Option.some k -- Qualified 'some' to resolve ambiguity

  -- We explicitly provide the DecidablePred instance using classical logic, which is sound
  -- because the existential quantifier is over a finite, bounded search space.
  have dec : DecidablePred P := fun k => Classical.dec (P k)

  -- Filter the range of possible bases k up to $\lfloor\sqrt{n}\rfloor$.
  let S : Finset ℕ := @Finset.filter _ P dec (range (n.sqrt + 1))

  -- Finset.max returns `WithBot ℕ`. We use `rec 0 id` to convert to `ℕ`,
  -- mapping ⊥ (empty set max) to 0 and a successful max to its value.
  (S.max).rec 0 id

/--
The conjecture below is false: `736 > 599`, yet `a 736 = 4`.  Indeed, the only
decompositions of `736` into at most four nondecreasing squares are
`736 = 4² + 12² + 24²` and `736 = 4² + 8² + 16² + 20²`, both of which have
smallest base `4`.  In particular, `736` cannot be written as a sum of at most
four squares whose bases are all `≥ 8`.  The following auxiliary lemmas record
this arithmetic impossibility.
-/
private theorem aux_no1 : ∀ x : ℕ, 8 ≤ x → x ^ 2 ≠ 736 := by
  intro x hx h
  have : x ≤ 27 := by nlinarith
  interval_cases x <;> omega

private theorem aux_no2 : ∀ x y : ℕ, 8 ≤ x → x ≤ y → x ^ 2 + y ^ 2 ≠ 736 := by
  intro x y hx hxy h
  have hy : y ≤ 27 := by nlinarith
  have hx19 : x ≤ 19 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

private theorem aux_no3 : ∀ x y z : ℕ, 8 ≤ x → x ≤ y → y ≤ z →
    x ^ 2 + y ^ 2 + z ^ 2 ≠ 736 := by
  intro x y z hx hxy hyz h
  have hz : z ≤ 27 := by nlinarith
  have hy : y ≤ 27 := by omega
  have hx15 : x ≤ 15 := by nlinarith
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

private theorem aux_no4 : ∀ x y z w : ℕ, 8 ≤ x → x ≤ y → y ≤ z → z ≤ w →
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ≠ 736 := by
  intro x y z w hx hxy hyz hzw h
  have hw : w ≤ 27 := by nlinarith
  have hz : z ≤ 27 := by omega
  have hy : y ≤ 27 := by omega
  have hx13 : x ≤ 13 := by nlinarith
  interval_cases x <;> interval_cases y <;> interval_cases z <;> interval_cases w <;> omega

private theorem a_736_le_7 : a 736 ≤ 7 := by
  unfold a
  extract_lets P dec S
  cases hm : S.max with
  | bot => exact Nat.zero_le _
  | coe v =>
    show v ≤ 7
    have hv : v ∈ S := Finset.mem_of_max hm
    simp only [S, Finset.mem_filter, Finset.mem_range] at hv
    obtain ⟨_hrange, hPv⟩ := hv
    obtain ⟨_hv0, s, hs1, hs2, hsum, hsorted, hhead⟩ := hPv
    by_contra hlt
    have hv8 : 8 ≤ v := by omega
    rcases s with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, tail⟩⟩⟩⟩
    · simp at hs1
    · simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
      exact aux_no1 w0 hv8 (by omega)
    · simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
      rw [List.sorted_cons] at hsorted
      obtain ⟨h0, _⟩ := hsorted
      have := h0 w1 (by simp)
      exact aux_no2 w0 w1 hv8 this (by omega)
    · simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
      simp only [List.sorted_cons] at hsorted
      obtain ⟨h0, h1, _⟩ := hsorted
      have e01 := h0 w1 (by simp)
      have e12 := h1 w2 (by simp)
      exact aux_no3 w0 w1 w2 hv8 e01 e12 (by omega)
    · rcases tail with _ | ⟨w4, tail2⟩
      · simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
        simp only [List.sorted_cons] at hsorted
        obtain ⟨h0, h1, h2, _⟩ := hsorted
        have e01 := h0 w1 (by simp)
        have e12 := h1 w2 (by simp)
        have e23 := h2 w3 (by simp)
        exact aux_no4 w0 w1 w2 w3 hv8 e01 e12 e23 (by omega)
      · simp only [List.length_cons] at hs2; omega

/--
The conjecture `∀ n, 599 < n → a n > 7` is **false**: taking `n = 736` gives a
counterexample, since `a 736 = 4 ≤ 7`.
-/
theorem oeis_241898_conjecture_0.disproof : ¬ (∀ n : ℕ, 599 < n → a n > 7) := by
  intro H
  have h736 : a 736 > 7 := H 736 (by norm_num)
  have hle : a 736 ≤ 7 := a_736_le_7
  omega
