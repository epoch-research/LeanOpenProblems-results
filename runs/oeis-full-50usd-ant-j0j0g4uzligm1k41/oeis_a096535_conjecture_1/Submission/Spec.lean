import FormalConjectures.Util.ProblemImports

/--
A096535: $a(0) = a(1) = 1$; $a(n) = (a(n-1) + a(n-2)) \bmod n$.
-/
def A096535 : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => (A096535 (n + 1) + A096535 n) % (n + 2)

/-!
## Analysis of the conjecture

`oeis_a096535_conjecture_1` (OEIS A096535, conjecture 1) states that every natural
number `k` occurs infinitely often in the sequence.

This is a genuinely open problem. Empirically the statement is true: numerically the
ratio `a(n)/n` equidistributes on `[0,1]`, and each fixed value `k` occurs with the
harmonic frequency `≈ log N` predicted by a dynamical Borel–Cantelli heuristic. The
dynamics is a non-autonomous perturbation of the hyperbolic toral automorphism
`(x,y) ↦ (y, x+y mod 1)`; asking whether the specific orbit hits the shrinking target
`{a(n) = k}` (of measure `1/n`, with `∑ 1/n = ∞`) infinitely often is a
shrinking-target / dynamical Borel–Cantelli question for a *specific* orbit — beyond
current techniques, which is exactly why OEIS records it as an (unproved) conjecture.

Below we formalize the strongest fact that *is* rigorously provable about the sequence:
it is unbounded.  (Unboundedness concerns large values and does not settle the
conjecture, which is about attaining each specific value infinitely often.)
-/

/-- Every term is bounded by `n + 2` (in fact by `n` for `n ≥ 2`). -/
lemma A096535_lt (n : ℕ) : A096535 n < n + 2 := by
  match n with
  | 0 => decide
  | 1 => decide
  | k+2 =>
    show (A096535 (k+1) + A096535 k) % (k+2) < k + 2 + 2
    exact lt_trans (Nat.mod_lt _ (by omega)) (by omega)

/-- Two consecutive terms are never both zero. -/
lemma A096535_no_consec_zero (n : ℕ) : ¬ (A096535 n = 0 ∧ A096535 (n+1) = 0) := by
  induction n with
  | zero => decide
  | succ k ih =>
    rintro ⟨h1, h2⟩
    apply ih
    have hrec : A096535 (k+2) = (A096535 (k+1) + A096535 k) % (k+2) := rfl
    rw [h1, Nat.zero_add, Nat.mod_eq_of_lt (A096535_lt k)] at hrec
    exact ⟨by rw [← hrec]; exact h2, h1⟩

/-- A sequence satisfying the plain Fibonacci recurrence `b(j+2) = b(j+1) + b(j)` with a
positive start is unbounded. -/
lemma fib_type_unbounded (b : ℕ → ℕ) (hrec : ∀ j, b (j+2) = b (j+1) + b j)
    (hpos : b 0 ≠ 0 ∨ b 1 ≠ 0) : ∀ M, ∃ j, M < b j := by
  have h2 : b 2 = b 1 + b 0 := hrec 0
  have h3 : b 3 = b 2 + b 1 := hrec 1
  obtain ⟨m, hm0, hm1⟩ : ∃ m, 1 ≤ b m ∧ 1 ≤ b (m+1) := by
    rcases hpos with h | h
    · rcases Nat.eq_zero_or_pos (b 1) with h1 | h1
      · exact ⟨2, show 1 ≤ b 2 by omega, show 1 ≤ b 3 by omega⟩
      · exact ⟨0, show 1 ≤ b 0 by omega, show 1 ≤ b 1 by omega⟩
    · exact ⟨1, show 1 ≤ b 1 by omega, show 1 ≤ b 2 by omega⟩
  have hge1 : ∀ t, 1 ≤ b (m + t) := by
    have H : ∀ t, 1 ≤ b (m + t) ∧ 1 ≤ b (m + t + 1) := by
      intro t
      induction t with
      | zero => exact ⟨by simpa using hm0, by simpa using hm1⟩
      | succ s IH =>
        obtain ⟨A, B⟩ := IH
        refine ⟨by simpa using B, ?_⟩
        have hh : b (m + s + 2) = b (m+s+1) + b (m+s) := hrec (m+s)
        have e : m + (s+1) + 1 = (m + s) + 2 := by ring
        rw [e, hh]; omega
    exact fun t => (H t).1
  have hgrow : ∀ t, b m + t ≤ b (m + 2*t) := by
    intro t
    induction t with
    | zero => simp
    | succ s IH =>
      have key : m + 2*(s+1) = (m + 2*s) + 2 := by ring
      rw [key, hrec (m + 2*s)]
      have hp1 : 1 ≤ b (m + (2*s+1)) := hge1 (2*s+1)
      have e : m + (2*s+1) = m + 2*s + 1 := by ring
      rw [e] at hp1
      omega
  intro M
  exact ⟨m + 2*(M+1), by have := hgrow (M+1); omega⟩

/-- **The sequence `A096535` is unbounded.**  If it were bounded by `M`, then for
`n ≥ 2M+2` the sum of the two previous terms is `< n`, so no reduction occurs and the
sequence obeys the plain Fibonacci recurrence; starting from a non-zero pair it then
grows without bound, a contradiction. -/
theorem A096535_unbounded : ∀ M, ∃ n, M < A096535 n := by
  intro M
  by_contra hcon
  push_neg at hcon
  set N := 2*M + 2 with hN
  have hrec : ∀ j, A096535 (N + j + 2) = A096535 (N + j + 1) + A096535 (N + j) := by
    intro j
    have hunfold : A096535 (N + j + 2)
        = (A096535 (N + j + 1) + A096535 (N + j)) % (N + j + 2) := rfl
    rw [hunfold]
    apply Nat.mod_eq_of_lt
    have h1 := hcon (N + j + 1)
    have h2 := hcon (N + j)
    omega
  have hpos : A096535 (N + 0) ≠ 0 ∨ A096535 (N + 0 + 1) ≠ 0 := by
    have hnz := A096535_no_consec_zero N
    simp only [Nat.add_zero]
    tauto
  obtain ⟨j, hj⟩ := fib_type_unbounded (fun j => A096535 (N + j))
    (fun j => hrec j) hpos M
  have hle := hcon (N + j)
  have hj' : M < A096535 (N + j) := hj
  omega

/--
A096535 Three conjectures: (1) All numbers appear infinitely often, i.e., for every number k >= 0 and every frequency f > 0 there is an index i such that a(i) = k is the f-th occurrence of k in the sequence.
-/
theorem oeis_a096535_conjecture_1 :
  ∀ (k : ℕ), ∀ (N : ℕ), ∃ (i : ℕ), i > N ∧ A096535 i = k := by
  sorry
