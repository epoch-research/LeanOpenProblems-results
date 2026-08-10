import FormalConjectures.Util.ProblemImports

open Nat

/--
A264025: Number of ways to write $n$ as $x^2 + y(2y+1) + \frac{z(z+1)}{2}$
where $x, y$ and $z$ are nonnegative integers with $z$ or $z+1$ prime.
-/
noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1))
  }

/-- The set of indices n for which A264025 n = 1, according to the conjecture. -/
def A264025_singletons : Finset ℕ :=
  {1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344}

/-- The explicit finite set of representations of `n`. -/
def reps (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1) ×ˢ
      Finset.range ((2 * n).sqrt + 1)).filter
    (fun p => p.1 ^ 2 + p.2.1 * (2 * p.2.1 + 1) + p.2.2 * (p.2.2 + 1) / 2 = n ∧
      (Nat.Prime p.2.2 ∨ Nat.Prime (p.2.2 + 1)))

/-- The defining predicate of `A264025` is equivalent to membership in `reps n`. -/
theorem mem_reps (n : ℕ) (p : ℕ × ℕ × ℕ) :
    (p.1 ^ 2 + p.2.1 * (2 * p.2.1 + 1) + p.2.2 * (p.2.2 + 1) / 2 = n ∧
      (Nat.Prime p.2.2 ∨ Nat.Prime (p.2.2 + 1))) ↔ p ∈ reps n := by
  obtain ⟨x, y, z⟩ := p
  simp only [reps, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨heq, hp⟩
    have hdvd : 2 ∣ z * (z + 1) := (Nat.even_mul_succ_self z).two_dvd
    have hz2 : z * (z + 1) = 2 * (z * (z + 1) / 2) := by omega
    refine ⟨⟨?_, ?_, ?_⟩, heq, hp⟩
    · have : x * x ≤ n := by
        nlinarith [Nat.zero_le (y * (2 * y + 1)), Nat.zero_le (z * (z + 1) / 2)]
      have := (Nat.le_sqrt).2 this; omega
    · have : y * y ≤ n := by
        nlinarith [Nat.zero_le (x ^ 2), Nat.zero_le (z * (z + 1) / 2)]
      have := (Nat.le_sqrt).2 this; omega
    · have : z * z ≤ 2 * n := by
        nlinarith [Nat.zero_le (x ^ 2), Nat.zero_le (y * (2 * y + 1))]
      have := (Nat.le_sqrt).2 this; omega
  · rintro ⟨_, heq, hp⟩
    exact ⟨heq, hp⟩

/-- `A264025 n` equals the cardinality of the explicit finite set `reps n`. -/
theorem A264025_eq (n : ℕ) : A264025 n = (reps n).card := by
  rw [A264025]
  rw [show {p : ℕ × ℕ × ℕ // (let (x, y, z) := p;
      x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧ (Nat.Prime z ∨ Nat.Prime (z + 1)))}
      = {p : ℕ × ℕ × ℕ // p ∈ reps n} from ?_]
  · rw [Nat.card_eq_finsetCard]
  · congr 1
    ext p
    obtain ⟨x, y, z⟩ := p
    exact mem_reps n (x, y, z)

/-- Backward direction of part (ii): each listed index is a singleton (finite check). -/
theorem A264025_singletons_card_one (n : ℕ) (hn : n ∈ A264025_singletons) :
    A264025 n = 1 := by
  rw [A264025_eq]
  simp only [A264025_singletons, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> native_decide

/-- Positivity holds on the finite range `1 ≤ n ≤ 1344` (finite check). -/
theorem A264025_pos_le (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 1344) : 0 < A264025 n := by
  have key : ∀ m ∈ Finset.Icc 1 1344, 0 < (reps m).card := by native_decide
  rw [A264025_eq]
  exact key n (Finset.mem_Icc.2 ⟨h1, h2⟩)

/-- On the finite range `n ≤ 1344`, singletons occur exactly on the listed indices
(finite check). -/
theorem A264025_forward_le (n : ℕ) (h : n ≤ 1344) (hc : A264025 n = 1) :
    n ∈ A264025_singletons := by
  have key : ∀ m ∈ Finset.Icc 0 1344, (reps m).card = 1 → m ∈ A264025_singletons := by
    native_decide
  rw [A264025_eq] at hc
  exact key n (Finset.mem_Icc.2 ⟨Nat.zero_le n, h⟩) hc

/-- The single open core of Zhi-Wei Sun's conjecture A264025: every `n > 1344` has at
least two representations.  All other content of the conjecture is reduced to this.

Reduction: multiplying by `8`, a representation of `n` corresponds bijectively to a
solution of `8*n+2 = (2*z+1)^2 + (4*y+1)^2 + 8*x^2` with `z` or `z+1` prime.  Proving
`a(n) ≥ 2` is thus an equidistribution statement for representations of the ternary form
`X^2 + Y^2 + 8 Z^2` correlated with the primality of `(X-1)/2`, which is open analytic
number theory (Duke-type equidistribution plus a prime sieve), not available in Mathlib;
no finite covering exists because the minimal required `z` is unbounded. -/
theorem A264025_ge_two_of_gt (n : ℕ) (h : 1344 < n) : 2 ≤ A264025 n := sorry

/--
A264025 Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
-/
theorem oeis_264025_conjecture_0 :
  (∀ n : ℕ, n > 0 → A264025 n > 0)
  ∧ (∀ n : ℕ, A264025 n = 1 ↔ n ∈ A264025_singletons) :=
by
  refine ⟨?positivity, fun n => ⟨?forward, A264025_singletons_card_one n⟩⟩
  case positivity =>
    intro n hn
    by_cases h : n ≤ 1344
    · exact A264025_pos_le n hn h
    · exact lt_of_lt_of_le (by norm_num) (A264025_ge_two_of_gt n (by omega))
  case forward =>
    intro hc
    by_cases h : n ≤ 1344
    · exact A264025_forward_le n h hc
    · exact absurd hc (by have := A264025_ge_two_of_gt n (by omega); omega)
