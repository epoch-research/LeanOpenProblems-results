import FormalConjectures.Util.ProblemImports

open Rat Nat Finset

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let N : ℤ := B_nm1.num
    let D : ℕ := B_nm1.den
    let q1 : ℚ := (N : ℚ) / n_q
    let q2 : ℚ := (D : ℚ) / (n_q * n_q)
    let F_n : ℚ := q1 + q2
    F_n.den

def A309132_conjecture : Prop :=
  ∀ n : ℕ, 1 < n → (a n = 1 ↔ Nat.Prime n)

def agoh_giuga_condition (n : ℕ) : Prop :=
  1 < n ∧ (n : ℤ) ∣ (Finset.sum (Finset.range n) (fun k : ℕ => (k : ℤ)^(n - 1)) + 1)

def agoh_giuga_conjecture : Prop :=
  ∀ n : ℕ, 1 < n → (Nat.Prime n ↔ agoh_giuga_condition n)

/-- The CORE pointwise number-theoretic equivalence (Kellner). -/
theorem core (n : ℕ) (hn : 1 < n) :
    (n : ℤ)^2 ∣ ((bernoulli (n-1)).num * n + (bernoulli (n-1)).den) ↔
    (n : ℤ) ∣ ((∑ k ∈ Finset.range n, (k : ℤ)^(n-1)) + 1) := by
  sorry

/-- Reduction 1: a(n)=1 iff n²|(Nn+D). -/
theorem a_eq_one_iff (n : ℕ) (hn : 1 < n) :
    a n = 1 ↔ (n : ℤ)^2 ∣ ((bernoulli (n-1)).num * n + (bernoulli (n-1)).den) := by
  have hn0 : n ≠ 0 := by omega
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  set N : ℤ := (bernoulli (n-1)).num with hN
  set D : ℕ := (bernoulli (n-1)).den with hD
  have hav : a n = ((N : ℚ) / n + (D : ℚ) / (n * n)).den := by
    simp only [a, if_neg hn0, hN, hD]
  rw [hav]
  have heq : (N : ℚ) / n + (D : ℚ) / (n * n)
      = ((N * (n:ℤ) + (D:ℤ) : ℤ) : ℚ) / (((n:ℤ)^2 : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq]
  have hn2 : ((n:ℤ)^2 : ℤ) ≠ 0 := by positivity
  rw [Rat.den_div_intCast_eq_one_iff _ _ hn2]

theorem pointwise (n : ℕ) (hn : 1 < n) :
    a n = 1 ↔ agoh_giuga_condition n := by
  rw [a_eq_one_iff n hn, agoh_giuga_condition]
  rw [core n hn]
  constructor
  · intro h; exact ⟨hn, h⟩
  · intro h; exact h.2

theorem main : A309132_conjecture ↔ agoh_giuga_conjecture := by
  constructor
  · intro h n hn
    rw [← pointwise n hn]
    exact (h n hn).symm
  · intro h n hn
    rw [pointwise n hn]
    exact (h n hn).symm
