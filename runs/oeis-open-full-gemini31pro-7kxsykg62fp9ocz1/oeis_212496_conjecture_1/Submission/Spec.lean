import FormalConjectures.Util.ProblemImports

open BigOperators Finset Nat Real

def omega_mult (k : ℕ) : ℕ :=
  k.factorization.sum (fun _ e => e)

def a (n : ℕ) : ℤ :=
  Finset.sum (Icc 1 n) fun k =>
    let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
    if exponent % 2 = 0 then 1 else -1

noncomputable
def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

theorem oeis_212496_conjecture_1 (n : ℕ) :
  (n > 0 → b n < 0) ∧
  (n > 1 → b n < -1 / sqrt (n : ℝ)) ∧
  (n > 2008 → b n > -log (log (n : ℝ)) / sqrt (n : ℝ)) :=
by sorry

theorem oeis_212496_conjecture_1.disproof : ¬ (type_of% @oeis_212496_conjecture_1) := by
  intro h
  have h2009 := h 2009
  rcases h2009 with ⟨_, _, h3⟩
  sorry
