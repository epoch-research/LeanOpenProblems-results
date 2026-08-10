import FormalConjectures.Util.ProblemImports
open BigOperators Finset Nat Real

def omega_mult (k : ℕ) : ℕ := k.factorization.sum (fun _ e => e)
noncomputable def liouvilleH (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, ((if (omega_mult k : ℤ) % 2 = 0 then (1:ℤ) else -1 : ℤ) : ℝ) / (k:ℝ)
noncomputable def b (n : ℕ) : ℝ :=
  Finset.sum (Icc 1 n) fun k =>
    let sign : ℤ := (fun k : ℕ =>
      let exponent : ℤ := (k : ℤ) - (omega_mult k : ℤ)
      if exponent % 2 = 0 then 1 else -1) k
    (sign : ℝ) / (k : ℝ)

lemma parity_sign_even (k : ℕ) (hk : Even k) :
    (if ((k : ℤ) - (omega_mult k : ℤ)) % 2 = 0 then (1:ℤ) else -1) =
    (if (omega_mult k : ℤ) % 2 = 0 then (1:ℤ) else -1) := by
  rcases hk with ⟨m,rfl⟩
  by_cases h : (omega_mult (2*m) : ℤ) % 2 = 0
  · simp [h, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  sorry
