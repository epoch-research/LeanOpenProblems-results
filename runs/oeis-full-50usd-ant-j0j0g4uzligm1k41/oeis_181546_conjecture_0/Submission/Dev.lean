import FormalConjectures.Util.ProblemImports

open Filter Asymptotics Real
open scoped Nat

noncomputable section

-- abbreviations
local notation "Φ" => goldenRatio
local notation "Ψ" => goldenConj

theorem phi_pow_succ_succ (m : ℕ) : Φ ^ (m+2) = Φ^(m+1) + Φ^m := by
  have := goldenRatio_sq
  calc Φ ^ (m+2) = Φ^2 * Φ^m := by ring
    _ = (Φ + 1) * Φ^m := by rw [goldenRatio_sq]
    _ = Φ^(m+1) + Φ^m := by ring

theorem psi_pow_succ_succ (m : ℕ) : Ψ ^ (m+2) = Ψ^(m+1) + Ψ^m := by
  calc Ψ ^ (m+2) = Ψ^2 * Ψ^m := by ring
    _ = (Ψ + 1) * Ψ^m := by rw [goldenConj_sq]
    _ = Ψ^(m+1) + Ψ^m := by ring

-- Lucas numbers closed form
theorem lucas_real (n : ℕ) : (lucasNumber n : ℝ) = Φ ^ n + Ψ ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [lucasNumber, LucasSequence.V]; norm_num
    | 1 =>
      simp only [lucasNumber, LucasSequence.V, pow_one]
      push_cast
      linarith [goldenRatio_add_goldenConj]
    | (m+2) =>
      have hrec : lucasNumber (m+2) = lucasNumber (m+1) + lucasNumber m := by
        simp [lucasNumber, LucasSequence.V]
      rw [hrec]
      push_cast
      rw [ih (m+1) (by omega), ih m (by omega), phi_pow_succ_succ, psi_pow_succ_succ]
      ring

-- limit value equals φ^L
noncomputable def limit_value (L : ℕ) : ℝ :=
  let fib_L : ℝ := Nat.fib L
  let lucas_L : ℝ := (lucasNumber L : ℤ)
  (fib_L * Real.sqrt 5 + lucas_L) / 2

theorem limit_value_eq (L : ℕ) : limit_value L = Φ ^ L := by
  unfold limit_value
  simp only
  rw [lucas_real, Real.coe_fib_eq]
  have h5 : Real.sqrt 5 ≠ 0 := by positivity
  field_simp
  ring
