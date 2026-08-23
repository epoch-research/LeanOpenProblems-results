import FormalConjectures.Util.ProblemImports

/-!
Discrete orthogonality for the 2-4-6-8 representation function.

We work with the standard additive character on `ZMod P`.
-/

open Complex Finset Nat
open scoped Real

namespace Tail2468

variable {P : ℕ} [NeZero P]

/-- `e(θ) = exp(2πi θ)`. -/
noncomputable def e (θ : ℝ) : ℂ := cexp (2 * π * I * θ)

lemma e_add (a b : ℝ) : e (a + b) = e a * e b := by
  unfold e
  rw [← Complex.exp_add]
  ring_nf

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_int (n : ℤ) : e (n : ℝ) = 1 := by
  simpa [e] using Complex.exp_int_mul_two_pi_mul_I n

lemma e_nat (n : ℕ) : e (n : ℝ) = 1 := e_int n

lemma e_periodic (θ : ℝ) (n : ℤ) : e (θ + n) = e θ := by
  rw [e_add, e_int, mul_one]

lemma norm_e (θ : ℝ) : ‖e θ‖ = 1 := by
  simp [e, Complex.norm_exp]
  ring

lemma e_neg (θ : ℝ) : e (-θ) = starRingEnd ℂ (e θ) := by
  unfold e
  rw [← Complex.exp_conj]
  simp [map_mul, map_ofNat]
  ring_nf

/-- Standard complete geometric sum. -/
lemma sum_e_range_eq (α : ℝ) (N : ℕ) :
    ∑ j ∈ range N, e (j * α) =
      if e α = 1 then (N : ℂ) else (1 - e (N * α)) / (1 - e α) := by
  have hpow : ∀ n : ℕ, e (n * α) = e α ^ n := by
    intro n
    induction n with
    | zero => simp [e_zero]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, e_add, ih, pow_succ, mul_comm]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    split_ifs with h
    · simp [h, hpow]
    · have hne : (1 - e α) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      field_simp [hne]
      have : e (N * α) * e α = e ((N + 1 : ℕ) * α) := by
        rw [← e_add]; congr 1; push_cast; ring
      rw [this]
      ring

lemma sum_e_int_div (Q : ℕ) (hQ : 0 < Q) (m : ℤ) :
    ∑ h ∈ range Q, e (h * m / Q) = if (Q : ℤ) ∣ m then (Q : ℂ) else 0 := by
  -- `e(h m / Q) = exp(2πi h m / Q)`. This is a standard geometric sum.
  have : ∀ h : ℕ, e (h * m / Q) = e ((h : ℝ) * ((m : ℝ) / Q)) := by
    intro h; ring_nf
  -- Use the cyclotomic evaluation: sum of Q-th roots.
  let ω : ℂ := e (m / Q)
  have hpow : ∀ h : ℕ, e ((h : ℝ) * (m : ℝ) / Q) = ω ^ h := by
    intro h
    induction h with
    | zero => simp [e_zero, ω]
    | succ h ih =>
      have : ((h + 1 : ℕ) : ℝ) * (m : ℝ) / Q = (h : ℝ) * (m : ℝ) / Q + (m : ℝ) / Q := by
        push_cast; ring
      rw [this, e_add, ih]
      simp [ω, pow_succ, mul_comm]
  simp_rw [this, hpow]
  -- sum ω^h = Q if ω=1 else 0
  have hω1 : ω = 1 ↔ (Q : ℤ) ∣ m := by
    constructor
    · intro h
      -- e(m/Q)=1 ⇒ m/Q ∈ ℤ
      have : e (m / Q) = 1 := h
      -- exp(2πi m/Q)=1 ⇒ m/Q ∈ ℤ
      have him : (m : ℝ) / Q = ((m : ℝ) / Q) := rfl
      -- Use that e(θ)=1 iff θ ∈ ℤ
      have he1 : e (m / Q) = 1 → ∃ k : ℤ, (m : ℝ) / Q = k := by
        intro heq
        -- cexp(2πi θ)=1 ↔ θ ∈ ℤ
        have : cexp (2 * π * I * (m / Q)) = 1 := heq
        -- Mathlib: Complex.exp_eq_one_iff
        have hexp := Complex.exp_eq_one_iff.1 this
        rcases hexp with ⟨k, hk⟩
        -- 2πi * (m/Q) = 2πi k, so m/Q = k
        refine ⟨k, ?_⟩
        have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        have h2 : (2 : ℂ) ≠ 0 := by norm_num
        have hI : I ≠ 0 := I_ne_zero
        -- hk : 2 * π * I * (m/Q) = 2 * π * I * k
        have : (2 * π * I : ℂ) * (m / Q : ℂ) = (2 * π * I : ℂ) * (k : ℂ) := by
          convert hk using 1
          · simp [div_eq_mul_inv]
            ring_nf
          · simp; ring
        have hmul : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero h2 hπ) hI
        have := mul_left_cancel₀ hmul this
        exact_mod_cast this.symm ▸ (by
          -- (m/Q : ℂ) = k ⇒ (m:ℝ)/Q = k
          have : ((m : ℝ) / Q : ℂ) = (m : ℂ) / Q := by
            simp [div_eq_mul_inv]
          -- actually just use ofReal
          sorry)
      rcases he1 this with ⟨k, hk⟩
      -- (m:ℝ)/Q = k ⇒ m = k * Q
      have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
      have : (m : ℝ) = k * Q := by
        field_simp [hQ0] at hk
        linarith
      have : (m : ℤ) = k * (Q : ℤ) := by exact_mod_cast this
      exact ⟨k, by linarith⟩
    · intro ⟨k, hk⟩
      have : (m : ℝ) / Q = k := by
        have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
        field_simp [hQ0]
        exact_mod_cast hk
      rw [ω, this, e_int]
  by_cases hdiv : (Q : ℤ) ∣ m
  · simp [hdiv]
    have : ω = 1 := hω1.2 hdiv
    simp [this]
  · simp [hdiv]
    have hω : ω ≠ 1 := fun h => hdiv (hω1.1 h)
    have hne : ω - 1 ≠ 0 := sub_ne_zero.mpr hω
    -- geometric sum
    have : ∑ h ∈ range Q, ω ^ h = (ω ^ Q - 1) / (ω - 1) := by
      rw [geom_sum_eq hω]
      ring
    rw [this]
    have hωQ : ω ^ Q = 1 := by
      -- e(m/Q)^Q = e(m) = 1
      have : ω ^ Q = e (m) := by
        have : ω ^ Q = e ((Q : ℝ) * (m : ℝ) / Q) := by
          -- e(m/Q)^Q = e(Q * m/Q) = e(m)
          have h1 : ∀ n : ℕ, ω ^ n = e ((n : ℝ) * (m : ℝ) / Q) := by
            intro n
            induction n with
            | zero => simp [e_zero, ω]
            | succ n ih =>
              rw [pow_succ, ih]
              have : ((n + 1 : ℕ) : ℝ) * (m : ℝ) / Q =
                  (n : ℝ) * (m : ℝ) / Q + (m : ℝ) / Q := by push_cast; ring
              rw [this, e_add]
              simp [ω, mul_comm]
          simpa using h1 Q
        have : (Q : ℝ) * (m : ℝ) / Q = m := by
          have : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
          field_simp
        rw [this] at this
        simpa using this
      simpa [e_int] using this
    simp [hωQ, hne]

end Tail2468
