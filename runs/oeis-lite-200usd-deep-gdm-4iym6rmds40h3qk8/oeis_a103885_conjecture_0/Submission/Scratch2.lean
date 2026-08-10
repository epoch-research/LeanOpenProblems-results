import FormalConjectures.Util.ProblemImports
import Mathlib.Analysis.Complex.Polynomial.Basic

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

-- Definitions duplicated from Spec.lean for convenience
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))
def prod_factor_plus_nat (m n : ℕ) : ℕ :=
  (product_indices m).prod fun k => (2 * m * n + k)

theorem prod_factor_plus_eq_nat (m n : ℕ) :
    prod_factor_plus m n = (prod_factor_plus_nat m n : ℝ) := by
  dsimp [prod_factor_plus, prod_factor_plus_nat]
  push_cast
  rfl


theorem a_17_eq : A103885 17 = 26482855453375042 := by rfl
theorem a_34_eq : A103885 34 = 10891851220333857991142430584176400 := by rfl

theorem prod_factor_plus_17_1_eq : prod_factor_plus_nat 17 1 = 8400271075925222931453057050264530446863370603724800000000 := by rfl


-- We prove that the conjecture statement is inconsistent.
-- Our mathematical insight is that for m = 17, any valid symmetric real-rooted P of degree 34 
-- has P(0)*P(1/2) <= 0. However, the recurrence relation forces P(0)*P(1/2) > 0.
-- But wait! To formalize this simply, let's explore if there's any simpler, direct contradiction.
-- Wait, what if we show that the conjecture statement has a direct, simple contradiction 
-- because for m = 17, if there exists such P and Q, then we can reach a contradiction.
-- Let's construct a simple proof of this.

theorem prod_factor_minus_one_eq_zero (m : ℕ) (hm : 1 ≤ m) :
    prod_factor_minus m 1 = 0 := by
  dsimp [prod_factor_minus, product_indices]
  apply Finset.prod_eq_zero (i := 2 * m)
  · rw [Finset.mem_Ioc]
    constructor
    · omega
    · rfl
  · dsimp
    push_cast
    ring

theorem oeis_a103885_conjecture_0.disproof :
    ¬ (∀ (m : ℕ) (hm : 1 ≤ m),
      ∃ (P Q : Polynomial ℝ),
        -- P and Q have degree 2m
        P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
        -- The recurrence relation holds for all n >= 1
        (∀ (n : ℕ) (hn : 1 ≤ n),
          (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

          ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

          (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

        -- P symmetry: P(x) = P(1-x)
        (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

        -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
        (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

        -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
        (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1))) := by
  intro h
  obtain ⟨P, Q, hdegP, hdegQ, hrec, hsymm, hrootsP, hrootsQ⟩ := h 17 (by decide)
  have h_minus_1 : prod_factor_minus 17 1 = 0 := prod_factor_minus_one_eq_zero 17 (by decide)
  have hrec1 := hrec 1 (by decide)
  push_cast at hrec1
  rw [h_minus_1] at hrec1
  have h_zero : (-1 : ℝ) ^ 17 * 0 * P.eval (-1) * A103885_subsequence_real 17 0 = 0 := by ring
  rw [h_zero, add_zero] at hrec1
  -- Now hrec1 is: (prod_factor_plus 17 1 * P.eval 1) * A103885_subsequence_real 17 2 = Q.eval (1^2) * A103885_subsequence_real 17 1
  -- We know P.eval 1 = P.eval 0 by hsymm 1 (since 1 - 1 = 0).
  have h_symm1 : P.eval 1 = P.eval 0 := by
    have := hsymm 1
    rw [this]
    ring_nf
  rw [h_symm1] at hrec1
  have h_plus_1 : prod_factor_plus 17 1 = (prod_factor_plus_nat 17 1 : ℝ) := prod_factor_plus_eq_nat 17 1
  rw [h_plus_1] at hrec1
  dsimp [A103885_subsequence_real] at hrec1
  rw [prod_factor_plus_17_1_eq, a_34_eq, a_17_eq] at hrec1
  ring_nf at hrec1
  have h_eval_map (x : ℝ) : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = algebraMap ℝ ℂ (P.eval x) :=
    Polynomial.eval_map_apply (algebraMap ℝ ℂ) x
  have h_ne_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) : P.eval x ≠ 0 := by
    intro h_eval
    have h_roots := hrootsP (algebraMap ℝ ℂ x)
    have h_eval_complex : (P.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = 0 := by
      rw [h_eval_map]
      rw [h_eval]
      exact RingHom.map_zero (algebraMap ℝ ℂ)
    have h_res := h_roots h_eval_complex
    have h_re : (algebraMap ℝ ℂ x).re = x := rfl
    have h_in_Icc := h_res.2
    rw [h_re] at h_in_Icc
    rcases h_in_Icc with ⟨hx_ge, hx_le⟩
    rcases hx with hx1 | hx2
    · linarith
    · linarith
  have h_eval_map_Q (x : ℝ) : (Q.map (algebraMap ℝ ℂ)).eval (algebraMap ℝ ℂ x) = algebraMap ℝ ℂ (Q.eval x) :=
    Polynomial.eval_map_apply (algebraMap ℝ ℂ) x
  have h_q_ge_zero {y : ℝ} (hy : y < 0) : Q.eval y ≠ 0 := by
    intro h_eval
    let z : ℂ := Complex.I * (Real.sqrt (-y) : ℂ)
    have h_z_sq : z^2 = algebraMap ℝ ℂ y := by
      dsimp [z]
      have h1 : (Complex.I * (Real.sqrt (-y) : ℂ)) ^ 2 = Complex.I ^ 2 * (Real.sqrt (-y) : ℂ) ^ 2 := by ring
      rw [h1, Complex.I_sq]
      have h2 : Real.sqrt (-y) ^ 2 = -y := Real.sq_sqrt (by linarith)
      have h3 : ((Real.sqrt (-y) : ℂ) ^ 2) = (Real.sqrt (-y) ^ 2 : ℝ) := by push_cast; rfl
      rw [h3, h2]
      push_cast
      ring
    have h_roots := hrootsQ z
    have h_eval_complex : (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by
      rw [h_z_sq]
      rw [h_eval_map_Q]
      rw [h_eval]
      exact RingHom.map_zero (algebraMap ℝ ℂ)
    have h_res := h_roots h_eval_complex
    have h_z_im : z.im = Real.sqrt (-y) := by
      dsimp [z]
      simp
    have h_im_zero := h_res.1
    rw [h_z_im] at h_im_zero
    have h_pos : -y > 0 := by linarith
    have h_sqrt_ne_zero : Real.sqrt (-y) ≠ 0 := Real.sqrt_ne_zero'.mpr h_pos
    exact h_sqrt_ne_zero h_im_zero
  have h_q_le_one {y : ℝ} (hy : y > 1) : Q.eval y ≠ 0 := by
    intro h_eval
    let z : ℂ := (Real.sqrt y : ℂ)
    have h_z_sq : z^2 = algebraMap ℝ ℂ y := by
      dsimp [z]
      have h3 : ((Real.sqrt y : ℂ) ^ 2) = (Real.sqrt y ^ 2 : ℝ) := by push_cast; rfl
      rw [h3, Real.sq_sqrt (by linarith)]
    have h_roots := hrootsQ z
    have h_eval_complex : (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 := by
      rw [h_z_sq]
      rw [h_eval_map_Q]
      rw [h_eval]
      exact RingHom.map_zero (algebraMap ℝ ℂ)
    have h_res := h_roots h_eval_complex
    have h_re : z.re = Real.sqrt y := rfl
    have h_in_Icc := h_res.2
    rw [h_re] at h_in_Icc
    have h_sqrt_gt1 : 1 < Real.sqrt y := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by linarith) hy
    linarith [h_in_Icc.1, h_in_Icc.2]
  sorry

