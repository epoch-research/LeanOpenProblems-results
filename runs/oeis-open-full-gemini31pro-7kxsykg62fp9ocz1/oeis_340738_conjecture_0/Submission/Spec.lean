import FormalConjectures.Util.ProblemImports

open Nat
open Filter

/--
A340738: Denominator of a sequence of fractions converging to $e$.
$a(1) = 1$
$a(2) = 2$
For $n > 2$:
If $n$ is odd: $a(n) = 2 a(n-1) + n a(n-2)$
If $n$ is even: $a(n) = \frac{n+2}{2} a(n-1) - a(n-2) - \frac{n-2}{2} a(n-3)$
-/
def A340738 : ℕ → ℕ
| 0 => 0 -- Sequence conventionally starts at index 1
| 1 => 1
| 2 => 2
| n + 3 =>
  let k := n + 3
  -- The recursive calls are safe since k ≥ 3.
  let a_prev_3 := A340738 (k - 3) -- a(k-3)
  let a_prev_2 := A340738 (k - 2) -- a(k-2)
  let a_prev_1 := A340738 (k - 1) -- a(k-1)

  -- k % 2 will be 0 for even k, and 1 for odd k.
  match k % 2 with
  | 0 => -- k is even, k ≥ 4
    -- a(k) = ((k+2)/2) * a(k-1) - a(k-2) - ((k-2)/2) * a(k-3)
    let c1 := (k + 2) / 2
    let c3 := (k - 2) / 2
    -- We rely on the property that the natural number recursion is well-defined on ℕ.
    c1 * a_prev_1 - a_prev_2 - c3 * a_prev_3
  | 1 => -- k is odd, k ≥ 3
    -- a(k) = 2 * a(k-1) + k * a(k-2)
    2 * a_prev_1 + k * a_prev_2
  | _ => 0 -- Should not happen

/--
A340737: Numerator of a sequence of fractions converging to $e$.
Uses the same recurrence as A340738 but starting with $b(1)=3, b(2)=5$.
-/
def A340737 : ℕ → ℕ
| 0 => 0
| 1 => 3
| 2 => 5
| n + 3 =>
  let k := n + 3
  let b_prev_3 := A340737 (k - 3)
  let b_prev_2 := A340737 (k - 2)
  let b_prev_1 := A340737 (k - 1)

  match k % 2 with
  | 0 => -- k is even, k ≥ 4
    let c1 := (k + 2) / 2
    let c3 := (k - 2) / 2
    c1 * b_prev_1 - b_prev_2 - c3 * b_prev_3
  | 1 => -- k is odd, k ≥ 3
    2 * b_prev_1 + k * b_prev_2
  | _ => 0

/-- The sequence of fractions $\frac{A340737(n)}{A340738(n)}$ as a sequence of real numbers.

Note: For $n \ge 1$, $A340738(n)$ is positive, so division by zero is not an issue
for the defined sequence of interest.
-/
noncomputable
def sequence_of_fractions (n : ℕ) : ℝ :=
  (A340737 n : ℝ) / (A340738 n : ℝ)


open Polynomial intervalIntegral Filter Topology Set Metric Real Nat

noncomputable def P_poly (k : ℕ) : ℝ[X] :=
  (X * (1 - X)) ^ k * C ((k ! : ℝ)⁻¹)


noncomputable def g_poly (k : ℕ) : ℝ[X] :=
  ((X * (1 - X)) ^ k * (X ^ 2 + C (2 * (k : ℝ) + 1) * X - C ((k : ℝ) + 1))) * C (((k + 1)! : ℝ)⁻¹)


lemma deriv_U_k (k : ℕ) :
  derivative ((X * (1 - X) : ℝ[X]) ^ k) = C (k : ℝ) * (X * (1 - X)) ^ (k - 1) * (1 - C 2 * X) := by
  rw [derivative_pow]
  have : derivative (X * (1 - X) : ℝ[X]) = 1 - C 2 * X := by
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_one, map_ofNat]; ring
  rw [this]


lemma g_poly_derivative (k : ℕ) :
  derivative (g_poly k) =
    (C (k : ℝ) * (X * (1 - X)) ^ (k - 1) * (1 - C 2 * X) * (X ^ 2 + C (2 * (k : ℝ) + 1) * X - C ((k : ℝ) + 1)) +
    (X * (1 - X)) ^ k * (C 2 * X + C (2 * (k : ℝ) + 1))) * C (((k + 1)! : ℝ)⁻¹) := by
  dsimp [g_poly]; rw [derivative_mul, derivative_mul]
  have H1 : derivative ((X * (1 - X) : ℝ[X]) ^ k) = C (k : ℝ) * (X * (1 - X)) ^ (k - 1) * (1 - C 2 * X) := deriv_U_k k
  rw [H1]
  have H2 : derivative (X ^ 2 + C (2 * (k : ℝ) + 1) * X - C ((k : ℝ) + 1)) = C 2 * X + C (2 * (k : ℝ) + 1) := by
    simp [map_ofNat]; ring
  rw [H2]
  have H3 : derivative (C (((k + 1)! : ℝ)⁻¹)) = 0 := derivative_C
  rw [H3]; ring


lemma deriv_identity_helper (K : ℝ) (Y : ℝ[X]) :
  let U : ℝ[X] := X * (1 - X)
  C K * Y * (1 - C 2 * X) * (X ^ 2 + C (2 * K + 1) * X - C (K + 1)) +
  (U * Y) * (C 2 * X + C (2 * K + 1)) =
  U ^ 2 * Y + C ((4 * K + 2) * (K + 1)) * (U * Y) - C (K * (K + 1)) * Y +
  (U * Y) * (X ^ 2 + C (2 * K + 1) * X - C (K + 1)) := by
  intro U; dsimp [U]; simp only [map_ofNat, map_one, map_mul, map_add]; ring


lemma fact_cancel_1 (k : ℕ) : (k ! : ℝ)⁻¹ * ((k + 1)! : ℝ) = (k + 1 : ℝ) := by
  have : ((k + 1)! : ℝ) = (k + 1 : ℝ) * (k ! : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring
  rw [this]; have h_pos : (k ! : ℝ) ≠ 0 := by positivity
  calc
    (k ! : ℝ)⁻¹ * ((k + 1 : ℝ) * (k ! : ℝ)) = (k + 1 : ℝ) * ((k ! : ℝ)⁻¹ * (k ! : ℝ)) := by ring
    _ = (k + 1 : ℝ) * 1 := by rw [inv_mul_cancel₀ h_pos]
    _ = (k + 1 : ℝ) := by ring


lemma fact_cancel_2 (k : ℕ) (hk : 1 ≤ k) : ((k - 1) ! : ℝ)⁻¹ * ((k + 1)! : ℝ) = (k : ℝ) * (k + 1 : ℝ) := by
  have h1 : k = k - 1 + 1 := by omega
  have : ((k + 1)! : ℝ) = (k + 1 : ℝ) * (k : ℝ) * ((k - 1) ! : ℝ) := by
    rw [Nat.factorial_succ]
    have h2 : k ! = k * (k - 1) ! := by nth_rw 1 [h1]; rw [Nat.factorial_succ]; congr 1; omega
    rw [h2]; push_cast; ring
  rw [this]; have h_pos : ((k - 1) ! : ℝ) ≠ 0 := by positivity
  calc
    ((k - 1) ! : ℝ)⁻¹ * ((k + 1 : ℝ) * (k : ℝ) * ((k - 1) ! : ℝ)) = ((k + 1 : ℝ) * (k : ℝ)) * (((k - 1) ! : ℝ)⁻¹ * ((k - 1) ! : ℝ)) := by ring
    _ = (k + 1 : ℝ) * (k : ℝ) * 1 := by rw [inv_mul_cancel₀ h_pos]
    _ = (k : ℝ) * (k + 1 : ℝ) := by ring


lemma P_poly_identity (k : ℕ) (hk : 1 ≤ k) :
  derivative (g_poly k) = P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k := by
  have H : derivative (g_poly k) * C ((k + 1)! : ℝ) = (P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k) * C ((k + 1)! : ℝ) := by
    rw [g_poly_derivative k]
    dsimp [P_poly, g_poly]
    have hk1 : (X * (1 - X) : ℝ[X]) ^ (k + 1) = (X * (1 - X)) ^ 2 * (X * (1 - X)) ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    have hk2 : (X * (1 - X) : ℝ[X]) ^ k = (X * (1 - X)) * (X * (1 - X)) ^ (k - 1) := by
      have : k = 1 + (k - 1) := by omega
      nth_rw 1 [this]; rw [pow_add, pow_one]
    rw [hk1, hk2]
    have h_cancel1 : C ((k ! : ℝ)⁻¹) * C ((k + 1)! : ℝ) = C (k + 1 : ℝ) := by rw [← C_mul, fact_cancel_1 k]
    have h_cancel2 : C (((k - 1)! : ℝ)⁻¹) * C ((k + 1)! : ℝ) = C ((k : ℝ) * (k + 1 : ℝ)) := by rw [← C_mul, fact_cancel_2 k hk]
    have h_cancel_g : C (((k + 1)! : ℝ)⁻¹) * C ((k + 1)! : ℝ) = 1 := by
      rw [← C_mul]; have : ((k + 1)! : ℝ)⁻¹ * ((k + 1)! : ℝ) = 1 := inv_mul_cancel₀ (by positivity); rw [this, C_1]
    simp only [add_mul, sub_mul, mul_add, mul_sub, mul_assoc]
    rw [h_cancel1, h_cancel2, h_cancel_g]
    simp only [map_ofNat, map_one, map_mul, map_add, mul_one]
    generalize (X * (1 - X) : ℝ[X]) ^ (k - 1) = Y; ring
  calc
    derivative (g_poly k) = derivative (g_poly k) * C ((k + 1)! : ℝ) * C (((k + 1)! : ℝ)⁻¹) := by rw [mul_assoc, ← C_mul, mul_inv_cancel₀, C_1, mul_one]; positivity
    _ = (P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k) * C ((k + 1)! : ℝ) * C (((k + 1)! : ℝ)⁻¹) := by rw [H]
    _ = P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k := by rw [mul_assoc, ← C_mul, mul_inv_cancel₀, C_1, mul_one]; positivity


lemma hasDerivAt_poly_exp (P : ℝ[X]) (x : ℝ) :
  HasDerivAt (fun x => P.eval x * exp (1 - x)) (((derivative P).eval x - P.eval x) * exp (1 - x)) x := by
  have h1 : HasDerivAt (fun x => P.eval x) ((derivative P).eval x) x := P.hasDerivAt x
  have h2 : HasDerivAt (fun x => exp (1 - x)) (- exp (1 - x)) x := by
    have hd1 : HasDerivAt (fun x : ℝ => 1) (0:ℝ) x := hasDerivAt_const x (1:ℝ)
    have hd2 : HasDerivAt (fun x : ℝ => x) (1:ℝ) x := hasDerivAt_id x
    have hd3 : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1 : ℝ) x := HasDerivAt.sub hd1 hd2
    have hd4 := HasDerivAt.exp hd3
    simpa using hd4
  have h3 := HasDerivAt.mul h1 h2
  convert h3 using 1; ring


lemma integral_poly_exp (P : ℝ[X]) :
  ∫ x in (0:ℝ)..1, ((P - derivative P).eval x) * exp (1 - x) = P.eval 0 * exp 1 - P.eval 1 := by
  have h_deriv : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun x => - (P.eval x * exp (1 - x))) (((P - derivative P).eval x) * exp (1 - x)) x := by
    intro x _
    have h1 := hasDerivAt_poly_exp P x
    have h2 := HasDerivAt.neg h1
    convert h2 using 1; simp; ring
  have h_cont : Continuous (fun x : ℝ => ((P - derivative P).eval x) * exp (1 - x)) := by
    apply Continuous.mul
    · exact (P - derivative P).continuous
    · exact continuous_exp.comp (continuous_const.sub continuous_id)
  have h_int := integral_eq_sub_of_hasDerivAt h_deriv (h_cont.intervalIntegrable _ _)
  rw [h_int]; simp; ring


noncomputable def I_k (k : ℕ) : ℝ := ∫ x in (0:ℝ)..1, (P_poly k).eval x * exp (1 - x)


lemma P_poly_cont (k : ℕ) : Continuous (fun x => (P_poly k).eval x * exp (1 - x)) := by
  apply Continuous.mul
  · exact (P_poly k).continuous
  · exact continuous_exp.comp (continuous_const.sub continuous_id)


lemma I_k_recurrence_helper (k : ℕ) (hk : 1 ≤ k) :
  I_k (k + 1) + (4 * (k : ℝ) + 2) * I_k k - I_k (k - 1) =
  ∫ x in (0:ℝ)..1, (P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1)).eval x * exp (1 - x) := by
  dsimp [I_k]
  have h_mul : (4 * (k : ℝ) + 2) * ∫ x in (0:ℝ)..1, (P_poly k).eval x * exp (1 - x) = ∫ x in (0:ℝ)..1, (4 * (k : ℝ) + 2) * ((P_poly k).eval x * exp (1 - x)) := by
    exact (intervalIntegral.integral_smul (4 * (k : ℝ) + 2) (fun x => (P_poly k).eval x * exp (1 - x))).symm
  rw [h_mul, ← intervalIntegral.integral_add, ← intervalIntegral.integral_sub]
  · congr 1; ext x; simp; ring
  · apply Continuous.intervalIntegrable; apply Continuous.add
    · exact P_poly_cont (k + 1)
    · apply Continuous.mul continuous_const (P_poly_cont k)
  · exact Continuous.intervalIntegrable (P_poly_cont (k - 1)) _ _
  · exact Continuous.intervalIntegrable (P_poly_cont (k + 1)) _ _
  · apply Continuous.intervalIntegrable; apply Continuous.mul continuous_const (P_poly_cont k)


lemma g_poly_eval_zero (k : ℕ) (hk : 1 ≤ k) : (g_poly k).eval 0 = 0 := by
  dsimp [g_poly]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_add, eval_C, eval_one]
  have : (0 * (1 - 0) : ℝ) ^ k = 0 := by rw [sub_zero, zero_mul, zero_pow]; omega
  rw [this]; ring


lemma g_poly_eval_one (k : ℕ) (hk : 1 ≤ k) : (g_poly k).eval 1 = 0 := by
  dsimp [g_poly]; simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_add, eval_C, eval_one]
  have : (1 * (1 - 1) : ℝ) ^ k = 0 := by rw [sub_self, mul_zero, zero_pow]; omega
  rw [this]; ring


lemma I_k_recurrence (k : ℕ) (hk : 1 ≤ k) :
  I_k (k + 1) + (4 * (k : ℝ) + 2) * I_k k - I_k (k - 1) = 0 := by
  rw [I_k_recurrence_helper k hk]
  have H_eq : P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) = derivative (g_poly k) - g_poly k := by
    have h1 := P_poly_identity k hk
    calc
      P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) = P_poly (k + 1) + C (4 * (k : ℝ) + 2) * P_poly k - P_poly (k - 1) + g_poly k - g_poly k := by ring
      _ = derivative (g_poly k) - g_poly k := by rw [← h1]
  rw [H_eq]
  have H_int := integral_poly_exp (- g_poly k)
  have H_eval : (- g_poly k - derivative (- g_poly k)) = derivative (g_poly k) - g_poly k := by simp; ring
  have H_eval2 : (fun x => (derivative (g_poly k) - g_poly k).eval x * exp (1 - x)) = (fun x => ((- g_poly k - derivative (- g_poly k)).eval x) * exp (1 - x)) := by ext x; congr 1; rw [H_eval]
  rw [H_eval2, H_int]
  have hz := g_poly_eval_zero k hk
  have ho := g_poly_eval_one k hk
  simp only [eval_neg]; rw [hz, ho]; ring


lemma a_odd_eval (k : ℕ) (hk : 1 ≤ k) :
  A340738 (2 * k + 1) = 2 * A340738 (2 * k) + (2 * k + 1) * A340738 (2 * k - 1) := by
  have h_eq : 2 * k + 1 = (2 * k - 2) + 3 := by omega
  nth_rw 1 [h_eq]; rw [A340738]; rw [show ((2 * k - 2) + 3) % 2 = 1 by omega]; dsimp
  have e1 : (2 * k - 2) + 2 = 2 * k := by omega
  have e2 : (2 * k - 2) + 3 = 2 * k + 1 := by omega
  have e3 : (2 * k - 2) + 3 - 2 = 2 * k - 1 := by omega
  have h1 : A340738 ((2 * k - 2) + 2) = A340738 (2 * k) := by rw [e1]
  have h2 : A340738 ((2 * k - 2) + 3 - 2) = A340738 (2 * k - 1) := by rw [e3]
  rw [h1, h2, e2]


lemma a_mono_pair (k : ℕ) (hk : 1 ≤ k) :
  1 ≤ A340738 (2 * k - 1) ∧ 
  A340738 (2 * k - 1) < A340738 (2 * k) ∧ 
  A340738 (2 * k) < A340738 (2 * k + 1) ∧
  A340738 (2 * k) + k * A340738 (2 * k - 1) ≤ (k + 1) * A340738 (2 * k + 1) := by
  induction' k, hk using Nat.le_induction with k hk ih
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · rcases ih with ⟨ih1, ih2, ih3, ih4⟩
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have h1 : 1 ≤ A340738 (2 * (k + 1) - 1) := by rw [e1]; omega
    have h2 : A340738 (2 * (k + 1) - 1) < A340738 (2 * (k + 1)) := by
      have def_2k2 : A340738 (2 * (k + 1)) = (k + 2) * A340738 (2 * k + 1) - A340738 (2 * k) - k * A340738 (2 * k - 1) := by
        have heq : 2 * (k + 1) = 2 * k - 1 + 3 := by omega
        nth_rw 1 [heq]; rw [A340738]; rw [show (2 * k - 1 + 3) % 2 = 0 by omega]; dsimp
        have c1 : (2 * k - 1 + 3 + 2) / 2 = k + 2 := by omega
        have c2 : (2 * k - 1 + 3 - 2) / 2 = k := by omega
        have r1 : A340738 (2 * k - 1 + 2) = A340738 (2 * k + 1) := by congr 1; omega
        have r2 : A340738 (2 * k - 1 + 3 - 2) = A340738 (2 * k) := by congr 1; omega
        have r3 : A340738 (2 * k - 1 + 3 - 3) = A340738 (2 * k - 1) := by congr 1
        rw [c1, c2, r1, r2, r3]
      rw [def_2k2, e1]
      have hk_z : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
      have step1 : (A340738 (2 * k) : ℤ) ≤ (A340738 (2 * k + 1) : ℤ) - 1 := by omega
      have step2 : (A340738 (2 * k - 1) : ℤ) ≤ (A340738 (2 * k + 1) : ℤ) - 2 := by omega
      have step3 : (k : ℤ) * (A340738 (2 * k - 1) : ℤ) ≤ (k : ℤ) * ((A340738 (2 * k + 1) : ℤ) - 2) := by nlinarith
      have step4 : (A340738 (2 * k) : ℤ) + (k : ℤ) * (A340738 (2 * k - 1) : ℤ) ≤ (A340738 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340738 (2 * k + 1) : ℤ) - 2) := by linarith
      have step5 : (A340738 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340738 (2 * k + 1) : ℤ) - 2) < ((k + 2 : ℕ) : ℤ) * (A340738 (2 * k + 1) : ℤ) - (A340738 (2 * k + 1) : ℤ) := by
        calc
          (A340738 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340738 (2 * k + 1) : ℤ) - 2)
            = ((k:ℤ) + 1) * (A340738 (2 * k + 1) : ℤ) - 2 * (k:ℤ) - 1 := by ring
          _ < ((k:ℤ) + 1) * (A340738 (2 * k + 1) : ℤ) := by linarith
          _ = ((k + 2 : ℕ) : ℤ) * (A340738 (2 * k + 1) : ℤ) - (A340738 (2 * k + 1) : ℤ) := by push_cast; ring
      have step6 : (A340738 (2 * k) : ℤ) + (k : ℤ) * (A340738 (2 * k - 1) : ℤ) + (A340738 (2 * k + 1) : ℤ) < ((k + 2 : ℕ) : ℤ) * (A340738 (2 * k + 1) : ℤ) := by linarith
      have step6_nat : A340738 (2 * k) + k * A340738 (2 * k - 1) + A340738 (2 * k + 1) < (k + 2) * A340738 (2 * k + 1) := by exact_mod_cast step6
      omega
    have h3 : A340738 (2 * (k + 1)) < A340738 (2 * (k + 1) + 1) := by
      have odd_eval := a_odd_eval (k + 1) (by omega)
      nlinarith
    have h4 : A340738 (2 * (k + 1)) + (k + 1) * A340738 (2 * (k + 1) - 1) ≤ (k + 2) * A340738 (2 * (k + 1) + 1) := by
      have odd_eval := a_odd_eval (k + 1) (by omega)
      have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      have e3 : 2 * (k + 1) = 2 * k + 2 := by omega
      have e4 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [e4, e2, e3] at odd_eval
      nlinarith
    exact ⟨h1, h2, h3, h4⟩


lemma b_odd_eval (k : ℕ) (hk : 1 ≤ k) :
  A340737 (2 * k + 1) = 2 * A340737 (2 * k) + (2 * k + 1) * A340737 (2 * k - 1) := by
  have h_eq : 2 * k + 1 = (2 * k - 2) + 3 := by omega
  nth_rw 1 [h_eq]; rw [A340737]; rw [show ((2 * k - 2) + 3) % 2 = 1 by omega]; dsimp
  have e1 : (2 * k - 2) + 2 = 2 * k := by omega
  have e2 : (2 * k - 2) + 3 = 2 * k + 1 := by omega
  have e3 : (2 * k - 2) + 3 - 2 = 2 * k - 1 := by omega
  have h1 : A340737 ((2 * k - 2) + 2) = A340737 (2 * k) := by rw [e1]
  have h2 : A340737 ((2 * k - 2) + 3 - 2) = A340737 (2 * k - 1) := by rw [e3]
  rw [h1, h2, e2]


lemma b_mono_pair (k : ℕ) (hk : 1 ≤ k) :
  1 ≤ A340737 (2 * k - 1) ∧ 
  A340737 (2 * k - 1) < A340737 (2 * k) ∧ 
  A340737 (2 * k) < A340737 (2 * k + 1) ∧
  A340737 (2 * k) + k * A340737 (2 * k - 1) ≤ (k + 1) * A340737 (2 * k + 1) := by
  induction' k, hk using Nat.le_induction with k hk ih
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · rcases ih with ⟨ih1, ih2, ih3, ih4⟩
    have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have h1 : 1 ≤ A340737 (2 * (k + 1) - 1) := by rw [e1]; omega
    have h2 : A340737 (2 * (k + 1) - 1) < A340737 (2 * (k + 1)) := by
      have def_2k2 : A340737 (2 * (k + 1)) = (k + 2) * A340737 (2 * k + 1) - A340737 (2 * k) - k * A340737 (2 * k - 1) := by
        have heq : 2 * (k + 1) = 2 * k - 1 + 3 := by omega
        nth_rw 1 [heq]; rw [A340737]; rw [show (2 * k - 1 + 3) % 2 = 0 by omega]; dsimp
        have c1 : (2 * k - 1 + 3 + 2) / 2 = k + 2 := by omega
        have c2 : (2 * k - 1 + 3 - 2) / 2 = k := by omega
        have r1 : A340737 (2 * k - 1 + 2) = A340737 (2 * k + 1) := by congr 1; omega
        have r2 : A340737 (2 * k - 1 + 3 - 2) = A340737 (2 * k) := by congr 1; omega
        have r3 : A340737 (2 * k - 1 + 3 - 3) = A340737 (2 * k - 1) := by congr 1
        rw [c1, c2, r1, r2, r3]
      rw [def_2k2, e1]
      have hk_z : (1:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk
      have step1 : (A340737 (2 * k) : ℤ) ≤ (A340737 (2 * k + 1) : ℤ) - 1 := by omega
      have step2 : (A340737 (2 * k - 1) : ℤ) ≤ (A340737 (2 * k + 1) : ℤ) - 2 := by omega
      have step3 : (k : ℤ) * (A340737 (2 * k - 1) : ℤ) ≤ (k : ℤ) * ((A340737 (2 * k + 1) : ℤ) - 2) := by nlinarith
      have step4 : (A340737 (2 * k) : ℤ) + (k : ℤ) * (A340737 (2 * k - 1) : ℤ) ≤ (A340737 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340737 (2 * k + 1) : ℤ) - 2) := by linarith
      have step5 : (A340737 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340737 (2 * k + 1) : ℤ) - 2) < ((k + 2 : ℕ) : ℤ) * (A340737 (2 * k + 1) : ℤ) - (A340737 (2 * k + 1) : ℤ) := by
        calc
          (A340737 (2 * k + 1) : ℤ) - 1 + (k : ℤ) * ((A340737 (2 * k + 1) : ℤ) - 2)
            = ((k:ℤ) + 1) * (A340737 (2 * k + 1) : ℤ) - 2 * (k:ℤ) - 1 := by ring
          _ < ((k:ℤ) + 1) * (A340737 (2 * k + 1) : ℤ) := by linarith
          _ = ((k + 2 : ℕ) : ℤ) * (A340737 (2 * k + 1) : ℤ) - (A340737 (2 * k + 1) : ℤ) := by push_cast; ring
      have step6 : (A340737 (2 * k) : ℤ) + (k : ℤ) * (A340737 (2 * k - 1) : ℤ) + (A340737 (2 * k + 1) : ℤ) < ((k + 2 : ℕ) : ℤ) * (A340737 (2 * k + 1) : ℤ) := by linarith
      have step6_nat : A340737 (2 * k) + k * A340737 (2 * k - 1) + A340737 (2 * k + 1) < (k + 2) * A340737 (2 * k + 1) := by exact_mod_cast step6
      omega
    have h3 : A340737 (2 * (k + 1)) < A340737 (2 * (k + 1) + 1) := by
      have odd_eval := b_odd_eval (k + 1) (by omega)
      nlinarith
    have h4 : A340737 (2 * (k + 1)) + (k + 1) * A340737 (2 * (k + 1) - 1) ≤ (k + 2) * A340737 (2 * (k + 1) + 1) := by
      nlinarith
    exact ⟨h1, h2, h3, h4⟩



lemma a_even_eval_rearranged (k : ℕ) (hk : 2 ≤ k) :
  A340738 (2 * k) + A340738 (2 * k - 2) + (k - 1) * A340738 (2 * k - 3) = (k + 1) * A340738 (2 * k - 1) := by
  have def_2k : A340738 (2 * k) = (k + 1) * A340738 (2 * k - 1) - A340738 (2 * k - 2) - (k - 1) * A340738 (2 * k - 3) := by
    have heq : 2 * k = 2 * k - 3 + 3 := by omega
    nth_rw 1 [heq]; rw [A340738]; rw [show (2 * k - 3 + 3) % 2 = 0 by omega]; dsimp
    have c1 : (2 * k - 3 + 3 + 2) / 2 = k + 1 := by omega
    have c2 : (2 * k - 3 + 3 - 2) / 2 = k - 1 := by omega
    have r1 : A340738 (2 * k - 3 + 2) = A340738 (2 * k - 1) := by congr 1; omega
    have r2 : A340738 (2 * k - 3 + 3 - 2) = A340738 (2 * k - 2) := by congr 1; omega
    have r3 : A340738 (2 * k - 3 + 3 - 3) = A340738 (2 * k - 3) := by congr 1
    rw [c1, c2, r1, r2, r3]
  have mono := a_mono_pair (k - 1) (by omega)
  have h4 := mono.2.2.2
  have h_replace : A340738 (2 * (k - 1)) + (k - 1) * A340738 (2 * (k - 1) - 1) ≤ (k - 1 + 1) * A340738 (2 * (k - 1) + 1) := h4
  have eq1 : A340738 (2 * (k - 1)) = A340738 (2 * k - 2) := by congr 1; omega
  have eq2 : A340738 (2 * (k - 1) - 1) = A340738 (2 * k - 3) := by congr 1; omega
  have eq3 : A340738 (2 * (k - 1) + 1) = A340738 (2 * k - 1) := by congr 1; omega
  have e4 : k - 1 + 1 = k := by omega
  rw [eq1, eq2, eq3, e4] at h_replace
  have h_mul : k * A340738 (2 * k - 1) + A340738 (2 * k - 1) = (k + 1) * A340738 (2 * k - 1) := by ring
  omega


lemma b_even_eval_rearranged (k : ℕ) (hk : 2 ≤ k) :
  A340737 (2 * k) + A340737 (2 * k - 2) + (k - 1) * A340737 (2 * k - 3) = (k + 1) * A340737 (2 * k - 1) := by
  have def_2k : A340737 (2 * k) = (k + 1) * A340737 (2 * k - 1) - A340737 (2 * k - 2) - (k - 1) * A340737 (2 * k - 3) := by
    have heq : 2 * k = 2 * k - 3 + 3 := by omega
    nth_rw 1 [heq]; rw [A340737]; rw [show (2 * k - 3 + 3) % 2 = 0 by omega]; dsimp
    have c1 : (2 * k - 3 + 3 + 2) / 2 = k + 1 := by omega
    have c2 : (2 * k - 3 + 3 - 2) / 2 = k - 1 := by omega
    have r1 : A340737 (2 * k - 3 + 2) = A340737 (2 * k - 1) := by congr 1; omega
    have r2 : A340737 (2 * k - 3 + 3 - 2) = A340737 (2 * k - 2) := by congr 1; omega
    have r3 : A340737 (2 * k - 3 + 3 - 3) = A340737 (2 * k - 3) := by congr 1
    rw [c1, c2, r1, r2, r3]
  have mono := b_mono_pair (k - 1) (by omega)
  have h4 := mono.2.2.2
  have h_replace : A340737 (2 * (k - 1)) + (k - 1) * A340737 (2 * (k - 1) - 1) ≤ (k - 1 + 1) * A340737 (2 * (k - 1) + 1) := h4
  have eq1 : A340737 (2 * (k - 1)) = A340737 (2 * k - 2) := by congr 1; omega
  have eq2 : A340737 (2 * (k - 1) - 1) = A340737 (2 * k - 3) := by congr 1; omega
  have eq3 : A340737 (2 * (k - 1) + 1) = A340737 (2 * k - 1) := by congr 1; omega
  have e4 : k - 1 + 1 = k := by omega
  rw [eq1, eq2, eq3, e4] at h_replace
  have h_mul : k * A340737 (2 * k - 1) + A340737 (2 * k - 1) = (k + 1) * A340737 (2 * k - 1) := by ring
  omega



lemma a_odd_pure_recurrence_int (k : ℕ) (hk : 2 ≤ k) :
  (A340738 (2 * k + 1) : ℝ) = (4 * (k : ℝ) + 2) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ) := by
  have h1_nat := a_odd_eval k (by omega)
  have hk1 : 1 ≤ k := by omega
  have h1 : (A340738 (2 * k + 1) : ℝ) = 2 * (A340738 (2 * k) : ℝ) + (2 * (k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by 
    calc
      (A340738 (2 * k + 1) : ℝ) = (((2 * A340738 (2 * k) + (2 * k + 1) * A340738 (2 * k - 1)) : ℕ) : ℝ) := by rw [h1_nat]
      _ = 2 * (A340738 (2 * k) : ℝ) + (2 * (k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by push_cast [hk1]; ring
  have h2_nat := a_even_eval_rearranged k (by omega)
  have h2 : (A340738 (2 * k) : ℝ) + (A340738 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ) = ((k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by 
    calc
      (A340738 (2 * k) : ℝ) + (A340738 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ)
        = (((A340738 (2 * k) + A340738 (2 * k - 2) + (k - 1) * A340738 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk1]; ring
      _ = (((k + 1) * A340738 (2 * k - 1) : ℕ) : ℝ) := by rw [h2_nat]
      _ = ((k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by push_cast; ring
  have h3 : 2 * (A340738 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ) = (A340738 (2 * k - 1) : ℝ) := by
    have this_val := a_odd_eval (k - 1) (by omega)
    have e1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
    have e2 : 2 * (k - 1) = 2 * k - 2 := by omega
    have e3 : 2 * k - 2 - 1 = 2 * k - 3 := by omega
    rw [e1, e2] at this_val
    rw [e3] at this_val
    have hk2 : 1 ≤ 2 * k := by omega
    calc
      2 * (A340738 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ)
        = (((2 * A340738 (2 * k - 2) + (2 * k - 1) * A340738 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk2]; ring
      _ = (A340738 (2 * k - 1) : ℝ) := by rw [← this_val]
  linarith


lemma b_odd_pure_recurrence_int (k : ℕ) (hk : 2 ≤ k) :
  (A340737 (2 * k + 1) : ℝ) = (4 * (k : ℝ) + 2) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) := by
  have h1_nat := b_odd_eval k (by omega)
  have hk1 : 1 ≤ k := by omega
  have h1 : (A340737 (2 * k + 1) : ℝ) = 2 * (A340737 (2 * k) : ℝ) + (2 * (k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by 
    calc
      (A340737 (2 * k + 1) : ℝ) = (((2 * A340737 (2 * k) + (2 * k + 1) * A340737 (2 * k - 1)) : ℕ) : ℝ) := by rw [h1_nat]
      _ = 2 * (A340737 (2 * k) : ℝ) + (2 * (k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by push_cast [hk1]; ring
  have h2_nat := b_even_eval_rearranged k (by omega)
  have h2 : (A340737 (2 * k) : ℝ) + (A340737 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ) = ((k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by 
    calc
      (A340737 (2 * k) : ℝ) + (A340737 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ)
        = (((A340737 (2 * k) + A340737 (2 * k - 2) + (k - 1) * A340737 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk1]; ring
      _ = (((k + 1) * A340737 (2 * k - 1) : ℕ) : ℝ) := by rw [h2_nat]
      _ = ((k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by push_cast; ring
  have h3 : 2 * (A340737 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ) = (A340737 (2 * k - 1) : ℝ) := by
    have this_val := b_odd_eval (k - 1) (by omega)
    have e1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
    have e2 : 2 * (k - 1) = 2 * k - 2 := by omega
    have e3 : 2 * k - 2 - 1 = 2 * k - 3 := by omega
    rw [e1, e2] at this_val
    rw [e3] at this_val
    have hk2 : 1 ≤ 2 * k := by omega
    calc
      2 * (A340737 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ)
        = (((2 * A340737 (2 * k - 2) + (2 * k - 1) * A340737 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk2]; ring
      _ = (A340737 (2 * k - 1) : ℝ) := by rw [← this_val]
  linarith


lemma a_even_pure_recurrence_int (k : ℕ) (hk : 2 ≤ k) :
  2 * (A340738 (2 * k) : ℝ) = (2 * (k : ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ) := by
  have hk1 : 1 ≤ k := by omega
  have h2_nat := a_even_eval_rearranged k hk
  have h2 : (A340738 (2 * k) : ℝ) + (A340738 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ) = ((k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by 
    calc
      (A340738 (2 * k) : ℝ) + (A340738 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ)
        = (((A340738 (2 * k) + A340738 (2 * k - 2) + (k - 1) * A340738 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk1]; ring
      _ = (((k + 1) * A340738 (2 * k - 1) : ℕ) : ℝ) := by rw [h2_nat]
      _ = ((k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) := by push_cast; ring
  have h3 : 2 * (A340738 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ) = (A340738 (2 * k - 1) : ℝ) := by
    have this_val := a_odd_eval (k - 1) (by omega)
    have e1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
    have e2 : 2 * (k - 1) = 2 * k - 2 := by omega
    have e3 : 2 * k - 2 - 1 = 2 * k - 3 := by omega
    rw [e1, e2] at this_val
    rw [e3] at this_val
    have hk2 : 1 ≤ 2 * k := by omega
    calc
      2 * (A340738 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340738 (2 * k - 3) : ℝ)
        = (((2 * A340738 (2 * k - 2) + (2 * k - 1) * A340738 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk2]; ring
      _ = (A340738 (2 * k - 1) : ℝ) := by rw [← this_val]
  linarith


lemma b_even_pure_recurrence_int (k : ℕ) (hk : 2 ≤ k) :
  2 * (A340737 (2 * k) : ℝ) = (2 * (k : ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) := by
  have hk1 : 1 ≤ k := by omega
  have h2_nat := b_even_eval_rearranged k hk
  have h2 : (A340737 (2 * k) : ℝ) + (A340737 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ) = ((k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by 
    calc
      (A340737 (2 * k) : ℝ) + (A340737 (2 * k - 2) : ℝ) + ((k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ)
        = (((A340737 (2 * k) + A340737 (2 * k - 2) + (k - 1) * A340737 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk1]; ring
      _ = (((k + 1) * A340737 (2 * k - 1) : ℕ) : ℝ) := by rw [h2_nat]
      _ = ((k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) := by push_cast; ring
  have h3 : 2 * (A340737 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ) = (A340737 (2 * k - 1) : ℝ) := by
    have this_val := b_odd_eval (k - 1) (by omega)
    have e1 : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
    have e2 : 2 * (k - 1) = 2 * k - 2 := by omega
    have e3 : 2 * k - 2 - 1 = 2 * k - 3 := by omega
    rw [e1, e2] at this_val
    rw [e3] at this_val
    have hk2 : 1 ≤ 2 * k := by omega
    calc
      2 * (A340737 (2 * k - 2) : ℝ) + (2 * (k:ℝ) - 1) * (A340737 (2 * k - 3) : ℝ)
        = (((2 * A340737 (2 * k - 2) + (2 * k - 1) * A340737 (2 * k - 3)) : ℕ) : ℝ) := by push_cast [hk2]; ring
      _ = (A340737 (2 * k - 1) : ℝ) := by rw [← this_val]
  linarith


noncomputable def J (n : ℕ) : ℝ := (A340737 n : ℝ) - (A340738 n : ℝ) * exp 1


lemma J_1 : J 1 = 3 - exp 1 := by
  dsimp [J]
  have h1 : A340737 1 = 3 := rfl
  have h2 : A340738 1 = 1 := rfl
  rw [h1, h2]; push_cast; ring


lemma J_3 : J 3 = 19 - 7 * exp 1 := by
  dsimp [J]
  have h1 : A340737 3 = 19 := rfl
  have h2 : A340738 3 = 7 := rfl
  rw [h1, h2]; push_cast; ring


lemma I_1_val : I_k 1 = 3 - exp 1 := by
  have H_int := integral_poly_exp (- X^2 - X - 1 : ℝ[X])
  have H_eq : ∀ x : ℝ, (P_poly 1).eval x * exp (1 - x) = ((- X^2 - X - (1:ℝ[X]) - derivative (- X^2 - X - 1)).eval x) * exp (1 - x) := by
    intro x
    congr 1
    dsimp [P_poly]
    simp
    ring
  have hint_eq : (∫ x in (0:ℝ)..1, (P_poly 1).eval x * exp (1-x)) = ∫ x in (0:ℝ)..1, ((- X^2 - X - (1:ℝ[X]) - derivative (- X^2 - X - 1)).eval x) * exp (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact H_eq x
  have h_ik : I_k 1 = ∫ x in (0:ℝ)..1, (P_poly 1).eval x * exp (1 - x) := rfl
  rw [h_ik, hint_eq, H_int]
  have hz : (- X^2 - X - (1:ℝ[X])).eval 0 = -1 := by simp
  have ho : (- X^2 - X - (1:ℝ[X])).eval 1 = -3 := by simp; norm_num
  rw [hz, ho]
  ring


lemma I_2_val : I_k 2 = 7 * exp 1 - 19 := by
  let Q : ℝ[X] := C (1/2) * X^4 + X^3 + C (7/2) * X^2 + C 7 * X + C 7
  have H_int := integral_poly_exp Q
  have H_eq : ∀ x : ℝ, (P_poly 2).eval x * exp (1 - x) = ((Q - derivative Q).eval x) * exp (1 - x) := by
    intro x
    congr 1
    dsimp [P_poly, Q]
    simp
    ring
  have hint_eq : (∫ x in (0:ℝ)..1, (P_poly 2).eval x * exp (1-x)) = ∫ x in (0:ℝ)..1, ((Q - derivative Q).eval x) * exp (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact H_eq x
  have h_ik : I_k 2 = ∫ x in (0:ℝ)..1, (P_poly 2).eval x * exp (1 - x) := rfl
  rw [h_ik, hint_eq, H_int]
  have hz : Q.eval 0 = 7 := by dsimp [Q]; simp
  have ho : Q.eval 1 = 19 := by dsimp [Q]; simp; norm_num
  rw [hz, ho]


lemma J_odd_recurrence (k : ℕ) (hk : 2 ≤ k) :
  J (2 * k + 1) = (4 * (k : ℝ) + 2) * J (2 * k - 1) + J (2 * k - 3) := by
  dsimp [J]
  have ha := a_odd_pure_recurrence_int k hk
  have hb := b_odd_pure_recurrence_int k hk
  calc
    (A340737 (2 * k + 1) : ℝ) - (A340738 (2 * k + 1) : ℝ) * exp 1
      = (4 * (k:ℝ) + 2) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) -
        ((4 * (k:ℝ) + 2) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ)) * exp 1 := by rw [ha, hb]
    _ = (4 * (k:ℝ) + 2) * ((A340737 (2 * k - 1) : ℝ) - (A340738 (2 * k - 1) : ℝ) * exp 1) +
        ((A340737 (2 * k - 3) : ℝ) - (A340738 (2 * k - 3) : ℝ) * exp 1) := by ring


lemma J_even_recurrence (k : ℕ) (hk : 2 ≤ k) :
  2 * J (2 * k) = (2 * (k : ℝ) + 1) * J (2 * k - 1) + J (2 * k - 3) := by
  dsimp [J]
  have ha := a_even_pure_recurrence_int k hk
  have hb := b_even_pure_recurrence_int k hk
  have h_b_eq : 2 * (A340737 (2 * k) : ℝ) = (2 * (k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) := hb
  have h_a_eq : 2 * (A340738 (2 * k) : ℝ) = (2 * (k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ) := ha
  calc
    2 * ((A340737 (2 * k) : ℝ) - (A340738 (2 * k) : ℝ) * exp 1)
      = 2 * (A340737 (2 * k) : ℝ) - 2 * (A340738 (2 * k) : ℝ) * exp 1 := by ring
    _ = (2 * (k:ℝ) + 1) * (A340737 (2 * k - 1) : ℝ) + (A340737 (2 * k - 3) : ℝ) -
        ((2 * (k:ℝ) + 1) * (A340738 (2 * k - 1) : ℝ) + (A340738 (2 * k - 3) : ℝ)) * exp 1 := by rw [h_b_eq, h_a_eq]
    _ = (2 * (k:ℝ) + 1) * ((A340737 (2 * k - 1) : ℝ) - (A340738 (2 * k - 1) : ℝ) * exp 1) +
        ((A340737 (2 * k - 3) : ℝ) - (A340738 (2 * k - 3) : ℝ) * exp 1) := by ring


lemma J_odd_eq_I (k : ℕ) : J (2 * k + 1) = (-1 : ℝ)^k * I_k (k + 1) := by
  induction' k using Nat.strong_induction_on with k ih
  obtain rfl | hk1 := Nat.eq_zero_or_pos k
  · -- k = 0
    simp [J_1, I_1_val]
  · have hk1_le : 1 ≤ k := hk1
    obtain rfl | hk2 := eq_or_lt_of_le hk1_le
    · -- k = 1
      have hz : (-1 : ℝ)^1 = -1 := by norm_num
      rw [hz, J_3, I_2_val]
      ring
    · -- k >= 2
      have h_rec := J_odd_recurrence k hk2
      have ih1 := ih (k - 1) (by omega)
      have ih2 := ih (k - 2) (by omega)
      have eq1 : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
      have eq2 : 2 * k - 3 = 2 * (k - 2) + 1 := by omega
      rw [eq1] at h_rec; rw [eq2] at h_rec
      rw [ih1, ih2] at h_rec
      have h_I_rec := I_k_recurrence (k) (by omega)
      have eq_I : I_k (k + 1) = - (4 * (k:ℝ) + 2) * I_k k + I_k (k - 1) := by linarith
      have hk_1 : (-1 : ℝ)^(k - 1) = - (-1 : ℝ)^k := by
        have : k = k - 1 + 1 := by omega
        nth_rw 2 [this]
        rw [pow_add, pow_one]
        ring
      have hk_2 : (-1 : ℝ)^(k - 2) = (-1 : ℝ)^k := by
        have : k = k - 2 + 2 := by omega
        nth_rw 2 [this]
        rw [pow_add, sq]
        ring
      have eq3 : k - 1 + 1 = k := by omega
      have eq4 : k - 2 + 1 = k - 1 := by omega
      rw [eq3] at h_rec
      rw [eq4] at h_rec
      rw [hk_1, hk_2] at h_rec
      rw [eq_I]
      linarith


lemma I_k_nonneg (k : ℕ) : 0 ≤ I_k k := by
  dsimp [I_k]
  apply intervalIntegral.integral_nonneg
  · norm_num
  · intro x hx
    dsimp [P_poly]
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
    have h1 : 0 ≤ x := hx.1
    have h2 : x ≤ 1 := hx.2
    have h3 : 0 ≤ 1 - x := by linarith
    have hp1 : 0 ≤ x * (1 - x) := by positivity
    have hp2 : 0 ≤ (x * (1 - x)) ^ k := pow_nonneg hp1 k
    have h_exp : 0 ≤ exp (1 - x) := exp_pos (1 - x) |>.le
    have h_fact : 0 ≤ ((k.factorial : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg k.factorial)
    positivity


lemma I_k_le (k : ℕ) : I_k k ≤ exp 1 * ((k.factorial : ℝ)⁻¹) := by
  have H : I_k k ≤ ∫ x in (0:ℝ)..1, exp 1 * ((k.factorial : ℝ)⁻¹) := by
    dsimp [I_k]
    apply intervalIntegral.integral_mono_on
    · norm_num
    · exact (P_poly_cont k).intervalIntegrable 0 1
    · exact continuous_const.intervalIntegrable 0 1
    · intro x hx
      dsimp [P_poly]
      simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C]
      have h1 : 0 ≤ x := hx.1
      have h2 : x ≤ 1 := hx.2
      have h3 : 0 ≤ 1 - x := by linarith
      have hp1 : 0 ≤ x * (1 - x) := by positivity
      have hp2 : x * (1 - x) ≤ 1 := by
        calc
          x * (1 - x) = x - x^2 := by ring
          _ ≤ x := by
            have : 0 ≤ x^2 := by positivity
            linarith
          _ ≤ 1 := h2
      have hp3 : (x * (1 - x)) ^ k ≤ 1 ^ k := by
        gcongr
      simp at hp3
      have h_exp : exp (1 - x) ≤ exp 1 := by
        apply exp_le_exp.mpr
        linarith
      have h_fact : 0 ≤ ((k.factorial : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg k.factorial)
      have : ((x * (1 - x)) ^ k * (k.factorial : ℝ)⁻¹) * exp (1 - x) ≤ (1 * (k.factorial : ℝ)⁻¹) * exp 1 := by
        gcongr
      calc
        ((x * (1 - x)) ^ k * (k.factorial : ℝ)⁻¹) * exp (1 - x)
          ≤ (1 * (k.factorial : ℝ)⁻¹) * exp 1 := this
        _ = exp 1 * (k.factorial : ℝ)⁻¹ := by ring
  have h_int : ∫ x in (0:ℝ)..1, exp 1 * ((k.factorial : ℝ)⁻¹) = exp 1 * ((k.factorial : ℝ)⁻¹) := by
    simp
  rw [h_int] at H
  exact H


lemma I_k_tendsto_zero : Tendsto I_k atTop (nhds 0) := by
  have h1 : Tendsto (fun k : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have h2 : Tendsto (fun k : ℕ => exp 1 * ((k.factorial : ℝ)⁻¹)) atTop (nhds 0) := by
    have ht : Tendsto (fun k : ℕ => ((k.factorial : ℝ)⁻¹)) atTop (nhds 0) := by
      have H := FloorSemiring.tendsto_pow_div_factorial_atTop (1 : ℝ)
      simp only [one_pow, one_div] at H
      exact H
    have H2 := Tendsto.const_mul (exp 1) ht
    have hc : exp 1 * 0 = 0 := mul_zero (exp 1)
    rw [hc] at H2
    exact H2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2
  · intro k
    exact I_k_nonneg k
  · intro k
    exact I_k_le k


lemma J_odd_tendsto_zero : Tendsto (fun k => J (2 * k + 1)) atTop (nhds 0) := by
  have ht : Tendsto (fun k => (-1 : ℝ) ^ k * I_k (k + 1)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have H : (fun k => ‖(-1 : ℝ) ^ k * I_k (k + 1)‖) = (fun k => ‖I_k (k + 1)‖) := by
      ext k
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [H]
    apply tendsto_zero_iff_norm_tendsto_zero.mp
    have H2 : Tendsto (fun k => I_k (k + 1)) atTop (nhds 0) := by
      exact I_k_tendsto_zero.comp (tendsto_add_atTop_nat 1)
    exact H2
  have eq : (fun k => J (2 * k + 1)) = (fun k => (-1 : ℝ) ^ k * I_k (k + 1)) := by
    ext k
    exact J_odd_eq_I k
  rw [eq]
  exact ht


lemma k_div_fact_tendsto_zero : Tendsto (fun k : ℕ => (k : ℝ) * ((k.factorial : ℝ)⁻¹)) atTop (nhds 0) := by
  have H1 : (fun k : ℕ => (k : ℝ) * ((k.factorial : ℝ)⁻¹)) =ᶠ[atTop] (fun k : ℕ => (((k - 1).factorial : ℝ)⁻¹)) := by
    apply eventually_atTop.mpr
    use 1
    intro k hk
    have eq1 : k.factorial = k * (k - 1).factorial := Nat.mul_factorial_pred (by omega) |>.symm
    dsimp
    have eq2 : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by exact_mod_cast eq1
    rw [eq2]
    rw [mul_inv]
    have h_k_ne_zero : (k : ℝ) ≠ 0 := by
      have : (k:ℝ) ≥ 1 := by exact_mod_cast hk
      linarith
    calc
      (k : ℝ) * ((k : ℝ)⁻¹ * ((k - 1).factorial : ℝ)⁻¹) = ((k : ℝ) * (k : ℝ)⁻¹) * ((k - 1).factorial : ℝ)⁻¹ := by ring
      _ = 1 * ((k - 1).factorial : ℝ)⁻¹ := by rw [mul_inv_cancel₀ h_k_ne_zero]
      _ = ((k - 1).factorial : ℝ)⁻¹ := by ring
  have ht : Tendsto (fun k : ℕ => (((k - 1).factorial : ℝ)⁻¹)) atTop (nhds 0) := by
    have H := FloorSemiring.tendsto_pow_div_factorial_atTop (1 : ℝ)
    simp only [one_pow, one_div] at H
    have H_sub : Tendsto (fun k : ℕ => k - 1) atTop atTop := tendsto_sub_atTop_nat 1
    exact H.comp H_sub
  exact Tendsto.congr' H1.symm ht


lemma k_I_k_tendsto_zero : Tendsto (fun k : ℕ => (k : ℝ) * I_k k) atTop (nhds 0) := by
  have H_le : ∀ k : ℕ, 0 ≤ (k : ℝ) * I_k k := by
    intro k
    have h1 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have h2 : 0 ≤ I_k k := I_k_nonneg k
    positivity
  have H_bound : ∀ k : ℕ, (k : ℝ) * I_k k ≤ (exp 1) * ((k : ℝ) * ((k.factorial : ℝ)⁻¹)) := by
    intro k
    have h_ik_le : I_k k ≤ exp 1 * ((k.factorial : ℝ)⁻¹) := I_k_le k
    have h_k_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    calc
      (k : ℝ) * I_k k ≤ (k : ℝ) * (exp 1 * ((k.factorial : ℝ)⁻¹)) := mul_le_mul_of_nonneg_left h_ik_le h_k_nonneg
      _ = (exp 1) * ((k : ℝ) * ((k.factorial : ℝ)⁻¹)) := by ring
  have h1 : Tendsto (fun k : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have h2 : Tendsto (fun k : ℕ => (exp 1) * ((k : ℝ) * ((k.factorial : ℝ)⁻¹))) atTop (nhds 0) := by
    have ht := k_div_fact_tendsto_zero
    have H2 := Tendsto.const_mul (exp 1) ht
    have hc : exp 1 * 0 = 0 := mul_zero (exp 1)
    rw [hc] at H2
    exact H2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 H_le H_bound


lemma J_odd_term_tendsto_zero : Tendsto (fun k : ℕ => (2 * (k:ℝ) + 1) * J (2 * k - 1)) atTop (nhds 0) := by
  have eq1 : (fun k : ℕ => (2 * (k:ℝ) + 1) * J (2 * k - 1)) =ᶠ[atTop] (fun k : ℕ => (2 * (k:ℝ) + 1) * ((-1 : ℝ) ^ (k - 1) * I_k k)) := by
    apply eventually_atTop.mpr
    use 1
    intro k hk
    dsimp
    have eq_idx : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
    rw [eq_idx, J_odd_eq_I (k - 1)]
    congr 1
    have eq_k : k - 1 + 1 = k := by omega
    rw [eq_k]
  have H2 : Tendsto (fun k : ℕ => (2 * (k:ℝ) + 1) * ((-1 : ℝ) ^ (k - 1) * I_k k)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have eq_norm : (fun k : ℕ => ‖(2 * (k:ℝ) + 1) * ((-1 : ℝ) ^ (k - 1) * I_k k)‖) = (fun k : ℕ => (2 * (k:ℝ) + 1) * ‖I_k k‖) := by
      ext k
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      have : 0 ≤ 2 * (k:ℝ) + 1 := by positivity
      rw [norm_of_nonneg this]
    rw [eq_norm]
    have eq_split : (fun k : ℕ => (2 * (k:ℝ) + 1) * ‖I_k k‖) = (fun k : ℕ => 2 * ((k:ℝ) * I_k k) + I_k k) := by
      ext k
      have : 0 ≤ I_k k := I_k_nonneg k
      rw [norm_of_nonneg this]
      ring
    rw [eq_split]
    have t1 : Tendsto (fun k : ℕ => 2 * ((k:ℝ) * I_k k)) atTop (nhds 0) := by
      have h := Tendsto.const_mul 2 k_I_k_tendsto_zero
      rw [mul_zero] at h
      exact h
    have t2 : Tendsto (fun k : ℕ => I_k k) atTop (nhds 0) := I_k_tendsto_zero
    have h_add := Tendsto.add t1 t2
    rw [add_zero] at h_add
    exact h_add
  exact Tendsto.congr' eq1.symm H2



lemma J_even_tendsto_zero : Tendsto (fun k : ℕ => J (2 * k)) atTop (nhds 0) := by
  have H_eq : (fun k : ℕ => J (2 * k)) =ᶠ[atTop] (fun k : ℕ => (1/2 : ℝ) * ((2 * (k:ℝ) + 1) * J (2 * k - 1) + J (2 * k - 3))) := by
    apply eventually_atTop.mpr
    use 2
    intro k hk
    have H_rec := J_even_recurrence k hk
    linarith
  have ht1 := J_odd_term_tendsto_zero
  have ht2 : Tendsto (fun k : ℕ => J (2 * k - 3)) atTop (nhds 0) := by
    have eq : (fun k : ℕ => J (2 * k - 3)) =ᶠ[atTop] (fun k : ℕ => J (2 * (k - 2) + 1)) := by
      apply eventually_atTop.mpr
      use 2
      intro k hk
      dsimp
      congr 1
      omega
    have H_sub : Tendsto (fun k : ℕ => J (2 * (k - 2) + 1)) atTop (nhds 0) := by
      have h_sub : Tendsto (fun k : ℕ => k - 2) atTop atTop := tendsto_sub_atTop_nat 2
      exact J_odd_tendsto_zero.comp h_sub
    exact Tendsto.congr' eq.symm H_sub
  have ht_add := Tendsto.add ht1 ht2
  rw [add_zero] at ht_add
  have ht_mul := Tendsto.const_mul (1/2 : ℝ) ht_add
  rw [mul_zero] at ht_mul
  exact Tendsto.congr' H_eq.symm ht_mul


lemma J_tendsto_zero : Tendsto (fun n : ℕ => J n) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have h_even := Metric.tendsto_atTop.mp J_even_tendsto_zero ε hε
  have h_odd := Metric.tendsto_atTop.mp J_odd_tendsto_zero ε hε
  rcases h_even with ⟨N1, hN1⟩
  rcases h_odd with ⟨N2, hN2⟩
  use max (2 * N1) (2 * N2 + 1)
  intro n hn
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : n = 2 * k := by omega
    rw [hk2] at hn ⊢
    have : N1 ≤ k := by omega
    exact hN1 k this
  · have hk2 : n = 2 * k + 1 := by omega
    rw [hk2] at hn ⊢
    have : N2 ≤ k := by omega
    exact hN2 k this


lemma a_pos (n : ℕ) (hn : 1 ≤ n) : (1 : ℝ) ≤ (A340738 n : ℝ) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : n = 2 * k := by omega
    have hk_pos : 1 ≤ k := by omega
    have h_mono := a_mono_pair k hk_pos
    have h1 : 1 ≤ A340738 (2 * k - 1) := h_mono.1
    have h3 : 1 ≤ A340738 (2 * k) := by omega
    rw [hk2]
    exact_mod_cast h3
  · have hk2 : n = 2 * k + 1 := by omega
    obtain rfl | hk_pos2 := Nat.eq_zero_or_pos k
    · have eq1 : n = 1 := by omega
      rw [eq1]
      have : A340738 1 = 1 := rfl
      rw [this]
      norm_num
    · have h_mono := a_mono_pair (k + 1) (by omega)
      have h1 : 1 ≤ A340738 (2 * (k + 1) - 1) := h_mono.1
      have eq2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [eq2] at h1
      rw [hk2]
      exact_mod_cast h1


lemma sequence_of_fractions_converges :
  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) := by
  have H_eq : (fun n : ℕ => sequence_of_fractions n - exp 1) =ᶠ[atTop] (fun n : ℕ => J n * ((A340738 n : ℝ)⁻¹)) := by
    apply eventually_atTop.mpr
    use 1
    intro n hn
    dsimp [sequence_of_fractions, J]
    have ha := a_pos n hn
    have ha_ne : (A340738 n : ℝ) ≠ 0 := by linarith
    calc
      (A340737 n : ℝ) / (A340738 n : ℝ) - exp 1
        = (A340737 n : ℝ) * (A340738 n : ℝ)⁻¹ - exp 1 * (A340738 n : ℝ) * (A340738 n : ℝ)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ ha_ne, mul_one]
          ring
      _ = ((A340737 n : ℝ) - (A340738 n : ℝ) * exp 1) * (A340738 n : ℝ)⁻¹ := by ring
  have H_zero : Tendsto (fun n : ℕ => J n * ((A340738 n : ℝ)⁻¹)) atTop (nhds 0) := by
    have h_j := J_tendsto_zero
    apply squeeze_zero_norm (a := fun n => ‖J n‖)
    · intro n
      have h_norm_inv : ‖((A340738 n : ℝ)⁻¹)‖ ≤ 1 := by
        by_cases hn : 1 ≤ n
        · have ha := a_pos n hn
          have ha_pos : 0 < (A340738 n : ℝ) := by linarith
          have H_inv : ((A340738 n : ℝ)⁻¹) ≤ 1 := (inv_le_one₀ ha_pos).mpr ha
          have H_pos : 0 ≤ ((A340738 n : ℝ)⁻¹) := inv_nonneg.mpr (by linarith)
          rw [norm_of_nonneg H_pos]
          exact H_inv
        · have h0 : n = 0 := by omega
          rw [h0]
          have : A340738 0 = 0 := rfl
          rw [this]
          norm_num
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) h_norm_inv
    · exact tendsto_zero_iff_norm_tendsto_zero.mp h_j
  have H_final : Tendsto (fun n : ℕ => sequence_of_fractions n - exp 1) atTop (nhds 0) := Tendsto.congr' H_eq.symm H_zero
  have H_add := Tendsto.add_const (exp 1) H_final
  simp at H_add
  exact H_add


/-- oeis_340738_conjecture_0: "The convergence is conjectured."
Formally, the sequence of fractions $A340737(n) / A340738(n)$ converges to $e$.
-/
theorem oeis_340738_conjecture_0 :
  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) := by
  exact sequence_of_fractions_converges


theorem oeis_340738_conjecture_0.disproof : ¬ (type_of% @oeis_340738_conjecture_0) := sorry


















