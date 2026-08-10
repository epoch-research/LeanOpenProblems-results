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

lemma deriv_exp_pow_pow (r s : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => Real.exp y * y^r * (1-y)^s) x =
    Real.exp x * x^r * (1-x)^s
      + Real.exp x * ((r:ℝ) * x^(r-1) * (1-x)^s
      - ((s:ℝ) * x^r * (1-x)^(s-1))) := by
  have houter : deriv (fun y : ℝ => Real.exp y * y^r * (1-y)^s) x =
      deriv (fun y : ℝ => Real.exp y * y^r) x * (1-x)^s + (Real.exp x * x^r) * deriv (fun y : ℝ => (1-y)^s) x :=
    deriv_mul (c := fun y : ℝ => Real.exp y * y^r) (d := fun y : ℝ => (1-y)^s) (by fun_prop) (by fun_prop)
  have hinner : deriv (fun y : ℝ => Real.exp y * y^r) x = deriv (fun y : ℝ => Real.exp y) x * x^r + Real.exp x * deriv (fun y : ℝ => y^r) x :=
    deriv_mul (c := fun y : ℝ => Real.exp y) (d := fun y : ℝ => y^r) (by fun_prop) (by fun_prop)
  have hexp : deriv (fun y : ℝ => Real.exp y) x = Real.exp x := by
    simpa using congrFun Real.deriv_exp x
  have hxpow : deriv (fun y : ℝ => y^r) x = (r:ℝ) * x^(r-1) := by
    simpa using (deriv_pow (f := fun y : ℝ => y) (x := x) (by fun_prop) r)
  have hone : deriv (fun y : ℝ => 1-y) x = -1 := by
    rw [deriv_const_sub, deriv_id'']
  have hcpow : deriv (fun y : ℝ => (1-y)^s) x = (s:ℝ) * (1-x)^(s-1) * (-1) := by
    calc deriv (fun y : ℝ => (1-y)^s) x
      = (s:ℝ) * (1-x)^(s-1) * deriv (fun y : ℝ => 1-y) x := by
          simpa using (deriv_pow (f := fun y : ℝ => 1-y) (x := x) (by fun_prop) s)
      _ = (s:ℝ) * (1-x)^(s-1) * (-1) := by rw [hone]
  rw [houter, hinner, hexp, hxpow, hcpow]
  ring
open Nat Filter
open scoped Interval
noncomputable def J (a b : ℕ) : ℝ := ∫ x in (0:ℝ)..1, Real.exp x * x^a * (1-x)^b

lemma J_deriv_id (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    J r s + (r:ℝ) * J (r-1) s - (s:ℝ) * J r (s-1) = 0 := by
  have h0 : (∫ x in (0:ℝ)..1, deriv (fun y : ℝ => Real.exp y * y^r * (1-y)^s) x) = 0 := by
    have hderiv : ∀ x ∈ [[(0:ℝ), 1]], DifferentiableAt ℝ (fun y : ℝ => Real.exp y * y^r * (1-y)^s) x := by
      intro x hx; fun_prop
    have hint : IntervalIntegrable (deriv (fun y : ℝ => Real.exp y * y^r * (1-y)^s)) MeasureTheory.volume (0:ℝ) 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_deriv_eq_sub hderiv hint]
    have hr0 : r ≠ 0 := by omega
    have hs0 : s ≠ 0 := by omega
    simp [hr0, hs0]
  have hderivint :
      (∫ x in (0:ℝ)..1, (Real.exp x * x^r * (1-x)^s
      + Real.exp x * ((r:ℝ) * x^(r-1) * (1-x)^s
      - ((s:ℝ) * x^r * (1-x)^(s-1))))) = 0 := by
    apply (intervalIntegral.integral_congr ?_).trans h0
    intro x hx
    symm
    exact deriv_exp_pow_pow r s x
  have hlin :
      (∫ x in (0:ℝ)..1, (Real.exp x * x^r * (1-x)^s
      + Real.exp x * ((r:ℝ) * x^(r-1) * (1-x)^s
      - ((s:ℝ) * x^r * (1-x)^(s-1))))) =
      J r s + (r:ℝ) * J (r-1) s - (s:ℝ) * J r (s-1) := by
    calc
      (∫ x in (0:ℝ)..1, (Real.exp x * x^r * (1-x)^s
      + Real.exp x * ((r:ℝ) * x^(r-1) * (1-x)^s
      - ((s:ℝ) * x^r * (1-x)^(s-1)))))
        = (∫ x in (0:ℝ)..1, (Real.exp x * x^r * (1-x)^s
            + ((r:ℝ) * (Real.exp x * x^(r-1) * (1-x)^s)
              - (s:ℝ) * (Real.exp x * x^r * (1-x)^(s-1))))) := by
              apply intervalIntegral.integral_congr
              intro x hx
              ring
      _ = J r s + (r:ℝ) * J (r-1) s - (s:ℝ) * J r (s-1) := by
              simp only [J]
              rw [intervalIntegral.integral_add]
              · rw [intervalIntegral.integral_sub]
                · rw [intervalIntegral.integral_const_mul]
                  rw [intervalIntegral.integral_const_mul]
                  ring
                · apply Continuous.intervalIntegrable; fun_prop
                · apply Continuous.intervalIntegrable; fun_prop
              · apply Continuous.intervalIntegrable; fun_prop
              · apply Continuous.intervalIntegrable; fun_prop
  rw [← hlin]
  exact hderivint

lemma J_succ_left (m : ℕ) : J (m+1) m = J m m - J m (m+1) := by
  simp only [J]
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro x hx
    simp only
    rw [show x ^ (m+1) = x^m * x by simpa [Nat.add_comm] using (pow_succ x m)]
    rw [show (1 - x) ^ (m+1) = (1-x)^m * (1-x) by simpa [Nat.add_comm] using (pow_succ (1-x) m)]
    ring
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

noncomputable def OddErr (m : ℕ) : ℝ := ((-1:ℝ)^(m+2)) / ((m+1) ! : ℝ) * J (m+1) (m+1)
noncomputable def EvenErr (m : ℕ) : ℝ := ((-1:ℝ)^(m+1)) / (m ! : ℝ) * J m (m+2)

lemma J_odd_combo (m : ℕ) :
    J (m+2) (m+2) = 2*(m+1:ℝ)*(m+2:ℝ)*J m (m+2) - (2*(m:ℝ)+3)*(m+2:ℝ)*J (m+1) (m+1) := by
  have hA : J (m+1) (m+2) + (m+1:ℝ) * J m (m+2) - (m+2:ℝ) * J (m+1) (m+1) = 0 := by
    simpa using J_deriv_id (m+1) (m+2) (by omega) (by omega)
  have hB : J (m+2) (m+2) + (m+2:ℝ) * J (m+1) (m+2) - (m+2:ℝ) * J (m+2) (m+1) = 0 := by
    simpa using J_deriv_id (m+2) (m+2) (by omega) (by omega)
  have hS : J (m+2) (m+1) = J (m+1) (m+1) - J (m+1) (m+2) := by
    simpa using J_succ_left (m+1)
  nlinarith

lemma OddErr_rec (m : ℕ) : OddErr (m+1) = 2 * EvenErr m + (2*(m:ℝ)+3) * OddErr m := by
  unfold OddErr EvenErr
  rw [J_odd_combo m]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+1)), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+2))]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring_nf

lemma J_succ_left_gen (a b : ℕ) : J (a+1) b = J a b - J a (b+1) := by
  simp only [J]
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro x hx
    simp only
    rw [show x ^ (a+1) = x^a * x by simpa [Nat.add_comm] using (pow_succ x a)]
    rw [show (1 - x) ^ (b+1) = (1-x)^b * (1-x) by simpa [Nat.add_comm] using (pow_succ (1-x) b)]
    ring
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

lemma J_even_combo (m : ℕ) (hm : 1 ≤ m) :
    -(m+1:ℝ) * J m (m+2) = (m+2:ℝ) * J (m+1) (m+1) - (m:ℝ)*(m+1:ℝ)*J (m-1) (m+1) + (m:ℝ)*(m+1:ℝ)*J m m := by
  have hA : J m (m+1) + (m:ℝ) * J (m-1) (m+1) - (m+1:ℝ) * J m m = 0 := by
    simpa using J_deriv_id m (m+1) (by omega) (by omega)
  have hB : J (m+1) (m+1) + (m+1:ℝ) * J m (m+1) - (m+1:ℝ) * J (m+1) m = 0 := by
    simpa using J_deriv_id (m+1) (m+1) (by omega) (by omega)
  have hS1 : J (m+1) (m+1) = J m (m+1) - J m (m+2) := by
    simpa using J_succ_left_gen m (m+1)
  have hS2 : J (m+1) m = J m m - J m (m+1) := by
    simpa using J_succ_left_gen m m
  nlinarith

lemma EvenErr_rec (m : ℕ) (hm : 1 ≤ m) :
    EvenErr m = (m+2:ℝ) * OddErr m - EvenErr (m-1) - (m:ℝ) * OddErr (m-1) := by
  unfold OddErr EvenErr
  have hJ := J_even_combo m hm
  have hm1 : m - 1 + 1 = m := by omega
  have hm2 : m - 1 + 2 = m + 1 := by omega
  simp only [hm1, hm2]
  have hfactm : (m ! : ℝ) = (m:ℝ) * ((m-1)! : ℝ) := by
    rw [← hm1, Nat.factorial_succ]
    simp [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+1)), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m-1))]
  simp only [hfactm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring_nf at hJ ⊢
  linear_combination ((m:ℝ) * (((m-1)! : ℝ)^2) * ((-1:ℝ)^m)) * hJ

lemma poly1_deriv (x:ℝ): deriv (fun y : ℝ => -y^2 + 3*y -3) x = -2*x+3 := by
  have hsub : deriv (fun y : ℝ => (-y^2 + 3*y) - 3) x = deriv (fun y : ℝ => -y^2 + 3*y) x - deriv (fun y : ℝ => (3:ℝ)) x :=
    deriv_sub (by fun_prop) (by fun_prop)
  have hadd : deriv (fun y : ℝ => -y^2 + 3*y) x = deriv (fun y : ℝ => -y^2) x + deriv (fun y : ℝ => 3*y) x :=
    deriv_add (by fun_prop) (by fun_prop)
  have hneg : deriv (fun y : ℝ => -y^2) x = -(2*x) := by
    rw [show deriv (fun y : ℝ => -y^2) x = (-1:ℝ) * deriv (fun y : ℝ => y^2) x by
      convert deriv_const_mul (-1:ℝ) (show DifferentiableAt ℝ (fun y : ℝ => y^2) x by fun_prop) using 1 <;> ring_nf]
    rw [show deriv (fun y : ℝ => y^2) x = 2*x by simpa using (deriv_pow (f := fun y:ℝ=>y) (x:=x) (by fun_prop) 2)]
    ring
  have hlin : deriv (fun y : ℝ => 3*y) x = 3 := by
    rw [show deriv (fun y : ℝ => 3*y) x = 3 * deriv (fun y : ℝ => y) x by exact deriv_const_mul 3 (by fun_prop)]
    rw [deriv_id'']; ring
  rw [show deriv (fun y : ℝ => -y^2 + 3*y -3) x = deriv (fun y : ℝ => (-y^2 + 3*y) - 3) x by rfl]
  rw [hsub, hadd, hneg, hlin, deriv_const]
  ring

lemma poly2_deriv (x:ℝ): deriv (fun y : ℝ => y^2 - 4*y + 5) x = 2*x-4 := by
  have hsub : deriv (fun y : ℝ => (y^2 - 4*y) + 5) x = deriv (fun y : ℝ => y^2 - 4*y) x + deriv (fun y : ℝ => (5:ℝ)) x :=
    deriv_add (by fun_prop) (by fun_prop)
  have hinner : deriv (fun y : ℝ => y^2 - 4*y) x = deriv (fun y : ℝ => y^2) x - deriv (fun y : ℝ => 4*y) x :=
    deriv_sub (by fun_prop) (by fun_prop)
  have hsq : deriv (fun y : ℝ => y^2) x = 2*x := by
    simpa using (deriv_pow (f := fun y:ℝ=>y) (x:=x) (by fun_prop) 2)
  have hlin : deriv (fun y : ℝ => 4*y) x = 4 := by
    rw [show deriv (fun y : ℝ => 4*y) x = 4 * deriv (fun y : ℝ => y) x by exact deriv_const_mul 4 (by fun_prop)]
    rw [deriv_id'']; ring
  rw [show deriv (fun y : ℝ => y^2 - 4*y + 5) x = deriv (fun y : ℝ => (y^2 - 4*y) + 5) x by ring]
  rw [hsub, hinner, hsq, hlin, deriv_const]
  ring

lemma J_one_one : J 1 1 = 3 - Real.exp 1 := by
  have hderiv : ∀ x ∈ [[(0:ℝ), 1]], DifferentiableAt ℝ (fun y : ℝ => Real.exp y * (-y^2 + 3*y - 3)) x := by
    intro x hx; fun_prop
  have hint : IntervalIntegrable (deriv (fun y : ℝ => Real.exp y * (-y^2 + 3*y - 3))) MeasureTheory.volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hftc := intervalIntegral.integral_deriv_eq_sub hderiv hint
  have hcongr : J 1 1 = ∫ x in (0:ℝ)..1, deriv (fun y : ℝ => Real.exp y * (-y^2 + 3*y - 3)) x := by
    unfold J
    apply intervalIntegral.integral_congr
    intro x hx
    symm
    rw [show deriv (fun y : ℝ => Real.exp y * (-y^2 + 3*y - 3)) x = deriv (fun y : ℝ => Real.exp y) x * (-x^2 + 3*x -3) + Real.exp x * deriv (fun y : ℝ => -y^2 + 3*y -3) x from
      deriv_mul (c := fun y : ℝ => Real.exp y) (d := fun y : ℝ => -y^2 + 3*y -3) (by fun_prop) (by fun_prop)]
    rw [show deriv (fun y : ℝ => Real.exp y) x = Real.exp x by simpa using congrFun Real.deriv_exp x]
    rw [poly1_deriv]
    ring
  rw [hcongr, hftc]
  rw [Real.exp_zero]
  ring

lemma J_zero_two : J 0 2 = 2 * Real.exp 1 - 5 := by
  have hderiv : ∀ x ∈ [[(0:ℝ), 1]], DifferentiableAt ℝ (fun y : ℝ => Real.exp y * (y^2 - 4*y + 5)) x := by
    intro x hx; fun_prop
  have hint : IntervalIntegrable (deriv (fun y : ℝ => Real.exp y * (y^2 - 4*y + 5))) MeasureTheory.volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hftc := intervalIntegral.integral_deriv_eq_sub hderiv hint
  have hcongr : J 0 2 = ∫ x in (0:ℝ)..1, deriv (fun y : ℝ => Real.exp y * (y^2 - 4*y + 5)) x := by
    unfold J
    apply intervalIntegral.integral_congr
    intro x hx
    symm
    rw [show deriv (fun y : ℝ => Real.exp y * (y^2 - 4*y + 5)) x = deriv (fun y : ℝ => Real.exp y) x * (x^2 - 4*x +5) + Real.exp x * deriv (fun y : ℝ => y^2 - 4*y +5) x from
      deriv_mul (c := fun y : ℝ => Real.exp y) (d := fun y : ℝ => y^2 - 4*y +5) (by fun_prop) (by fun_prop)]
    rw [show deriv (fun y : ℝ => Real.exp y) x = Real.exp x by simpa using congrFun Real.deriv_exp x]
    rw [poly2_deriv]
    ring
  rw [hcongr, hftc]
  rw [Real.exp_zero]
  ring

lemma abs_J_le_exp_one (a b : ℕ) : |J a b| ≤ Real.exp 1 := by
  calc
    |J a b| ≤ ∫ x in (0:ℝ)..1, |Real.exp x * x^a * (1-x)^b| := by
      simpa [J] using intervalIntegral.abs_integral_le_integral_abs (f := fun x : ℝ => Real.exp x * x^a * (1-x)^b) (a := (0:ℝ)) (b := 1) (by norm_num)
    _ ≤ ∫ x in (0:ℝ)..1, Real.exp 1 := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · apply Continuous.intervalIntegrable; fun_prop
      · apply Continuous.intervalIntegrable; fun_prop
      · intro x hx
        have hx0 : 0 ≤ x := hx.1
        have hx1 : x ≤ 1 := hx.2
        have h1x0 : 0 ≤ 1 - x := by linarith
        have hxpow_le : x^a ≤ 1 := by simpa using (pow_le_one₀ (n := a) hx0 hx1)
        have h1xpow_le : (1-x)^b ≤ 1 := by
          have hle : 1 - x ≤ 1 := by linarith
          simpa using (pow_le_one₀ (n := b) h1x0 hle)
        have hexp_le : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
        rw [abs_of_nonneg]
        · calc
            Real.exp x * x^a * (1-x)^b ≤ Real.exp 1 * 1 * 1 := by
              gcongr
            _ = Real.exp 1 := by ring
        · positivity
    _ = Real.exp 1 := by simp

lemma abs_OddErr_le (m : ℕ) : |OddErr m| ≤ Real.exp 1 / (m+1 : ℝ) := by
  unfold OddErr
  have hJ := abs_J_le_exp_one (m+1) (m+1)
  have hfactpos : (0:ℝ) < ((m+1)! : ℝ) := by exact_mod_cast Nat.factorial_pos (m+1)
  have hdenpos : (0:ℝ) < (m+1 : ℝ) := by positivity
  have hfacge : (m+1 : ℝ) ≤ ((m+1)! : ℝ) := by exact_mod_cast Nat.self_le_factorial (m+1)
  calc
    |((-1:ℝ) ^ (m + 2) / ↑(m + 1)! * J (m + 1) (m + 1))|
        = |J (m+1) (m+1)| / ((m+1)! : ℝ) := by
            rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, one_div]
            rw [abs_of_pos hfactpos]
            ring
    _ ≤ Real.exp 1 / ((m+1)! : ℝ) := by gcongr
    _ ≤ Real.exp 1 / (m+1 : ℝ) := by
      have hexp_nonneg : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      exact div_le_div_of_nonneg_left hexp_nonneg hdenpos hfacge


lemma abs_EvenErr_le (m : ℕ) (hm : 1 ≤ m) : |EvenErr m| ≤ Real.exp 1 / (m : ℝ) := by
  unfold EvenErr
  have hJ := abs_J_le_exp_one m (m+2)
  have hfactpos : (0:ℝ) < (m ! : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hdenpos : (0:ℝ) < (m : ℝ) := by positivity
  have hfacge : (m : ℝ) ≤ (m ! : ℝ) := by exact_mod_cast Nat.self_le_factorial m
  calc
    |((-1:ℝ) ^ (m + 1) / ↑m ! * J m (m + 2))|
        = |J m (m+2)| / (m ! : ℝ) := by
            rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, one_div]
            rw [abs_of_pos hfactpos]
            ring
    _ ≤ Real.exp 1 / (m ! : ℝ) := by gcongr
    _ ≤ Real.exp 1 / (m : ℝ) := by
      exact div_le_div_of_nonneg_left (Real.exp_pos 1).le hdenpos hfacge

lemma tendsto_abs_OddErr : Tendsto (fun m : ℕ => |OddErr m|) atTop (nhds 0) := by
  apply squeeze_zero (fun m => abs_nonneg (OddErr m)) (fun m => abs_OddErr_le m)
  have h := (tendsto_const_nhds (x := Real.exp 1)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using h

lemma tendsto_OddErr : Tendsto OddErr atTop (nhds 0) := by
  exact (tendsto_zero_iff_abs_tendsto_zero OddErr).2 tendsto_abs_OddErr

lemma tendsto_abs_EvenErr : Tendsto (fun m : ℕ => |EvenErr m|) atTop (nhds 0) := by
  refine squeeze_zero' (f := fun m : ℕ => |EvenErr m|) (g := fun m : ℕ => Real.exp 1 / (m : ℝ)) ?_ ?_ ?_
  · filter_upwards with m
    exact abs_nonneg (EvenErr m)
  · rw [eventually_atTop]
    refine ⟨1, ?_⟩
    intro m hm
    exact abs_EvenErr_le m hm
  · have h := (tendsto_const_nhds (x := Real.exp 1)).mul tendsto_inverse_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv] using h

lemma tendsto_EvenErr : Tendsto EvenErr atTop (nhds 0) := by
  exact (tendsto_zero_iff_abs_tendsto_zero EvenErr).2 tendsto_abs_EvenErr
lemma div_two_form (m : ℕ) : (2 * m + 1 + 3) / 2 = m + 2 := by omega
lemma A_odd_rec (m : ℕ) : A340738 (2*m+3) = 2*A340738 (2*m+2) + (2*m+3)*A340738 (2*m+1) := by simp [A340738, Nat.add_mod]
lemma B_odd_rec (m : ℕ) : A340737 (2*m+3) = 2*A340737 (2*m+2) + (2*m+3)*A340737 (2*m+1) := by simp [A340737, Nat.add_mod]
lemma A_even_rec (m : ℕ) : A340738 (2*m+4) = (m+3)*A340738 (2*m+3) - A340738 (2*m+2) - (m+1)*A340738 (2*m+1) := by simp [A340738, Nat.add_mod]; rw [div_two_form]
lemma B_even_rec (m : ℕ) : A340737 (2*m+4) = (m+3)*A340737 (2*m+3) - A340737 (2*m+2) - (m+1)*A340737 (2*m+1) := by simp [A340737, Nat.add_mod]; rw [div_two_form]

lemma even_output_ge (m a b c : ℕ) (ha : a ≤ c) (hb : b ≤ c) : c ≤ (m+3)*c - b - (m+1)*a := by
  have hsum : b + (m+1)*a + c ≤ (m+3)*c := by
    nlinarith [Nat.mul_le_mul_left (m+1) ha]
  omega

lemma A_mono_pair : ∀ m : ℕ, A340738 (2*m+1) ≤ A340738 (2*m+2) ∧ A340738 (2*m+2) ≤ A340738 (2*m+3) := by
  intro m
  induction m with
  | zero => norm_num [A340738]
  | succ m ih =>
      rcases ih with ⟨h12, h23⟩
      have h34 : A340738 (2*m+3) ≤ A340738 (2*m+4) := by
        rw [A_even_rec]
        exact even_output_ge m (A340738 (2*m+1)) (A340738 (2*m+2)) (A340738 (2*m+3)) (h12.trans h23) h23
      have h45 : A340738 (2*m+4) ≤ A340738 (2*m+5) := by
        rw [show 2*m+5 = 2*(m+1)+3 by ring, A_odd_rec]
        change A340738 (2*m+4) ≤ 2 * A340738 (2*m+4) + (2*m+5) * A340738 (2*m+3)
        omega
      simpa [Nat.mul_add, Nat.add_assoc, Nat.left_distrib, Nat.right_distrib] using And.intro h34 h45

lemma B_mono_pair : ∀ m : ℕ, A340737 (2*m+1) ≤ A340737 (2*m+2) ∧ A340737 (2*m+2) ≤ A340737 (2*m+3) := by
  intro m
  induction m with
  | zero => norm_num [A340737]
  | succ m ih =>
      rcases ih with ⟨h12, h23⟩
      have h34 : A340737 (2*m+3) ≤ A340737 (2*m+4) := by
        rw [B_even_rec]
        exact even_output_ge m (A340737 (2*m+1)) (A340737 (2*m+2)) (A340737 (2*m+3)) (h12.trans h23) h23
      have h45 : A340737 (2*m+4) ≤ A340737 (2*m+5) := by
        rw [show 2*m+5 = 2*(m+1)+3 by ring, B_odd_rec]
        change A340737 (2*m+4) ≤ 2 * A340737 (2*m+4) + (2*m+5) * A340737 (2*m+3)
        omega
      simpa [Nat.mul_add, Nat.add_assoc, Nat.left_distrib, Nat.right_distrib] using And.intro h34 h45

lemma cast_even_rec_of_mono (m a b c : ℕ) (ha : a ≤ c) (hb : b ≤ c) :
    (((m+3)*c - b - (m+1)*a : ℕ) : ℝ) = (m+3:ℝ)*c - (b:ℝ) - (m+1:ℝ)*a := by
  have hb1 : b ≤ (m+3)*c := by
    have hc : c ≤ (m+3)*c := by nlinarith
    exact hb.trans hc
  have hsub : (m+1)*a ≤ (m+3)*c - b := by
    apply Nat.le_sub_of_add_le
    have : b + (m+1)*a ≤ (m+3)*c := by
      nlinarith [Nat.mul_le_mul_left (m+1) ha]
    simpa [add_comm, add_left_comm, add_assoc] using this
  rw [Nat.cast_sub hsub, Nat.cast_sub hb1]
  norm_num [Nat.cast_mul, Nat.cast_add]

lemma A_even_rec_real (m : ℕ) : (A340738 (2*m+4) : ℝ) = (m+3:ℝ)*(A340738 (2*m+3):ℝ) - (A340738 (2*m+2):ℝ) - (m+1:ℝ)*(A340738 (2*m+1):ℝ) := by
  rw [A_even_rec]
  exact cast_even_rec_of_mono m _ _ _ ((A_mono_pair m).1.trans (A_mono_pair m).2) (A_mono_pair m).2

lemma B_even_rec_real (m : ℕ) : (A340737 (2*m+4) : ℝ) = (m+3:ℝ)*(A340737 (2*m+3):ℝ) - (A340737 (2*m+2):ℝ) - (m+1:ℝ)*(A340737 (2*m+1):ℝ) := by
  rw [B_even_rec]
  exact cast_even_rec_of_mono m _ _ _ ((B_mono_pair m).1.trans (B_mono_pair m).2) (B_mono_pair m).2

lemma err_pair :
    (∀ m : ℕ, (A340737 (2*m+1) : ℝ) - Real.exp 1 * (A340738 (2*m+1) : ℝ) = OddErr m) ∧
    (∀ m : ℕ, (A340737 (2*m+2) : ℝ) - Real.exp 1 * (A340738 (2*m+2) : ℝ) = EvenErr m) := by
  have h : ∀ m : ℕ,
    ((A340737 (2*m+1) : ℝ) - Real.exp 1 * (A340738 (2*m+1) : ℝ) = OddErr m) ∧
    ((A340737 (2*m+2) : ℝ) - Real.exp 1 * (A340738 (2*m+2) : ℝ) = EvenErr m) := by
    intro m
    induction m with
    | zero =>
        constructor
        · simp [A340737, A340738, OddErr, J_one_one]
        · simp [A340737, A340738, EvenErr, J_zero_two]
          ring
    | succ m ih =>
        rcases ih with ⟨hodd, heven⟩
        have hodd_succ : (A340737 (2*(m+1)+1) : ℝ) - Real.exp 1 * (A340738 (2*(m+1)+1) : ℝ) = OddErr (m+1) := by
          rw [show 2*(m+1)+1 = 2*m+3 by ring]
          rw [B_odd_rec, A_odd_rec]
          push_cast
          rw [show (2:ℝ) * A340737 (2 * m + 2) + (2*(m:ℝ)+3) * A340737 (2 * m + 1) -
              Real.exp 1 * ( (2:ℝ) * A340738 (2 * m + 2) + (2*(m:ℝ)+3) * A340738 (2 * m + 1)) =
              2*((A340737 (2*m+2):ℝ)-Real.exp 1*(A340738 (2*m+2):ℝ)) + (2*(m:ℝ)+3)*((A340737 (2*m+1):ℝ)-Real.exp 1*(A340738 (2*m+1):ℝ)) by ring]
          rw [hodd, heven, OddErr_rec]
        have hodd_succ_norm : (A340737 (2*m+3) : ℝ) - Real.exp 1 * (A340738 (2*m+3) : ℝ) = OddErr (m+1) := by
          simpa [show 2*(m+1)+1 = 2*m+3 by ring] using hodd_succ
        have heven_succ : (A340737 (2*(m+1)+2) : ℝ) - Real.exp 1 * (A340738 (2*(m+1)+2) : ℝ) = EvenErr (m+1) := by
          rw [show 2*(m+1)+2 = 2*m+4 by ring]
          rw [B_even_rec_real, A_even_rec_real]
          rw [show (↑m + 3) * ↑(A340737 (2 * m + 3)) - ↑(A340737 (2 * m + 2)) - (↑m + 1) * ↑(A340737 (2 * m + 1)) -
                Real.exp 1 * ((↑m + 3) * ↑(A340738 (2 * m + 3)) - ↑(A340738 (2 * m + 2)) - (↑m + 1) * ↑(A340738 (2 * m + 1))) =
                (m+3:ℝ)*((A340737 (2*m+3):ℝ)-Real.exp 1*(A340738 (2*m+3):ℝ)) -
                ((A340737 (2*m+2):ℝ)-Real.exp 1*(A340738 (2*m+2):ℝ)) -
                (m+1:ℝ)*((A340737 (2*m+1):ℝ)-Real.exp 1*(A340738 (2*m+1):ℝ)) by ring]
          rw [hodd_succ_norm, heven, hodd, EvenErr_rec (m+1) (by omega)]
          rw [show m + 1 - 1 = m by omega]
          norm_num [Nat.cast_add, Nat.cast_one]
          left
          ring
        exact ⟨hodd_succ, heven_succ⟩
  exact ⟨fun m => (h m).1, fun m => (h m).2⟩

lemma A_pos_pair : ∀ m : ℕ, 0 < A340738 (2*m+1) ∧ 0 < A340738 (2*m+2) := by
  intro m
  induction m with
  | zero => norm_num [A340738]
  | succ m ih =>
      constructor
      · exact lt_of_lt_of_le ih.2 (A_mono_pair m).2
      · exact lt_of_lt_of_le (lt_of_lt_of_le ih.2 (A_mono_pair m).2) (A_mono_pair (m+1)).1

lemma A_pos_of_pos {n : ℕ} (hn : 1 ≤ n) : 0 < A340738 n := by
  by_cases h : n % 2 = 0
  · let m := n/2 - 1
    have hnrepr : n = 2*m+2 := by
      dsimp [m]
      omega
    rw [hnrepr]
    exact (A_pos_pair m).2
  · let m := n/2
    have hnrepr : n = 2*m+1 := by
      dsimp [m]
      omega
    rw [hnrepr]
    exact (A_pos_pair m).1

lemma tendsto_errorSeq : Tendsto (fun n : ℕ => (A340737 n : ℝ) - Real.exp 1 * (A340738 n : ℝ)) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hodd := (Metric.tendsto_nhds.1 tendsto_OddErr) ε hε
  have heven := (Metric.tendsto_nhds.1 tendsto_EvenErr) ε hε
  rw [eventually_atTop] at hodd heven ⊢
  rcases hodd with ⟨No, hodd⟩
  rcases heven with ⟨Ne, heven⟩
  refine ⟨2 * max No Ne + 2, ?_⟩
  intro n hn
  by_cases hpar : n % 2 = 0
  · let m := n/2 - 1
    have hnrepr : n = 2*m+2 := by dsimp [m]; omega
    have hm : Ne ≤ m := by dsimp [m]; omega
    have herr := heven m hm
    rw [hnrepr, (err_pair).2 m]
    simpa [Real.dist_eq, abs_sub_comm] using herr
  · let m := n/2
    have hnrepr : n = 2*m+1 := by dsimp [m]; omega
    have hm : No ≤ m := by dsimp [m]; omega
    have herr := hodd m hm
    rw [hnrepr, (err_pair).1 m]
    simpa [Real.dist_eq, abs_sub_comm] using herr

lemma tendsto_sequence_sub_exp : Tendsto (fun n : ℕ => sequence_of_fractions n - Real.exp 1) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have herr := (Metric.tendsto_nhds.1 tendsto_errorSeq) ε hε
  rw [eventually_atTop] at herr ⊢
  rcases herr with ⟨N, hN⟩
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 N) hn
  have hnN : N ≤ n := le_trans (le_max_right 1 N) hn
  have hAposNat : 0 < A340738 n := A_pos_of_pos hn1
  have hApos : (0:ℝ) < (A340738 n : ℝ) := by exact_mod_cast hAposNat
  have hAge1 : (1:ℝ) ≤ (A340738 n : ℝ) := by exact_mod_cast hAposNat
  have herrn := hN n hnN
  rw [Real.dist_eq] at herrn ⊢
  have hneq : (A340738 n : ℝ) ≠ 0 := ne_of_gt hApos
  have halg : sequence_of_fractions n - Real.exp 1 = ((A340737 n : ℝ) - Real.exp 1 * (A340738 n : ℝ)) / (A340738 n : ℝ) := by
    rw [sequence_of_fractions]
    field_simp [hneq]
  rw [halg]
  simp only [sub_zero]
  calc
    |((A340737 n : ℝ) - Real.exp 1 * (A340738 n : ℝ)) / (A340738 n : ℝ)|
        = |(A340737 n : ℝ) - Real.exp 1 * (A340738 n : ℝ)| / (A340738 n : ℝ) := by
          rw [abs_div, abs_of_pos hApos]
    _ ≤ |(A340737 n : ℝ) - Real.exp 1 * (A340738 n : ℝ)| := by
          simpa using div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num : (0:ℝ) < 1) hAge1
    _ < ε := by simpa [Real.dist_eq] using herrn

theorem oeis_340738_conjecture_0 :
  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) := by
  have h2 : Tendsto (fun n : ℕ => sequence_of_fractions n - Real.exp 1 + Real.exp 1) atTop (nhds (0 + Real.exp 1)) :=
    tendsto_sequence_sub_exp.add tendsto_const_nhds
  simpa using h2
