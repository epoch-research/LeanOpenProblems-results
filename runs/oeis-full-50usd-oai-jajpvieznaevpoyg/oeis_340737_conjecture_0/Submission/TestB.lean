import FormalConjectures.Util.ProblemImports

open Nat

/--
A340737: Numerators of a sequence of fractions converging to $e$.
$$a(1) = 3, a(2) = 5$$
For $n > 2$:
$$a(n) = \begin{cases} \left(\frac{n+2}{2}\right) a(n-1) - a(n-2) - \left(\frac{n-2}{2}\right) a(n-3) & \text{if } n \text{ is even} \\ 2 a(n-1) + n a(n-2) & \text{if } n \text{ is odd} \end{cases}$$
-/
noncomputable def A340737 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Required for total function, O(1,1) suggests 0 is not relevant.
  | 1 => 3
  | 2 => 5
  | n' + 3 => -- n $\ge$ 3
    let n := n' + 3

    let a_nm1 := A340737 (n - 1)
    let a_nm2 := A340737 (n - 2)
    let a_nm3 := A340737 (n - 3)

    if n % 2 = 0 then
      -- n is even, n $\ge$ 4
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2

      -- $a(n) = c_1 \cdot a(n-1) - a(n-2) - c_2 \cdot a(n-3)$.
      -- We use Int.ofNat for safe subtraction, as the result is known to be positive.
      Int.toNat (Int.ofNat c1 * Int.ofNat a_nm1 - Int.ofNat a_nm2 - Int.ofNat c2 * Int.ofNat a_nm3)
    else
      -- n is odd, n $\ge$ 3
      2 * a_nm1 + n * a_nm2
termination_by n

/--
A340738: Denominators of a sequence of fractions converging to $e$.
This sequence is defined by the same recurrence relation as A340737 but with initial values $b(1)=1, b(2)=2$.
$$b(1) = 1, b(2) = 2$$
For $n > 2$:
$$b(n) = \begin{cases} \left(\frac{n+2}{2}\right) b(n-1) - b(n-2) - \left(\frac{n-2}{2}\right) b(n-3) & \text{if } n \text{ is even} \\ 2 b(n-1) + n b(n-2) & \text{if } n \text{ is odd} \end{cases}$$
-/
noncomputable def A340738 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n' + 3 => -- n $\ge$ 3
    let n := n' + 3

    let b_nm1 := A340738 (n - 1)
    let b_nm2 := A340738 (n - 2)
    let b_nm3 := A340738 (n - 3)

    if n % 2 = 0 then
      -- n is even, n $\ge$ 4
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2

      -- $b(n) = c_1 \cdot b(n-1) - b(n-2) - c_2 \cdot b(n-3)$.
      -- We use Int.ofNat for safe subtraction.
      Int.toNat (Int.ofNat c1 * Int.ofNat b_nm1 - Int.ofNat b_nm2 - Int.ofNat c2 * Int.ofNat b_nm3)
    else
      -- n is odd, n $\ge$ 3
      2 * b_nm1 + n * b_nm2
termination_by n


open scoped Interval
open MeasureTheory intervalIntegral Filter

noncomputable def prevA (m : ℕ) : ℕ := if m = 0 then 1 else A340737 (2*m - 1)
noncomputable def prevB (m : ℕ) : ℕ := if m = 0 then 1 else A340738 (2*m - 1)

lemma A_odd_step (m : ℕ) : A340737 (2*m + 3) = 2 * A340737 (2*m + 2) + (2*m + 3) * A340737 (2*m + 1) := by
  rw [A340737]
  have hodd : (2 * m + 3) % 2 ≠ 0 := by omega
  simp

lemma B_odd_step (m : ℕ) : A340738 (2*m + 3) = 2 * A340738 (2*m + 2) + (2*m + 3) * A340738 (2*m + 1) := by
  rw [A340738]
  have hodd : (2 * m + 3) % 2 ≠ 0 := by omega
  simp

lemma A_even_bridge (m : ℕ) : 2 * A340737 (2*m + 2) = (2*m + 3) * A340737 (2*m + 1) + prevA m := by
  induction m with
  | zero => norm_num [prevA, A340737]
  | succ m ih =>
      have hodd := A_odd_step m
      rw [show 2 * (m+1) + 2 = 2*m + 4 by ring]
      rw [A340737]
      have heven : (2 * m + 4) % 2 = 0 := by omega
      simp [heven, prevA]
      let z : ℤ := (((2 * ↑m + 1 + 3) / 2 + 1) * ↑(A340737 (2 * m + 3)) - ↑(A340737 (2 * m + 2)) -
          (↑m + 1) * ↑(A340737 (2 * m + 1)))
      change 2 * z.toNat = (2 * (m + 1) + 3) * A340737 (2 * (m + 1) + 1) + A340737 (2 * (m + 1) - 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      have hoddI : (A340737 (2 * m + 3) : ℤ) = 2 * (A340737 (2 * m + 2) : ℤ) + (2 * m + 3 : ℕ) * (A340737 (2 * m + 1) : ℤ) := by
        exact_mod_cast hodd
      have hz2 : 2 * z = ((2 * m + 5) * A340737 (2 * m + 3) + A340737 (2 * m + 1) : ℕ) := by
        dsimp [z]
        have hdiv : (2 * (m : ℤ) + 1 + 3) / 2 = (m : ℤ) + 2 := by omega
        rw [hdiv, hoddI]
        norm_num
        ring
      have hznon : 0 ≤ z := by
        have hrhs_non : (0 : ℤ) ≤ ((2 * m + 5) * A340737 (2 * m + 3) + A340737 (2 * m + 1) : ℕ) := by positivity
        nlinarith
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_mul, Int.toNat_of_nonneg hznon]
      exact hz2

lemma B_even_bridge (m : ℕ) : 2 * A340738 (2*m + 2) = (2*m + 3) * A340738 (2*m + 1) + prevB m := by
  induction m with
  | zero => norm_num [prevB, A340738]
  | succ m ih =>
      have hodd := B_odd_step m
      rw [show 2 * (m+1) + 2 = 2*m + 4 by ring]
      rw [A340738]
      have heven : (2 * m + 4) % 2 = 0 := by omega
      simp [heven, prevB]
      let z : ℤ := (((2 * ↑m + 1 + 3) / 2 + 1) * ↑(A340738 (2 * m + 3)) - ↑(A340738 (2 * m + 2)) -
          (↑m + 1) * ↑(A340738 (2 * m + 1)))
      change 2 * z.toNat = (2 * (m + 1) + 3) * A340738 (2 * (m + 1) + 1) + A340738 (2 * (m + 1) - 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      have hoddI : (A340738 (2 * m + 3) : ℤ) = 2 * (A340738 (2 * m + 2) : ℤ) + (2 * m + 3 : ℕ) * (A340738 (2 * m + 1) : ℤ) := by
        exact_mod_cast hodd
      have hz2 : 2 * z = ((2 * m + 5) * A340738 (2 * m + 3) + A340738 (2 * m + 1) : ℕ) := by
        dsimp [z]
        have hdiv : (2 * (m : ℤ) + 1 + 3) / 2 = (m : ℤ) + 2 := by omega
        rw [hdiv, hoddI]
        norm_num
        ring
      have hznon : 0 ≤ z := by
        have hrhs_non : (0 : ℤ) ≤ ((2 * m + 5) * A340738 (2 * m + 3) + A340738 (2 * m + 1) : ℕ) := by positivity
        nlinarith
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_mul, Int.toNat_of_nonneg hznon]
      exact hz2

lemma A_odd_recurrence (m : ℕ) : A340737 (2*m + 5) = (4*m + 10) * A340737 (2*m + 3) + A340737 (2*m + 1) := by
  rw [show 2*m + 5 = 2*(m+1)+3 by ring]
  rw [A_odd_step (m+1)]
  rw [show 2*(m+1)+2 = 2*m+4 by ring, show 2*(m+1)+3 = 2*m+5 by ring,
    show 2*(m+1)+1 = 2*m+3 by ring]
  have hb := A_even_bridge (m+1)
  rw [show 2 * (m+1) + 2 = 2*m+4 by ring] at hb
  rw [show 2 * (m+1) + 1 = 2*m+3 by ring] at hb
  rw [show 2 * (m+1) + 3 = 2*m+5 by ring] at hb
  rw [show prevA (m+1) = A340737 (2*m+1) by simp [prevA]; congr <;> omega] at hb
  rw [hb]
  ring

lemma B_odd_recurrence (m : ℕ) : A340738 (2*m + 5) = (4*m + 10) * A340738 (2*m + 3) + A340738 (2*m + 1) := by
  rw [show 2*m + 5 = 2*(m+1)+3 by ring]
  rw [B_odd_step (m+1)]
  rw [show 2*(m+1)+2 = 2*m+4 by ring, show 2*(m+1)+3 = 2*m+5 by ring,
    show 2*(m+1)+1 = 2*m+3 by ring]
  have hb := B_even_bridge (m+1)
  rw [show 2 * (m+1) + 2 = 2*m+4 by ring] at hb
  rw [show 2 * (m+1) + 1 = 2*m+3 by ring] at hb
  rw [show 2 * (m+1) + 3 = 2*m+5 by ring] at hb
  rw [show prevB (m+1) = A340738 (2*m+1) by simp [prevB]; congr <;> omega] at hb
  rw [hb]
  ring

lemma B_odd_pos (m : ℕ) : 0 < A340738 (2*m+1) := by
  induction m using Nat.twoStepInduction with
  | zero => norm_num [A340738]
  | one => norm_num [A340738]
  | more m h0 h1 =>
      rw [show 2*(m+2)+1 = 2*m+5 by ring]
      rw [B_odd_recurrence m]
      positivity

lemma deriv_tpow (r : ℕ) : deriv (fun x : ℝ => (x * (1 - x)) ^ r) =
    fun x => (r : ℝ) * (x * (1 - x)) ^ (r - 1) * (1 - 2 * x) := by
  funext x
  by_cases hr : r = 0
  · subst r
    simp
  · have hder : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * x) x := by
      convert ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))) using 1
      · simp
        ring
    have hp := hder.pow r
    rw [deriv]
    exact hp.deriv

example (r : ℕ) :
    (∫ x in (0:ℝ)..1, Real.exp x * deriv (fun y : ℝ => (y * (1 - y)) ^ r) x)
      = Real.exp 1 * ((1:ℝ) * (1 - 1)) ^ r - Real.exp 0 * ((0:ℝ) * (1 - 0)) ^ r
        - ∫ x in (0:ℝ)..1, Real.exp x * ((x * (1 - x)) ^ r) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => Real.exp x) (u' := fun x : ℝ => Real.exp x)
    (v := fun x : ℝ => (x * (1 - x)) ^ r)
    (v' := fun x : ℝ => deriv (fun y : ℝ => (y * (1 - y)) ^ r) x)
    (a := (0:ℝ)) (b := (1:ℝ))
    (hu := by intro x hx; exact Real.hasDerivAt_exp x)
    (hv := by intro x hx; exact (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => (y * (1 - y)) ^ r) x).hasDerivAt)
    (hu' := by exact Continuous.intervalIntegrable (by fun_prop) 0 1)
    (hv' := by
      rw [deriv_tpow]
      exact Continuous.intervalIntegrable (by fun_prop) 0 1)
  simpa using h


lemma integral_exp_deriv2_eq (r : ℕ) (hr : 2 ≤ r) :
    (∫ x in (0:ℝ)..1, Real.exp x * deriv (deriv (fun y : ℝ => (y * (1 - y)) ^ r)) x)
      = ∫ x in (0:ℝ)..1, Real.exp x * ((x * (1 - x)) ^ r) := by
  let phi : ℝ → ℝ := fun y => (y * (1 - y)) ^ r
  have hphi0 : phi 0 = 0 := by
    dsimp [phi]
    have : r ≠ 0 := by omega
    simp [this]
  have hphi1 : phi 1 = 0 := by
    dsimp [phi]
    have : r ≠ 0 := by omega
    simp [this]
  have hdphi0 : deriv phi 0 = 0 := by
    dsimp [phi]
    rw [deriv_tpow]
    have : r - 1 ≠ 0 := by omega
    simp [this]
  have hdphi1 : deriv phi 1 = 0 := by
    dsimp [phi]
    rw [deriv_tpow]
    have : r - 1 ≠ 0 := by omega
    simp [this]
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => Real.exp x) (u' := fun x : ℝ => Real.exp x)
    (v := phi) (v' := fun x : ℝ => deriv phi x)
    (a := (0:ℝ)) (b := (1:ℝ))
    (hu := by intro x hx; exact Real.hasDerivAt_exp x)
    (hv := by intro x hx; exact (by dsimp [phi]; fun_prop : DifferentiableAt ℝ phi x).hasDerivAt)
    (hu' := by exact Continuous.intervalIntegrable (by fun_prop) 0 1)
    (hv' := by
      dsimp [phi]
      rw [deriv_tpow]
      exact Continuous.intervalIntegrable (by fun_prop) 0 1)
  have ibp1' : (∫ x in (0:ℝ)..1, Real.exp x * deriv phi x) = - ∫ x in (0:ℝ)..1, Real.exp x * phi x := by
    rw [ibp1, hphi0, hphi1]
    simp
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => Real.exp x) (u' := fun x : ℝ => Real.exp x)
    (v := fun x : ℝ => deriv phi x) (v' := fun x : ℝ => deriv (deriv phi) x)
    (a := (0:ℝ)) (b := (1:ℝ))
    (hu := by intro x hx; exact Real.hasDerivAt_exp x)
    (hv := by
      intro x hx
      dsimp [phi]
      rw [deriv_tpow]
      exact (by fun_prop : DifferentiableAt ℝ (fun x => (r : ℝ) * (x * (1 - x)) ^ (r - 1) * (1 - 2 * x)) x).hasDerivAt)
    (hu' := by exact Continuous.intervalIntegrable (by fun_prop) 0 1)
    (hv' := by
      dsimp [phi]
      rw [deriv_tpow]
      exact Continuous.intervalIntegrable (by fun_prop) 0 1)
  rw [ibp2, hdphi0, hdphi1]
  rw [ibp1']
  simp [phi]

-- copied second derivative lemmas
lemma deriv_second_aux (r : ℕ) (hr : 2 ≤ r) (x : ℝ) :
    deriv (fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1) * (1 - 2 * y)) x =
      (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2) * (1 - 2 * x) ^ 2
        - 2 * (r : ℝ) * (x * (1 - x)) ^ (r - 1) := by
  have hpow : deriv (fun y : ℝ => (y * (1 - y)) ^ (r - 1)) x =
      ((r - 1 : ℕ) : ℝ) * (x * (1 - x)) ^ ((r - 1) - 1) * (1 - 2 * x) := by
    simpa using congrFun (deriv_tpow (r - 1)) x
  have hconst : deriv (fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1)) x =
      (r : ℝ) * deriv (fun y : ℝ => (y * (1 - y)) ^ (r - 1)) x := by
    rw [deriv_const_mul]
    fun_prop
  have hlin : deriv (fun y : ℝ => 1 - 2 * y) x = -2 := by
    have h : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
      convert (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_const x (2:ℝ)).mul (hasDerivAt_id x)) using 1
      · norm_num
    exact h.deriv
  change deriv (((fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1)) *
      (fun y : ℝ => 1 - 2 * y))) x = _
  rw [deriv_mul (c := fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1))
      (d := fun y : ℝ => 1 - 2 * y)]
  · rw [hconst, hpow, hlin]
    have h1 : r - 1 - 1 = r - 2 := by omega
    have hcast : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num
    rw [h1, hcast]
    ring
  · fun_prop
  · fun_prop

lemma deriv2_tpow_chain (r : ℕ) (hr : 2 ≤ r) : deriv (deriv (fun x : ℝ => (x * (1 - x)) ^ r)) =
    fun x => (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2) * (1 - 2 * x) ^ 2
        - 2 * (r : ℝ) * (x * (1 - x)) ^ (r - 1) := by
  funext x
  rw [deriv_tpow]
  exact deriv_second_aux r hr x

lemma deriv2_tpow_expanded (r : ℕ) (hr : 2 ≤ r) : deriv (deriv (fun x : ℝ => (x * (1 - x)) ^ r)) =
    fun x => (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2)
        - (2 * (r : ℝ) * (2 * (r : ℝ) - 1)) * (x * (1 - x)) ^ (r - 1) := by
  rw [deriv2_tpow_chain r hr]
  funext x
  have hpow : (x * (1 - x)) ^ (r - 1) = (x * (1 - x)) ^ (r - 2) * (x * (1 - x)) := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
  rw [hpow]
  ring

noncomputable def K (r : ℕ) : ℝ := ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ r

lemma K_recurrence (r : ℕ) (hr : 2 ≤ r) :
    K r = (r : ℝ) * (r - 1 : ℝ) * K (r - 2) - (2 * (r : ℝ) * (2 * (r : ℝ) - 1)) * K (r - 1) := by
  have h := (integral_exp_deriv2_eq r hr).symm
  rw [deriv2_tpow_expanded r hr] at h
  dsimp [K]
  rw [h]
  simp only [Pi.sub_apply, mul_sub]
  rw [intervalIntegral.integral_sub]
  · let c : ℝ := (r : ℝ) * (r - 1 : ℝ)
    let d : ℝ := (2 * (r : ℝ) * (2 * (r : ℝ) - 1))
    have hA : (∫ x in (0:ℝ)..1, Real.exp x * (c * (x * (1 - x)) ^ (r - 2))) =
        c * ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ (r - 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    have hB : (∫ x in (0:ℝ)..1, Real.exp x * (d * (x * (1 - x)) ^ (r - 1))) =
        d * ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ (r - 1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    have hA' : (∫ x in (0:ℝ)..1, Real.exp x * (((r : ℝ) * (r : ℝ) - (r : ℝ) * 1) * (x * 1 - x * x) ^ (r - 2))) =
        ((r : ℝ) * (r : ℝ) - (r : ℝ) * 1) * ∫ x in (0:ℝ)..1, Real.exp x * (x * 1 - x * x) ^ (r - 2) := by
      calc
        (∫ x in (0:ℝ)..1, Real.exp x * (((r : ℝ) * (r : ℝ) - (r : ℝ) * 1) * (x * 1 - x * x) ^ (r - 2)))
            = ∫ x in (0:ℝ)..1, Real.exp x * (c * (x * (1 - x)) ^ (r - 2)) := by
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp [c]
              ring
        _ = c * ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ (r - 2) := hA
        _ = ((r : ℝ) * (r : ℝ) - (r : ℝ) * 1) * ∫ x in (0:ℝ)..1, Real.exp x * (x * 1 - x * x) ^ (r - 2) := by
              dsimp [c]
              ring_nf
    have hB' : (∫ x in (0:ℝ)..1, Real.exp x * (((2 * (r : ℝ) * (2 * (r : ℝ)) - 2 * (r : ℝ) * 1)) * (x * 1 - x * x) ^ (r - 1))) =
        ((2 * (r : ℝ) * (2 * (r : ℝ)) - 2 * (r : ℝ) * 1)) * ∫ x in (0:ℝ)..1, Real.exp x * (x * 1 - x * x) ^ (r - 1) := by
      calc
        (∫ x in (0:ℝ)..1, Real.exp x * (((2 * (r : ℝ) * (2 * (r : ℝ)) - 2 * (r : ℝ) * 1)) * (x * 1 - x * x) ^ (r - 1)))
            = ∫ x in (0:ℝ)..1, Real.exp x * (d * (x * (1 - x)) ^ (r - 1)) := by
              apply intervalIntegral.integral_congr
              intro x hx
              dsimp [d]
              ring
        _ = d * ∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ (r - 1) := hB
        _ = ((2 * (r : ℝ) * (2 * (r : ℝ)) - 2 * (r : ℝ) * 1)) * ∫ x in (0:ℝ)..1, Real.exp x * (x * 1 - x * x) ^ (r - 1) := by
              dsimp [d]
              ring_nf
    rw [hA', hB']
  · exact Continuous.intervalIntegrable (by fun_prop) 0 1
  · exact Continuous.intervalIntegrable (by fun_prop) 0 1


noncomputable def S (m : ℕ) : ℝ := (-1 : ℝ) ^ (m + 1) * K (m + 1) / (m + 1).factorial

lemma S_recurrence (m : ℕ) : S (m + 2) = (4*m + 10 : ℝ) * S (m + 1) + S m := by
  unfold S
  have hK := K_recurrence (m + 3) (by omega : 2 ≤ m + 3)
  -- K(m+3) relation, now algebra with factorials/signs
  rw [hK]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+1)), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+2)), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m+3))]
  rw [show m + 3 - 2 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega]
  ring_nf


lemma K_zero : K 0 = Real.exp 1 - 1 := by
  dsimp [K]
  simpa using intervalIntegral.integral_exp 0 1

lemma K_one : K 1 = 3 - Real.exp 1 := by
  dsimp [K]
  have hder : deriv (fun x : ℝ => Real.exp x * (-x^2 + 3*x - 3)) = fun x => Real.exp x * (x * (1 - x)) := by
    funext x
    change deriv (((fun x : ℝ => Real.exp x) * (fun x : ℝ => -x^2 + 3*x - 3))) x = _
    rw [deriv_mul (c := fun x : ℝ => Real.exp x) (d := fun x : ℝ => -x^2 + 3*x - 3)]
    · rw [Real.deriv_exp]
      have hp : deriv (fun x : ℝ => -x^2 + 3*x - 3) x = -2*x + 3 := by
        have h1 : HasDerivAt (fun x : ℝ => -(x^2)) (-(2*x)) x := by
          convert ((hasDerivAt_id x).pow 2).neg using 1
          · simp
        have h2 : HasDerivAt (fun x : ℝ => 3*x) 3 x := by
          convert ((hasDerivAt_const x (3:ℝ)).mul (hasDerivAt_id x)) using 1 <;> ring
        have h3 : HasDerivAt (fun x : ℝ => -x^2 + 3*x - 3) (-2*x + 3) x := by
          convert (h1.add h2).sub (hasDerivAt_const x (3:ℝ)) using 1 <;> ring
        exact h3.deriv
      rw [hp]
      ring
    · exact Real.differentiableAt_exp
    · fun_prop
  simp only [pow_one]
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (a := (0:ℝ)) (b := (1:ℝ))
    (fun x : ℝ => Real.exp x * (-x^2 + 3*x - 3)) hder
    (by intro x hx; fun_prop)
    (by fun_prop)
  rw [hftc]
  norm_num
  ring

lemma K_two : K 2 = 14 * Real.exp 1 - 38 := by
  have h := K_recurrence 2 (by norm_num)
  norm_num [K_zero, K_one] at h
  linarith

lemma S_zero : S 0 = Real.exp 1 - 3 := by
  norm_num [S, K_one]

lemma S_one : S 1 = 7 * Real.exp 1 - 19 := by
  norm_num [S, K_two]
  ring


lemma K_nonneg (r : ℕ) : 0 ≤ K r := by
  dsimp [K]
  apply intervalIntegral.integral_nonneg
  · norm_num
  · intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have ht0 : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
    exact mul_nonneg (Real.exp_pos x).le (pow_nonneg ht0 r)

lemma K_le_exp (r : ℕ) : K r ≤ Real.exp 1 := by
  dsimp [K]
  have hmono : (∫ x in (0:ℝ)..1, Real.exp x * (x * (1 - x)) ^ r) ≤ ∫ x in (0:ℝ)..1, Real.exp 1 := by
    apply intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := (1:ℝ)) (μ := volume)
    · norm_num
    · exact Continuous.intervalIntegrable (by fun_prop) 0 1
    · exact Continuous.intervalIntegrable (by fun_prop) 0 1
    · intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := hx.2
      have ht0 : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
      have ht1 : x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg (x-1)]
      have htpow : (x * (1 - x)) ^ r ≤ 1 := by
        exact pow_le_one₀ ht0 ht1
      have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
      simpa using mul_le_mul hexp htpow (pow_nonneg ht0 r) (Real.exp_pos 1).le
  have hconst : (∫ x in (0:ℝ)..1, Real.exp 1) = Real.exp 1 := by simp
  simpa [hconst] using hmono

lemma S_tendsto_zero : Filter.Tendsto S Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hbound : ∀ m, |S m| ≤ Real.exp 1 * (((m+1).factorial : ℝ)⁻¹) := by
    intro m
    have hK0 := K_nonneg (m+1)
    have hK1 := K_le_exp (m+1)
    unfold S
    have hfacpos : 0 < ((m+1).factorial : ℝ) := by positivity
    rw [abs_div, abs_mul, abs_pow]
    norm_num
    rw [abs_of_nonneg hK0]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hK1 (inv_nonneg.mpr hfacpos.le)
  refine squeeze_zero (fun m => ?_) hbound ?_
  · exact abs_nonneg (S m)
  · have ht : Filter.Tendsto (fun m : ℕ => Real.exp 1 * (((m+1).factorial : ℝ)⁻¹)) Filter.atTop (nhds (Real.exp 1 * 0)) := by
      apply Filter.Tendsto.const_mul
      have hfacNat : Filter.Tendsto (fun m : ℕ => (m + 1).factorial) Filter.atTop Filter.atTop :=
        factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
      have hfacReal : Filter.Tendsto (fun m : ℕ => ((m + 1).factorial : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.comp hfacNat
      exact tendsto_inv_atTop_zero.comp hfacReal
    simpa using ht

noncomputable def Eodd (m : ℕ) : ℝ := (A340738 (2*m+1) : ℝ) * Real.exp 1 - (A340737 (2*m+1) : ℝ)

lemma Eodd_zero : Eodd 0 = S 0 := by
  norm_num [Eodd, A340737, A340738, S_zero]

lemma Eodd_one : Eodd 1 = S 1 := by
  norm_num [Eodd, A340737, A340738, S_one]

lemma Eodd_recurrence (m : ℕ) : Eodd (m+2) = (4*m+10 : ℝ) * Eodd (m+1) + Eodd m := by
  unfold Eodd
  rw [show 2*(m+2)+1 = 2*m+5 by ring, show 2*(m+1)+1 = 2*m+3 by ring]
  rw [A_odd_recurrence m, B_odd_recurrence m]
  norm_num
  ring

lemma Eodd_eq_S (m : ℕ) : Eodd m = S m := by
  induction m using Nat.twoStepInduction with
  | zero => exact Eodd_zero
  | one => exact Eodd_one
  | more m h0 h1 =>
      rw [Eodd_recurrence m, S_recurrence m, h0, h1]


lemma S_abs_bound (m : ℕ) : |S m| ≤ Real.exp 1 * (((m+1).factorial : ℝ)⁻¹) := by
  have hK0 := K_nonneg (m+1)
  have hK1 := K_le_exp (m+1)
  unfold S
  have hfacpos : 0 < ((m+1).factorial : ℝ) := by positivity
  rw [abs_div, abs_mul, abs_pow]
  norm_num
  rw [abs_of_nonneg hK0]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hK1 (inv_nonneg.mpr hfacpos.le)

lemma Eodd_abs_bound (m : ℕ) : |Eodd m| ≤ Real.exp 1 * (((m+1).factorial : ℝ)⁻¹) := by
  rw [Eodd_eq_S]
  exact S_abs_bound m

lemma Eodd_tendsto_zero : Filter.Tendsto Eodd Filter.atTop (nhds 0) := by
  exact S_tendsto_zero.congr (fun m => (Eodd_eq_S m).symm)

lemma odd_ratio_tendsto : Filter.Tendsto (fun m : ℕ => (A340737 (2*m+1) : ℝ) / (A340738 (2*m+1) : ℝ)) Filter.atTop (nhds (Real.exp 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have hbound : ∀ m, |(A340737 (2*m+1) : ℝ) / (A340738 (2*m+1) : ℝ) - Real.exp 1| ≤ |Eodd m| := by
    intro m
    have hposNat := B_odd_pos m
    have hqpos : 0 < (A340738 (2*m+1) : ℝ) := by exact_mod_cast hposNat
    have hqge : 1 ≤ (A340738 (2*m+1) : ℝ) := by exact_mod_cast hposNat
    have hcalc : (A340737 (2*m+1) : ℝ) / (A340738 (2*m+1) : ℝ) - Real.exp 1 = - Eodd m / (A340738 (2*m+1) : ℝ) := by
      unfold Eodd
      field_simp [hqpos.ne']
      ring
    rw [hcalc]
    rw [abs_div, abs_neg]
    have hdivle : |Eodd m| / (A340738 (2*m+1) : ℝ) ≤ |Eodd m| / 1 := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hqge
    simpa using hdivle
  refine squeeze_zero (fun m => abs_nonneg _) hbound ?_
  simpa [Function.comp_def] using (tendsto_zero_iff_abs_tendsto_zero Eodd).1 Eodd_tendsto_zero

lemma inv_factorial_tendsto_zero : Filter.Tendsto (fun m : ℕ => (((m).factorial : ℝ)⁻¹)) Filter.atTop (nhds 0) := by
  have hfacReal : Filter.Tendsto (fun m : ℕ => ((m).factorial : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop
  exact tendsto_inv_atTop_zero.comp hfacReal

lemma lin_Eodd_tendsto_zero : Filter.Tendsto (fun m : ℕ => ((2*m+3 : ℕ) : ℝ) * Eodd m) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hbound : ∀ m : ℕ, |((2*m+3 : ℕ) : ℝ) * Eodd m| ≤ (3 * Real.exp 1) * (((m).factorial : ℝ)⁻¹) := by
    intro m
    have hb := Eodd_abs_bound m
    have hfacpos : 0 < ((m+1).factorial : ℝ) := by positivity
    have hmfacpos : 0 < ((m).factorial : ℝ) := by positivity
    have hcpos : 0 ≤ ((2*m+3 : ℕ) : ℝ) := by positivity
    rw [abs_mul, abs_of_nonneg hcpos]
    calc
      ((2*m+3 : ℕ) : ℝ) * |Eodd m| ≤ ((2*m+3 : ℕ) : ℝ) * (Real.exp 1 * (((m+1).factorial : ℝ)⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hb hcpos
      _ ≤ (3 * Real.exp 1) * (((m).factorial : ℝ)⁻¹) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        field_simp [hmfacpos.ne', (show ((m+1 : ℕ) : ℝ) ≠ 0 by positivity)]
        have hexp_nonneg : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
        norm_num at *
        nlinarith
  refine squeeze_zero (fun m => abs_nonneg _) hbound ?_
  have ht := (tendsto_const_nhds (x := 3 * Real.exp 1)).mul inv_factorial_tendsto_zero
  simpa using ht

noncomputable def Eeven (m : ℕ) : ℝ := (A340738 (2*m+2) : ℝ) * Real.exp 1 - (A340737 (2*m+2) : ℝ)

lemma Eeven_shift_formula (m : ℕ) : 2 * Eeven (m+1) = (2*m+5 : ℝ) * Eodd (m+1) + Eodd m := by
  unfold Eeven Eodd
  have hA := A_even_bridge (m+1)
  have hB := B_even_bridge (m+1)
  rw [show 2*(m+1)+2 = 2*m+4 by ring] at hA hB
  rw [show 2*(m+1)+1 = 2*m+3 by ring] at hA hB
  rw [show 2*(m+1)+3 = 2*m+5 by ring] at hA hB
  rw [show prevA (m+1) = A340737 (2*m+1) by simp [prevA]; congr <;> omega] at hA
  rw [show prevB (m+1) = A340738 (2*m+1) by simp [prevB]; congr <;> omega] at hB
  -- real-cast versions
  have hAr : (2 : ℝ) * (A340737 (2*m+4) : ℝ) = (2*m+5 : ℝ) * (A340737 (2*m+3) : ℝ) + (A340737 (2*m+1) : ℝ) := by exact_mod_cast hA
  have hBr : (2 : ℝ) * (A340738 (2*m+4) : ℝ) = (2*m+5 : ℝ) * (A340738 (2*m+3) : ℝ) + (A340738 (2*m+1) : ℝ) := by exact_mod_cast hB
  rw [show 2*(m+1)+2 = 2*m+4 by ring, show 2*(m+1)+1 = 2*m+3 by ring]
  ring_nf
  ring_nf at hAr hBr
  have hBrE : ↑(A340738 (4 + m * 2)) * Real.exp 1 * 2 =
      Real.exp 1 * ↑m * ↑(A340738 (3 + m * 2)) * 2 +
        Real.exp 1 * ↑(A340738 (3 + m * 2)) * 5 +
        Real.exp 1 * ↑(A340738 (1 + m * 2)) := by
    calc
      ↑(A340738 (4 + m * 2)) * Real.exp 1 * 2 = Real.exp 1 * (↑(A340738 (4 + m * 2)) * 2) := by ring
      _ = Real.exp 1 * (↑m * ↑(A340738 (3 + m * 2)) * 2 + ↑(A340738 (3 + m * 2)) * 5 + ↑(A340738 (1 + m * 2))) := by rw [hBr]
      _ = Real.exp 1 * ↑m * ↑(A340738 (3 + m * 2)) * 2 +
        Real.exp 1 * ↑(A340738 (3 + m * 2)) * 5 +
        Real.exp 1 * ↑(A340738 (1 + m * 2)) := by ring
  nlinarith [hAr, hBrE]


lemma prevB_pos (m : ℕ) : 0 < prevB m := by
  by_cases hm : m = 0
  · simp [prevB, hm]
  · have hpos := B_odd_pos (m-1)
    have hidx : 2 * (m - 1) + 1 = 2*m - 1 := by omega
    simp [prevB, hm]
    simpa [hidx] using hpos

lemma B_even_pos (m : ℕ) : 0 < A340738 (2*m+2) := by
  have h := B_even_bridge m
  have hrhs : 0 < (2*m+3) * A340738 (2*m+1) + prevB m := by
    have hodd := B_odd_pos m
    have hp := prevB_pos m
    positivity
  have htwo : 0 < 2 * A340738 (2*m+2) := by
    rw [h]
    exact hrhs
  omega

lemma Eeven_tendsto_zero : Filter.Tendsto Eeven Filter.atTop (nhds 0) := by
  apply (Filter.tendsto_add_atTop_iff_nat (f := Eeven) 1).1
  have hlin_shift : Filter.Tendsto (fun m : ℕ => ((2*(m+1)+3 : ℕ) : ℝ) * Eodd (m+1)) Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => ((2*k+3 : ℕ) : ℝ) * Eodd k) 1).2 lin_Eodd_tendsto_zero
  have hsum : Filter.Tendsto (fun m : ℕ => ((2*m+5 : ℕ) : ℝ) * Eodd (m+1) + Eodd m) Filter.atTop (nhds 0) := by
    have hlin' : Filter.Tendsto (fun m : ℕ => ((2*m+5 : ℕ) : ℝ) * Eodd (m+1)) Filter.atTop (nhds 0) := by
      refine hlin_shift.congr (fun m => ?_)
      congr 1
    simpa using hlin'.add Eodd_tendsto_zero
  have hhalf : Filter.Tendsto (fun m : ℕ => (2:ℝ)⁻¹ * (((2*m+5 : ℕ) : ℝ) * Eodd (m+1) + Eodd m)) Filter.atTop (nhds 0) := by
    simpa using hsum.const_mul ((2:ℝ)⁻¹)
  refine hhalf.congr (fun m => ?_)
  have hf := Eeven_shift_formula m
  norm_num
  nlinarith [hf]

lemma even_ratio_tendsto : Filter.Tendsto (fun m : ℕ => (A340737 (2*m+2) : ℝ) / (A340738 (2*m+2) : ℝ)) Filter.atTop (nhds (Real.exp 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have hbound : ∀ m, |(A340737 (2*m+2) : ℝ) / (A340738 (2*m+2) : ℝ) - Real.exp 1| ≤ |Eeven m| := by
    intro m
    have hposNat := B_even_pos m
    have hqpos : 0 < (A340738 (2*m+2) : ℝ) := by exact_mod_cast hposNat
    have hqge : 1 ≤ (A340738 (2*m+2) : ℝ) := by exact_mod_cast hposNat
    have hcalc : (A340737 (2*m+2) : ℝ) / (A340738 (2*m+2) : ℝ) - Real.exp 1 = - Eeven m / (A340738 (2*m+2) : ℝ) := by
      unfold Eeven
      field_simp [hqpos.ne']
      ring
    rw [hcalc, abs_div, abs_neg]
    have hdivle : |Eeven m| / (A340738 (2*m+2) : ℝ) ≤ |Eeven m| / 1 := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hqge
    simpa using hdivle
  refine squeeze_zero (fun m => abs_nonneg _) hbound ?_
  simpa [Function.comp_def] using (tendsto_zero_iff_abs_tendsto_zero Eeven).1 Eeven_tendsto_zero

theorem tendsto_of_odd_even {f : ℕ → ℝ} {a : ℝ}
    (hodd : Filter.Tendsto (fun m : ℕ => f (2*m+1)) Filter.atTop (nhds a))
    (heven : Filter.Tendsto (fun m : ℕ => f (2*m+2)) Filter.atTop (nhds a)) :
    Filter.Tendsto f Filter.atTop (nhds a) := by
  rw [Metric.tendsto_atTop] at hodd heven ⊢
  intro ε hε
  rcases hodd ε hε with ⟨No, hNo⟩
  rcases heven ε hε with ⟨Ne, hNe⟩
  refine ⟨max (2*No+1) (2*Ne+2), ?_⟩
  intro n hn
  by_cases hpar : n % 2 = 0
  · let m := n / 2 - 1
    have hnpos : 0 < n := by
      have : 2*Ne+2 ≤ n := le_trans (le_max_right _ _) hn
      omega
    have hnform : n = 2*(n/2 - 1)+2 := by omega
    rw [hnform]
    apply hNe
    have : 2*Ne+2 ≤ n := le_trans (le_max_right _ _) hn
    omega
  · let m := n / 2
    have hnform : n = 2*(n/2)+1 := by omega
    rw [hnform]

    apply hNo
    have : 2*No+1 ≤ n := le_trans (le_max_left _ _) hn
    omega
theorem final_test :
  Filter.Tendsto (fun n : ℕ => (A340737 n : ℝ) / (A340738 n : ℝ)) Filter.atTop (nhds (Real.exp 1)) := by
  exact tendsto_of_odd_even odd_ratio_tendsto even_ratio_tendsto

