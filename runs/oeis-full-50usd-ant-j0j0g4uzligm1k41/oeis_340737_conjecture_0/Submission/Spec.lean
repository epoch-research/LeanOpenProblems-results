import FormalConjectures.Util.ProblemImports

open Nat
open Real intervalIntegral MeasureTheory

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

namespace Aux340737

noncomputable def g (p q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => p
  | 2 => q
  | n' + 3 =>
    let n := n' + 3
    if n % 2 = 0 then
      (((n + 2) / 2 : ℕ) : ℤ) * g p q (n - 1) - g p q (n - 2) - (((n - 2) / 2 : ℕ) : ℤ) * g p q (n - 3)
    else
      2 * g p q (n - 1) + (n : ℤ) * g p q (n - 2)
termination_by n => n

lemma g0 (p q : ℤ) : g p q 0 = 0 := by rw [g]
lemma g1 (p q : ℤ) : g p q 1 = p := by rw [g]
lemma g2 (p q : ℤ) : g p q 2 = q := by rw [g]

lemma g_odd (p q : ℤ) (j : ℕ) :
    g p q (2*j+3) = 2 * g p q (2*j+2) + (2*(j:ℤ)+3) * g p q (2*j+1) := by
  rw [show 2*j+3 = (2*j) + 3 from rfl, g]; rw [if_neg (by omega)]
  simp only [show 2*j+3-1 = 2*j+2 from rfl, show 2*j+3-2 = 2*j+1 from rfl]; push_cast; ring

lemma g_even (p q : ℤ) (j : ℕ) :
    g p q (2*j+4) = ((j:ℤ)+3) * g p q (2*j+3) - g p q (2*j+2) - ((j:ℤ)+1) * g p q (2*j+1) := by
  rw [show 2*j+4 = (2*j+1) + 3 from rfl, g]; rw [if_pos (by omega)]
  simp only [show 2*j+1+3-1 = 2*j+3 from rfl, show 2*j+1+3-2 = 2*j+2 from rfl,
             show 2*j+1+3-3 = 2*j+1 from rfl]
  rw [show ((2*j+1+3+2)/2 : ℕ) = j+3 by omega, show ((2*j+2)/2 : ℕ) = j+1 by omega]; push_cast; ring

lemma g_rec2 (p q : ℤ) (k : ℕ) :
    g p q (2*k+5) = (4*(k:ℤ)+10) * g p q (2*k+3) + g p q (2*k+1) := by
  rw [show 2*k+5 = 2*(k+1)+3 by ring, g_odd, show 2*(k+1)+2 = 2*k+4 by ring, g_even,
      show 2*(k+1)+1 = 2*k+3 by ring, g_odd]
  push_cast; ring

lemma g_core (p q : ℤ) (hp : 0 ≤ p) (hpq : p ≤ q) :
    ∀ n, 0 ≤ g p q n ∧ g p q n ≤ g p q (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => refine ⟨by rw [g0], ?_⟩; rw [g0, g1]; exact hp
    | 1 => refine ⟨by rw [g1]; exact hp, ?_⟩; rw [g1, g2]; exact hpq
    | 2 =>
      refine ⟨by rw [g2]; linarith, ?_⟩
      rw [g2, show (2:ℕ)+1 = 2*0+3 from rfl, g_odd, g2, g1]; push_cast; linarith
    | m + 3 =>
      rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [show j + j + 3 = 2*j+3 by ring]
        have h1 := ih (2*j+1) (by omega)
        have h2 := ih (2*j+2) (by omega)
        rw [show 2*j+1+1 = 2*j+2 from rfl] at h1
        rw [show 2*j+2+1 = 2*j+3 from rfl] at h2
        have hnn : 0 ≤ g p q (2*j+3) := by
          rw [g_odd]
          have := mul_nonneg (by positivity : (0:ℤ) ≤ 2*(j:ℤ)+3) h1.1; linarith
        refine ⟨hnn, ?_⟩
        rw [show 2*j+3+1 = 2*j+4 from rfl, g_even, g_odd]
        nlinarith [h1.1, h2.1, Int.natCast_nonneg j,
          mul_nonneg (Int.natCast_nonneg j) h1.1, mul_nonneg (Int.natCast_nonneg j) h2.1]
      · rw [show 2*j+1+3 = 2*j+4 by ring]
        have h1 := ih (2*j+1) (by omega)
        have h2 := ih (2*j+2) (by omega)
        have h3 := ih (2*j+3) (by omega)
        rw [show 2*j+1+1 = 2*j+2 from rfl] at h1
        rw [show 2*j+2+1 = 2*j+3 from rfl] at h2
        rw [show 2*j+3+1 = 2*j+4 from rfl] at h3
        have hnn : 0 ≤ g p q (2*j+4) := by
          rw [g_even]
          nlinarith [h1.1, h2.1, h3.1, h1.2, h2.2, Int.natCast_nonneg j,
            mul_nonneg (Int.natCast_nonneg j) h3.1]
        refine ⟨hnn, ?_⟩
        rw [show 2*j+4+1 = 2*(j+1)+3 by ring, g_odd, show 2*(j+1)+2 = 2*j+4 by ring,
            show 2*(j+1)+1 = 2*j+3 by ring]
        nlinarith [hnn, h3.1, Int.natCast_nonneg j]

lemma g_nonneg (p q : ℤ) (hp : 0 ≤ p) (hpq : p ≤ q) (n : ℕ) : 0 ≤ g p q n :=
  (g_core p q hp hpq n).1

lemma g_mono (p q : ℤ) (hp : 0 ≤ p) (hpq : p ≤ q) : Monotone (g p q) :=
  monotone_nat_of_le_succ (fun n => (g_core p q hp hpq n).2)

/- ## The two OEIS sequences -/





lemma eqA : ∀ n, ((A340737 n : ℕ) : ℤ) = g 3 5 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [A340737, g]; norm_num
    | 1 => rw [A340737, g]; norm_num
    | 2 => rw [A340737, g]; norm_num
    | m + 3 =>
      rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [show j+j+3 = 2*j+3 by ring, show 2*j+3 = (2*j)+3 from rfl, A340737]
        simp only [show 2*j+3-1 = 2*j+2 from rfl, show 2*j+3-2 = 2*j+1 from rfl]
        rw [if_neg (by omega), g_odd]
        have e1 := ih (2*j+1) (by omega)
        have e2 := ih (2*j+2) (by omega)
        push_cast; rw [e1, e2]
      · rw [show 2*j+1+3 = 2*j+4 by ring]
        have e1 := ih (2*j+1) (by omega)
        have e2 := ih (2*j+2) (by omega)
        have e3 := ih (2*j+3) (by omega)
        rw [show 2*j+4 = (2*j+1)+3 from rfl, A340737]
        simp only [show 2*j+1+3-1 = 2*j+3 from rfl, show 2*j+1+3-2 = 2*j+2 from rfl,
                   show 2*j+1+3-3 = 2*j+1 from rfl]
        rw [if_pos (by omega)]
        have key : (Int.ofNat ((2*j+1+3+2)/2) * Int.ofNat (A340737 (2*j+3))
            - Int.ofNat (A340737 (2*j+2)) - Int.ofNat ((2*j+2)/2) * Int.ofNat (A340737 (2*j+1)))
            = g 3 5 (2*j+4) := by
          rw [g_even]; simp only [Int.ofNat_eq_natCast]
          rw [e1, e2, e3, show ((2*j+1+3+2)/2:ℕ) = j+3 by omega, show ((2*j+2)/2:ℕ)=j+1 by omega]
          push_cast; ring
        rw [key, Int.toNat_of_nonneg (g_nonneg 3 5 (by norm_num) (by norm_num) _)]

lemma eqB : ∀ n, ((A340738 n : ℕ) : ℤ) = g 1 2 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [A340738, g]; norm_num
    | 1 => rw [A340738, g]; norm_num
    | 2 => rw [A340738, g]; norm_num
    | m + 3 =>
      rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [show j+j+3 = 2*j+3 by ring, show 2*j+3 = (2*j)+3 from rfl, A340738]
        simp only [show 2*j+3-1 = 2*j+2 from rfl, show 2*j+3-2 = 2*j+1 from rfl]
        rw [if_neg (by omega), g_odd]
        have e1 := ih (2*j+1) (by omega)
        have e2 := ih (2*j+2) (by omega)
        push_cast; rw [e1, e2]
      · rw [show 2*j+1+3 = 2*j+4 by ring]
        have e1 := ih (2*j+1) (by omega)
        have e2 := ih (2*j+2) (by omega)
        have e3 := ih (2*j+3) (by omega)
        rw [show 2*j+4 = (2*j+1)+3 from rfl, A340738]
        simp only [show 2*j+1+3-1 = 2*j+3 from rfl, show 2*j+1+3-2 = 2*j+2 from rfl,
                   show 2*j+1+3-3 = 2*j+1 from rfl]
        rw [if_pos (by omega)]
        have key : (Int.ofNat ((2*j+1+3+2)/2) * Int.ofNat (A340738 (2*j+3))
            - Int.ofNat (A340738 (2*j+2)) - Int.ofNat ((2*j+2)/2) * Int.ofNat (A340738 (2*j+1)))
            = g 1 2 (2*j+4) := by
          rw [g_even]; simp only [Int.ofNat_eq_natCast]
          rw [e1, e2, e3, show ((2*j+1+3+2)/2:ℕ) = j+3 by omega, show ((2*j+2)/2:ℕ)=j+1 by omega]
          push_cast; ring
        rw [key, Int.toNat_of_nonneg (g_nonneg 1 2 (by norm_num) (by norm_num) _)]

/- ## Hermite integrals -/

noncomputable def J (m : ℕ) : ℝ := ∫ t in (0:ℝ)..1, (t^2 - t)^m * Real.exp t
noncomputable def W (m : ℕ) : ℝ := ∫ t in (0:ℝ)..1, (t^2 - t)^m * (2*t - 1) * Real.exp t

lemma hderivbase (t : ℝ) : HasDerivAt (fun t : ℝ => t^2 - t) (2*t - 1) t := by
  have h1 : HasDerivAt (fun t : ℝ => t^2) (2*t) t := by simpa using (hasDerivAt_pow 2 t)
  simpa using h1.sub (hasDerivAt_id t)

lemma factI (m : ℕ) : J (m+1) = -((m:ℝ)+1) * W m := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => (t^2 - t)^(m+1) * Real.exp t)
        (((m:ℝ)+1) * (t^2-t)^m * (2*t-1) * Real.exp t + (t^2-t)^(m+1) * Real.exp t) t := by
    intro t _
    have hp : HasDerivAt (fun t : ℝ => (t^2 - t)^(m+1)) (((m:ℝ)+1) * (t^2-t)^m * (2*t-1)) t := by
      simpa [Nat.add_sub_cancel, pow_succ] using (hderivbase t).pow (m+1)
    have := hp.mul (Real.hasDerivAt_exp t)
    convert this using 1
  have hint : IntervalIntegrable
      (fun t : ℝ => ((m:ℝ)+1) * (t^2-t)^m * (2*t-1) * Real.exp t + (t^2-t)^(m+1) * Real.exp t)
      volume 0 1 := by apply Continuous.intervalIntegrable; fun_prop
  have key := integral_eq_sub_of_hasDerivAt hderiv hint
  have hF1 : ((1:ℝ)^2 - 1)^(m+1) * Real.exp 1 = 0 := by norm_num
  have hF0 : ((0:ℝ)^2 - 0)^(m+1) * Real.exp 0 = 0 := by norm_num
  rw [hF1, hF0] at key
  simp only [sub_zero] at key
  rw [intervalIntegral.integral_add ?_ ?_] at key
  · have e1 : (∫ t in (0:ℝ)..1, ((m:ℝ)+1) * (t^2-t)^m * (2*t-1) * Real.exp t)
        = ((m:ℝ)+1) * W m := by
      rw [W, ← intervalIntegral.integral_const_mul]; congr 1; ext t; ring
    have e2 : (∫ t in (0:ℝ)..1, (t^2-t)^(m+1) * Real.exp t) = J (m+1) := rfl
    rw [e1, e2] at key; linarith
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

lemma factII (m : ℕ) : W (m+1) = -(4*(m:ℝ)+6)*J (m+1) - ((m:ℝ)+1)*J m := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => (t^2 - t)^(m+1) * (2*t-1) * Real.exp t)
        ((4*(m:ℝ)+6)*(t^2-t)^(m+1)*Real.exp t + ((m:ℝ)+1)*(t^2-t)^m*Real.exp t
          + (t^2-t)^(m+1)*(2*t-1)*Real.exp t) t := by
    intro t _
    have hp : HasDerivAt (fun t : ℝ => (t^2 - t)^(m+1)) (((m:ℝ)+1) * (t^2-t)^m * (2*t-1)) t := by
      simpa [Nat.add_sub_cancel, pow_succ] using (hderivbase t).pow (m+1)
    have hw : HasDerivAt (fun t : ℝ => 2*t - 1) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
    have h1 := (hp.mul hw).mul (Real.hasDerivAt_exp t)
    convert h1 using 1
    simp only [Pi.mul_apply]; ring
  have hint : IntervalIntegrable
      (fun t : ℝ => (4*(m:ℝ)+6)*(t^2-t)^(m+1)*Real.exp t + ((m:ℝ)+1)*(t^2-t)^m*Real.exp t
          + (t^2-t)^(m+1)*(2*t-1)*Real.exp t) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have key := integral_eq_sub_of_hasDerivAt hderiv hint
  have hG1 : ((1:ℝ)^2 - 1)^(m+1) * (2*1-1) * Real.exp 1 = 0 := by norm_num
  have hG0 : ((0:ℝ)^2 - 0)^(m+1) * (2*0-1) * Real.exp 0 = 0 := by norm_num
  rw [hG1, hG0] at key
  simp only [sub_zero] at key
  rw [intervalIntegral.integral_add ?_ ?_, intervalIntegral.integral_add ?_ ?_] at key
  · have e1 : (∫ t in (0:ℝ)..1, (4*(m:ℝ)+6)*(t^2-t)^(m+1)*Real.exp t) = (4*(m:ℝ)+6)*J (m+1) := by
      rw [J, ← intervalIntegral.integral_const_mul]; congr 1; ext t; ring
    have e2 : (∫ t in (0:ℝ)..1, ((m:ℝ)+1)*(t^2-t)^m*Real.exp t) = ((m:ℝ)+1)*J m := by
      rw [J, ← intervalIntegral.integral_const_mul]; congr 1; ext t; ring
    have e3 : (∫ t in (0:ℝ)..1, (t^2-t)^(m+1)*(2*t-1)*Real.exp t) = W (m+1) := rfl
    rw [e1, e2, e3] at key; linarith
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop

lemma Jrec (m : ℕ) :
    J (m+2) = (4*(m:ℝ)+6)*((m:ℝ)+2)*J (m+1) + ((m:ℝ)+1)*((m:ℝ)+2)*J m := by
  have hI := factI (m+1)
  have hII := factII m
  rw [hII] at hI
  push_cast at hI
  linear_combination hI

lemma J0 : J 0 = Real.exp 1 - 1 := by
  simp only [J, pow_zero, one_mul]
  rw [integral_exp, Real.exp_zero]

lemma J1 : J 1 = Real.exp 1 - 3 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => (t^2 - 3*t + 3) * Real.exp t) ((t^2 - t)*Real.exp t) t := by
    intro t _
    have h1 : HasDerivAt (fun t:ℝ=>t^2) (2*t) t := by simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun t:ℝ=>3*t) 3 t := by simpa using (hasDerivAt_id t).const_mul 3
    have hp : HasDerivAt (fun t:ℝ => t^2-3*t+3) (2*t-3) t := by
      simpa using (h1.sub h2).add_const 3
    have := hp.mul (Real.hasDerivAt_exp t)
    convert this using 1; ring
  have hint : IntervalIntegrable (fun t:ℝ => (t^2-t)*Real.exp t) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have key := integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [J, pow_one]
  rw [key, Real.exp_zero]; norm_num

lemma Jbound (m : ℕ) : |J m| ≤ Real.exp 1 * (1/4)^m := by
  have h : ∀ t ∈ Set.uIoc (0:ℝ) 1, ‖(t^2-t)^m * Real.exp t‖ ≤ Real.exp 1 * (1/4)^m := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    obtain ⟨h0, h1⟩ := ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_pos (Real.exp_pos t)]
    have habs : |t^2 - t| ≤ 1/4 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t - 1/2), mul_nonneg h0.le (sub_nonneg.mpr h1)]
    have hp : |t^2-t|^m ≤ (1/4)^m := pow_le_pow_left₀ (abs_nonneg _) habs m
    have he : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
    calc |t^2-t|^m * Real.exp t ≤ (1/4)^m * Real.exp 1 :=
            mul_le_mul hp he (Real.exp_pos t).le (by positivity)
      _ = Real.exp 1 * (1/4)^m := by ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const h
  rw [Real.norm_eq_abs] at hb
  simp only [show |(1:ℝ) - 0| = 1 by norm_num, mul_one] at hb
  exact hb

/- ## Connecting the odd subsequence to the integrals -/

noncomputable def Jf (m : ℕ) : ℝ := J m / (m.factorial : ℝ)

lemma Jf_rec (m : ℕ) : Jf (m+2) = (4*(m:ℝ)+6)*Jf (m+1) + Jf m := by
  simp only [Jf]
  have h := Jrec m
  have hm : (m.factorial:ℝ) ≠ 0 := by positivity
  have hm1 : ((m:ℝ)+1) ≠ 0 := by positivity
  have hm2 : ((m:ℝ)+2) ≠ 0 := by positivity
  have e1 : ((m+1).factorial:ℝ) = ((m:ℝ)+1)*(m.factorial:ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have e2 : ((m+2).factorial:ℝ) = ((m:ℝ)+2)*((m+1).factorial:ℝ) := by
    rw [show m+2 = (m+1)+1 from rfl, Nat.factorial_succ]; push_cast; ring
  rw [e2, e1, h]
  field_simp

noncomputable def rho (k : ℕ) : ℝ := (g 3 5 (2*k+1) : ℝ) - Real.exp 1 * (g 1 2 (2*k+1) : ℝ)

lemma rho_rec (k : ℕ) : rho (k+2) = (4*(k:ℝ)+10)*rho (k+1) + rho k := by
  simp only [rho]
  rw [show 2*(k+2)+1 = 2*k+5 by ring, show 2*(k+1)+1 = 2*k+3 by ring,
      g_rec2 3 5 k, g_rec2 1 2 k]
  push_cast; ring

lemma rho0 : rho 0 = 3 - Real.exp 1 := by
  simp only [rho]; rw [show 2*0+1 = 1 from rfl, g1, g1]; push_cast; ring

lemma rho1 : rho 1 = 19 - 7 * Real.exp 1 := by
  simp only [rho]
  have e35 : g 3 5 3 = 19 := by
    have h := g_odd 3 5 0
    simp only [show 2*0+3=3 from rfl, show 2*0+2=2 from rfl, show 2*0+1=1 from rfl] at h
    rw [g1, g2] at h; rw [h]; norm_num
  have e12 : g 1 2 3 = 7 := by
    have h := g_odd 1 2 0
    simp only [show 2*0+3=3 from rfl, show 2*0+2=2 from rfl, show 2*0+1=1 from rfl] at h
    rw [g1, g2] at h; rw [h]; norm_num
  rw [show 2*1+1 = 3 from rfl, e35, e12]; push_cast; ring

lemma rho_eq : ∀ k, rho k = - Jf (k+1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      rw [rho0]
      show (3:ℝ) - Real.exp 1 = - Jf 1
      simp only [Jf]
      rw [J1, show ((1:ℕ).factorial : ℝ) = 1 by norm_num [Nat.factorial]]
      ring
    | 1 =>
      rw [rho1]
      have hJ2 : J 2 = 14 * Real.exp 1 - 38 := by
        have h := Jrec 0
        simp only [show (0:ℕ)+2 = 2 from rfl, show (0:ℕ)+1 = 1 from rfl] at h
        rw [J1, J0] at h; push_cast at h; linarith
      show (19 : ℝ) - 7 * Real.exp 1 = - Jf 2
      simp only [Jf, hJ2]
      rw [show ((2:ℕ).factorial : ℝ) = 2 by norm_num [Nat.factorial]]
      ring
    | k+2 =>
      have i1 := ih (k+1) (by omega)
      have i2 := ih k (by omega)
      rw [show (k+1)+1 = k+2 from rfl] at i1
      have hjf := Jf_rec (k+1)
      simp only [show (k+1)+2 = k+3 from rfl, show (k+1)+1 = k+2 from rfl] at hjf
      push_cast at hjf
      rw [rho_rec, i1, i2, show (k+2)+1 = k+3 from rfl]
      linear_combination hjf

lemma rho_bound (k : ℕ) : |rho k| ≤ Real.exp 1 * (1/4)^(k+1) := by
  rw [rho_eq, abs_neg]
  have hF : (1:ℝ) ≤ (((k+1).factorial):ℝ) := by exact_mod_cast (k+1).factorial_pos
  have hpos : (0:ℝ) < (((k+1).factorial):ℝ) := by exact_mod_cast (k+1).factorial_pos
  simp only [Jf, abs_div, abs_of_pos hpos]
  exact (div_le_self (abs_nonneg _) hF).trans (Jbound (k+1))

/- ## Error bounds and convergence -/

lemma err_odd (k : ℕ) :
    |((g 3 5 (2*k+1) : ℤ):ℝ) - Real.exp 1 * ((g 1 2 (2*k+1) : ℤ):ℝ)|
      ≤ ((↑(2*k+1):ℝ)+1) * Real.exp 1 * (1/2)^(2*k+1) := by
  have hr : |((g 3 5 (2*k+1) : ℤ):ℝ) - Real.exp 1 * ((g 1 2 (2*k+1) : ℤ):ℝ)| = |rho k| := by
    rw [rho]
  rw [hr]
  refine (rho_bound k).trans ?_
  have hP : (0:ℝ) < (1/2:ℝ)^(2*k+1) := by positivity
  have hp4 : (1/4:ℝ)^(k+1) = (1/2)^(2*k+1) * (1/2) := by
    rw [show (1/4:ℝ) = (1/2)^2 by norm_num, ← pow_mul, show 2*(k+1) = (2*k+1)+1 by ring, pow_succ]
  rw [hp4]
  push_cast
  nlinarith [hP, Real.exp_pos 1, Nat.cast_nonneg (α := ℝ) k,
    mul_pos (Real.exp_pos 1) hP,
    mul_nonneg (mul_nonneg (Real.exp_pos 1).le hP.le) (Nat.cast_nonneg (α := ℝ) k)]

lemma err_even (j : ℕ) :
    |((g 3 5 (2*j+2) : ℤ):ℝ) - Real.exp 1 * ((g 1 2 (2*j+2) : ℤ):ℝ)|
      ≤ ((↑(2*j+2):ℝ)+1) * Real.exp 1 * (1/2)^(2*j+2) := by
  have hrel : ∀ (p q : ℤ), ((g p q (2*j+3):ℤ):ℝ)
      = 2*((g p q (2*j+2):ℤ):ℝ) + (2*(j:ℝ)+3)*((g p q (2*j+1):ℤ):ℝ) := by
    intro p q; have h := g_odd p q j; exact_mod_cast h
  have hA := hrel 3 5
  have hB := hrel 1 2
  have key : ((g 3 5 (2*j+2):ℤ):ℝ) - Real.exp 1 * ((g 1 2 (2*j+2):ℤ):ℝ)
      = (rho (j+1) - (2*(j:ℝ)+3)*rho j)/2 := by
    simp only [rho]
    rw [show 2*(j+1)+1 = 2*j+3 by ring]
    linear_combination (-(1/2 : ℝ)) * hA + (Real.exp 1 / 2) * hB
  rw [key, abs_div, show |(2:ℝ)| = 2 by norm_num]
  have h1 := rho_bound (j+1)
  have h2 := rho_bound j
  have habs : |rho (j+1) - (2*(j:ℝ)+3)*rho j| ≤ |rho (j+1)| + (2*(j:ℝ)+3)*|rho j| := by
    calc |rho (j+1) - (2*(j:ℝ)+3)*rho j| ≤ |rho (j+1)| + |(2*(j:ℝ)+3)*rho j| := abs_sub _ _
      _ = |rho (j+1)| + (2*(j:ℝ)+3)*|rho j| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*(j:ℝ)+3)]
  have hP : (0:ℝ) < (1/2:ℝ)^(2*j+2) := by positivity
  have hp1 : (1/4:ℝ)^(j+1) = (1/2)^(2*j+2) := by
    rw [show (2*j+2) = 2*(j+1) by ring, pow_mul]; norm_num
  have hp2 : (1/4:ℝ)^(j+2) = (1/2)^(2*j+2) * (1/4) := by
    rw [show (2*j+2) = 2*(j+1) by ring, pow_mul, show j+2 = (j+1)+1 by ring, pow_succ]; norm_num
  rw [show ((j:ℕ)+1)+1 = j+2 from rfl] at h1
  rw [hp1] at h2
  rw [hp2] at h1
  push_cast
  -- goal: |rho(j+1) - (2j+3) rho j| / 2 ≤ (2j+3) * e * (1/2)^(2j+2)
  nlinarith [habs, h1, h2, hP, Real.exp_pos 1, Nat.cast_nonneg (α := ℝ) j,
    abs_nonneg (rho (j+1)), abs_nonneg (rho j),
    mul_nonneg (mul_nonneg (Real.exp_pos 1).le hP.le) (Nat.cast_nonneg (α := ℝ) j),
    mul_pos (Real.exp_pos 1) hP,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (abs_nonneg (rho j))]

lemma castA (n : ℕ) : ((A340737 n : ℕ) : ℝ) = ((g 3 5 n : ℤ) : ℝ) := by
  have h := eqA n; exact_mod_cast h
lemma castB (n : ℕ) : ((A340738 n : ℕ) : ℝ) = ((g 1 2 n : ℤ) : ℝ) := by
  have h := eqB n; exact_mod_cast h

lemma Bge1 (n : ℕ) (hn : 1 ≤ n) : (1:ℝ) ≤ (A340738 n : ℝ) := by
  rw [castB]
  have hmono : g 1 2 1 ≤ g 1 2 n := g_mono 1 2 (by norm_num) (by norm_num) hn
  rw [g1] at hmono
  exact_mod_cast hmono

lemma err_bound (n : ℕ) (hn : 1 ≤ n) :
    |((g 3 5 n : ℤ):ℝ) - Real.exp 1 * ((g 1 2 n : ℤ):ℝ)| ≤ ((n:ℝ)+1)*Real.exp 1*(1/2)^n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨k, rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j+1 := ⟨m-1, by omega⟩
    rw [show (j+1)+(j+1) = 2*j+2 by ring]; exact err_even j
  · exact err_odd k

end Aux340737

open Aux340737

/--
oeis_340737_conjecture_0: The convergence is conjectured.
Formally, the sequence of fractions $\frac{\mathrm{A}340737(n)}{\mathrm{A}340738(n)}$ converges to $e$.
-/
theorem oeis_340737_conjecture_0 :
  Filter.Tendsto (fun n : ℕ => (A340737 n : ℝ) / (A340738 n : ℝ)) Filter.atTop (nhds (Real.exp 1)) :=
by
  rw [← tendsto_sub_nhds_zero_iff]
  have hg : Filter.Tendsto (fun n:ℕ => ((n:ℝ)+1)*Real.exp 1*(1/2)^n) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n:ℕ => (n:ℝ)*(1/2:ℝ)^n) Filter.atTop (nhds 0) :=
      tendsto_self_mul_const_pow_of_lt_one (by norm_num) (by norm_num)
    have h2 : Filter.Tendsto (fun n:ℕ => (1/2:ℝ)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h3 := (h1.add h2).mul_const (Real.exp 1)
    simp only [zero_add, zero_mul] at h3
    refine h3.congr (fun n => ?_); ring
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  have hB := Bge1 n hn
  have hBpos : (0:ℝ) < (A340738 n : ℝ) := lt_of_lt_of_le one_pos hB
  rw [div_sub' (ne_of_gt hBpos), abs_div, abs_of_pos hBpos]
  refine (div_le_self (abs_nonneg _) hB).trans ?_
  rw [castA, castB]
  convert err_bound n hn using 2
  ring

