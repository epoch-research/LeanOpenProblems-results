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

namespace OEIS340738

open Real intervalIntegral MeasureTheory

/- ### The integral `I n = ∫₀¹ (x(1-x))ⁿ eˣ dx` and its recurrence -/

noncomputable def I (n : ℕ) : ℝ := ∫ x in (0:ℝ)..1, (x*(1-x))^n * Real.exp x

lemma cont_int (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => (x*(1-x))^k * Real.exp x) volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

lemma Hderiv (j : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (x*(1-x))^(j+2) - (j+2 : ℝ)*((1-2*x)*(x*(1-x))^(j+1)))
      ( ((j+2 : ℝ) * (x*(1-x))^(j+1) * (1-2*x))
        - (j+2 : ℝ) * ((-2)*(x*(1-x))^(j+1) + (1-2*x)*((j+1 : ℝ)*(x*(1-x))^j*(1-2*x))) ) x := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun x : ℝ => (1:ℝ)-x) (-1) x := by
    simpa using (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
  have ha : HasDerivAt (fun x : ℝ => x*(1-x)) (1-2*x) x := by
    have := h1.mul h2
    convert this using 1
    ring
  have hb : HasDerivAt (fun x : ℝ => (1:ℝ)-2*x) (-2) x := by
    simpa using (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_const x (2:ℝ)).mul (hasDerivAt_id x))
  have hp2 : HasDerivAt (fun x : ℝ => (x*(1-x))^(j+2)) ((j+2 : ℝ) * (x*(1-x))^(j+1) * (1-2*x)) x := by
    have := ha.pow (j+2)
    simpa using this
  have hp1 : HasDerivAt (fun x : ℝ => (x*(1-x))^(j+1)) ((j+1 : ℝ) * (x*(1-x))^j * (1-2*x)) x := by
    have := ha.pow (j+1)
    simpa using this
  have hmid : HasDerivAt (fun x : ℝ => (1-2*x)*(x*(1-x))^(j+1))
      ((-2)*(x*(1-x))^(j+1) + (1-2*x)*((j+1 : ℝ)*(x*(1-x))^j*(1-2*x))) x := hb.mul hp1
  exact hp2.sub (hmid.const_mul (j+2 : ℝ))

lemma I_zero : I 0 = Real.exp 1 - 1 := by
  simp only [I, pow_zero, one_mul]
  rw [integral_exp]; simp

lemma I_one : I 1 = 3 - Real.exp 1 := by
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (-x^2+3*x-3) * Real.exp x)
      ((x*(1-x))^1 * Real.exp x) x := by
    intro x
    have hpoly : HasDerivAt (fun x : ℝ => -x^2+3*x-3) (-2*x+3) x := by
      have h1 : HasDerivAt (fun x : ℝ => x^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
      have h2 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
      have := (h1.neg.add ((hasDerivAt_const x (3:ℝ)).mul h2)).sub (hasDerivAt_const x (3:ℝ))
      convert this using 1; ring
    have hd := hpoly.mul (Real.hasDerivAt_exp x)
    convert hd using 1; ring
  have := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun x _ => hF x)
    (by apply Continuous.intervalIntegrable; fun_prop)
  simp only [I]
  rw [this]; simp; ring

lemma I_nonneg (n : ℕ) : 0 ≤ I n := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  simp only [Set.mem_Icc] at hu
  apply mul_nonneg
  · exact pow_nonneg (by nlinarith [hu.1, hu.2]) n
  · exact (Real.exp_pos u).le

lemma I_le (n : ℕ) : I n ≤ Real.exp 1 - 1 := by
  have : I n ≤ ∫ x in (0:ℝ)..1, Real.exp x := by
    apply integral_mono_on (by norm_num) (cont_int n)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro x hx
    simp only [Set.mem_Icc] at hx
    have h1 : (x*(1-x))^n ≤ 1 := by
      apply pow_le_one₀
      · nlinarith [hx.1, hx.2]
      · nlinarith [hx.1, hx.2]
    have h2 : (0:ℝ) ≤ Real.exp x := (Real.exp_pos x).le
    calc (x*(1-x))^n * Real.exp x ≤ 1 * Real.exp x := by nlinarith [h2]
      _ = Real.exp x := one_mul _
  rw [integral_exp] at this; simpa using this

lemma I_rec (j : ℕ) :
    I (j+2) = -2*(j+2:ℝ)*(2*(j:ℝ)+3) * I (j+1) + (j+2:ℝ)*((j:ℝ)+1) * I j := by
  have hF : ∀ x : ℝ, HasDerivAt
      (fun x : ℝ => ((x*(1-x))^(j+2) - (j+2 : ℝ)*((1-2*x)*(x*(1-x))^(j+1))) * Real.exp x)
      (((x*(1-x))^(j+2) + 2*(j+2 : ℝ)*(2*(j:ℝ)+3)*(x*(1-x))^(j+1)
          - (j+2 : ℝ)*((j:ℝ)+1)*(x*(1-x))^j) * Real.exp x) x := by
    intro x
    have hd := (Hderiv j x).mul (Real.hasDerivAt_exp x)
    convert hd using 1
    have e2 : (x*(1-x))^(j+2) = (x*(1-x))^j * (x*(1-x))^2 := by rw [← pow_add]
    have e1 : (x*(1-x))^(j+1) = (x*(1-x))^j * (x*(1-x)) := by rw [← pow_succ]
    rw [e2, e1]; ring
  have hint : IntervalIntegrable
      (fun x : ℝ => ((x*(1-x))^(j+2) + 2*(j+2 : ℝ)*(2*(j:ℝ)+3)*(x*(1-x))^(j+1)
          - (j+2 : ℝ)*((j:ℝ)+1)*(x*(1-x))^j) * Real.exp x) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have key := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun x _ => hF x) hint
  have hz2 : (j:ℕ)+2 ≠ 0 := by omega
  have hz1 : (j:ℕ)+1 ≠ 0 := by omega
  norm_num [zero_pow hz2, zero_pow hz1] at key
  have hsplit : (fun x : ℝ => ((x*(1-x))^(j+2) + 2*(j+2 : ℝ)*(2*(j:ℝ)+3)*(x*(1-x))^(j+1)
          - (j+2 : ℝ)*((j:ℝ)+1)*(x*(1-x))^j) * Real.exp x)
      = (fun x : ℝ => (x*(1-x))^(j+2) * Real.exp x
          + (2*(j+2 : ℝ)*(2*(j:ℝ)+3)) * ((x*(1-x))^(j+1) * Real.exp x)
          + (-((j+2 : ℝ)*((j:ℝ)+1))) * ((x*(1-x))^j * Real.exp x)) := by
    funext x; ring
  rw [hsplit] at key
  rw [integral_add ((cont_int (j+2)).add (((cont_int (j+1)).const_mul _)))
        ((cont_int j).const_mul _),
      integral_add (cont_int (j+2)) ((cont_int (j+1)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at key
  simp only [I] at *
  linarith [key]

/- ### The sequence `T n = (-1)ⁿ / (n+1)! · I(n+1)` -/

noncomputable def T (n : ℕ) : ℝ := (-1)^n / (Nat.factorial (n+1) : ℝ) * I (n+1)

lemma fact_pos (n : ℕ) : (0:ℝ) < (Nat.factorial n : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

lemma T_rec (n : ℕ) : T (n+2) = (4*(n:ℝ)+10) * T (n+1) + T n := by
  have hI := I_rec (n+1)
  rw [show (n+1)+2 = n+3 from rfl, show (n+1)+1 = n+2 from rfl] at hI
  push_cast at hI
  simp only [T]
  rw [show n+2+1 = n+3 from rfl, show n+1+1 = n+2 from rfl]
  have f3 : (Nat.factorial (n+3):ℝ) = ((n:ℝ)+3)*(((n:ℝ)+2)*((Nat.factorial (n+1)):ℝ)) := by
    rw [show n+3 = (n+2)+1 from rfl, Nat.factorial_succ, show n+2 = (n+1)+1 from rfl,
        Nat.factorial_succ]
    push_cast; ring
  have f2 : (Nat.factorial (n+2):ℝ) = ((n:ℝ)+2)*((Nat.factorial (n+1)):ℝ) := by
    rw [show n+2 = (n+1)+1 from rfl, Nat.factorial_succ]; push_cast; ring
  have hp1 : (0:ℝ) < (Nat.factorial (n+1):ℝ) := fact_pos _
  rw [hI, f3, f2, pow_succ, pow_succ]
  field_simp
  ring

lemma T_zero : T 0 = 3 - Real.exp 1 := by
  have h : I (0+1) = 3 - Real.exp 1 := I_one
  simp only [T]; rw [h]; norm_num

lemma T_one : T 1 = 19 - 7 * Real.exp 1 := by
  have hI2 : I (1+1) = 14 * Real.exp 1 - 38 := by
    have h := I_rec 0
    rw [show (0:ℕ)+2 = 1+1 from rfl, show (0:ℕ)+1 = 1 from rfl] at h
    rw [I_one, I_zero] at h
    rw [h]; push_cast; ring
  simp only [T]; rw [hI2]
  norm_num; ring

lemma T_abs_le (n : ℕ) : |T n| ≤ (Real.exp 1 - 1) / (Nat.factorial (n+1) : ℝ) := by
  simp only [T]
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, one_div,
      abs_of_nonneg (le_of_lt (fact_pos (n+1))), abs_of_nonneg (I_nonneg (n+1))]
  rw [inv_mul_eq_div, div_le_div_iff_of_pos_right (fact_pos (n+1))]
  exact I_le (n+1)

/- ### Recurrences for the base sequences -/

section generic
variable {f : ℕ → ℕ}
variable (hodd : ∀ k, f (2*k+3) = 2 * f (2*k+2) + (2*k+3) * f (2*k+1))
variable (heven : ∀ k, f (2*k+4) = (k+3) * f (2*k+3) - f (2*k+2) - (k+1) * f (2*k+1))

include hodd heven in
lemma even_pos (k : ℕ) :
    f (2*k+4) = (2*k+5) * f (2*k+2) + 2*(k+2)^2 * f (2*k+1) := by
  have ho := hodd k
  have he := heven k
  set p := f (2*k+2) with hp
  set q := f (2*k+1) with hq
  rw [ho] at he
  rw [he]
  have key : (k+3)*(2*p+(2*k+3)*q) = (2*k+5)*p + 2*(k+2)^2*q + p + (k+1)*q := by ring
  omega

include hodd heven in
lemma subseq (n : ℕ) :
    f (2*n+5) = (4*n+10) * f (2*n+3) + f (2*n+1) := by
  have ho1 : f (2*n+5) = 2 * f (2*n+4) + (2*n+5) * f (2*n+3) := by
    have h := hodd (n+1)
    rw [show 2*(n+1)+3 = 2*n+5 from by ring, show 2*(n+1)+2 = 2*n+4 from by ring,
        show 2*(n+1)+1 = 2*n+3 from by ring] at h
    exact h
  have hep : f (2*n+4) = (2*n+5) * f (2*n+2) + 2*(n+2)^2 * f (2*n+1) := even_pos hodd heven n
  have ho2 : f (2*n+3) = 2 * f (2*n+2) + (2*n+3) * f (2*n+1) := hodd n
  rw [ho1, hep, ho2]
  ring

include hodd heven in
lemma pos_pair (h1 : 1 ≤ f 1) (h2 : 1 ≤ f 2) :
    ∀ n, (n+1 ≤ f (2*n+1)) ∧ (1 ≤ f (2*n+2)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa using h1
    · simpa using h2
  | succ m ih =>
    obtain ⟨iha, ihb⟩ := ih
    refine ⟨?_, ?_⟩
    · have h := hodd m
      rw [show 2*(m+1)+1 = 2*m+3 from by ring, h]
      nlinarith [iha, ihb]
    · have h := even_pos hodd heven m
      rw [show 2*(m+1)+2 = 2*m+4 from by ring, h]
      nlinarith [iha, ihb]

end generic

lemma A_odd (k : ℕ) : A340738 (2*k+3) = 2 * A340738 (2*k+2) + (2*k+3) * A340738 (2*k+1) := by
  rw [A340738]
  have h2 : (2*k+3) % 2 = 1 := by omega
  simp only [h2]
  norm_num
  congr 2

lemma A_even (k : ℕ) : A340738 (2*k+4) =
    (k+3) * A340738 (2*k+3) - A340738 (2*k+2) - (k+1) * A340738 (2*k+1) := by
  rw [show 2*k+4 = (2*k+1)+3 from by ring, A340738]
  have h2 : (2*k+1+3) % 2 = 0 := by omega
  simp only [h2]
  have e1 : (2*k+1+3+2)/2 = k+3 := by omega
  have e2 : (2*k+1+3-2)/2 = k+1 := by omega
  have i1 : 2*k+1+3-1 = 2*k+3 := by omega
  have i2 : 2*k+1+3-2 = 2*k+2 := by omega
  have i3 : 2*k+1+3-3 = 2*k+1 := by omega
  rw [e1, e2, i1, i2, i3]

lemma B_odd (k : ℕ) : A340737 (2*k+3) = 2 * A340737 (2*k+2) + (2*k+3) * A340737 (2*k+1) := by
  rw [A340737]
  have h2 : (2*k+3) % 2 = 1 := by omega
  simp only [h2]
  norm_num
  congr 2

lemma B_even (k : ℕ) : A340737 (2*k+4) =
    (k+3) * A340737 (2*k+3) - A340737 (2*k+2) - (k+1) * A340737 (2*k+1) := by
  rw [show 2*k+4 = (2*k+1)+3 from by ring, A340737]
  have h2 : (2*k+1+3) % 2 = 0 := by omega
  simp only [h2]
  have e1 : (2*k+1+3+2)/2 = k+3 := by omega
  have e2 : (2*k+1+3-2)/2 = k+1 := by omega
  have i1 : 2*k+1+3-1 = 2*k+3 := by omega
  have i2 : 2*k+1+3-2 = 2*k+2 := by omega
  have i3 : 2*k+1+3-3 = 2*k+1 := by omega
  rw [e1, e2, i1, i2, i3]

/- ### Positivity and growth -/

lemma A_pos (n : ℕ) : (n+1 ≤ A340738 (2*n+1)) ∧ (1 ≤ A340738 (2*n+2)) :=
  pos_pair A_odd A_even (by decide) (by decide) n

lemma B_pos (n : ℕ) : (n+1 ≤ A340737 (2*n+1)) ∧ (1 ≤ A340737 (2*n+2)) :=
  pos_pair B_odd B_even (by decide) (by decide) n

/- ### The key identity `S n = T n` -/

noncomputable def e : ℝ := Real.exp 1

noncomputable def S (n : ℕ) : ℝ := (A340737 (2*n+1) : ℝ) - e * (A340738 (2*n+1) : ℝ)

lemma S_rec (n : ℕ) : S (n+2) = (4*(n:ℝ)+10) * S (n+1) + S n := by
  have hA := subseq A_odd A_even n
  have hB := subseq B_odd B_even n
  have cA : (A340738 (2*n+5):ℝ) = (4*(n:ℝ)+10)*(A340738 (2*n+3):ℝ)+(A340738 (2*n+1):ℝ) := by
    exact_mod_cast hA
  have cB : (A340737 (2*n+5):ℝ) = (4*(n:ℝ)+10)*(A340737 (2*n+3):ℝ)+(A340737 (2*n+1):ℝ) := by
    exact_mod_cast hB
  simp only [S]
  rw [show 2*(n+2)+1 = 2*n+5 from by ring, show 2*(n+1)+1 = 2*n+3 from by ring, cA, cB]
  ring

lemma S_zero : S 0 = 3 - e := by
  simp only [S, e]
  norm_num [show A340737 1 = 3 from rfl, show A340738 1 = 1 from rfl]

lemma S_one : S 1 = 19 - 7 * e := by
  simp only [S, e]
  norm_num [show A340737 3 = 19 from rfl, show A340738 3 = 7 from rfl]
  ring

lemma S_eq_T : ∀ n, S n = T n ∧ S (n+1) = T (n+1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [S_zero, T_zero, e]
    · rw [S_one, T_one, e]
  | succ m ih =>
    obtain ⟨iha, ihb⟩ := ih
    refine ⟨ihb, ?_⟩
    rw [show m+1+1 = m+2 from rfl, S_rec, T_rec, iha, ihb]

lemma S_eq_T' (n : ℕ) : S n = T n := (S_eq_T n).1

/- ### The Casoratian -/

noncomputable def Ez (n : ℕ) : ℤ :=
  (A340737 (2*n+2) : ℤ) * (A340738 (2*n+1) : ℤ)
    - (A340738 (2*n+2) : ℤ) * (A340737 (2*n+1) : ℤ)

lemma Ez_rec (n : ℕ) : Ez (n+1) = - Ez n := by
  have hAe := even_pos A_odd A_even n
  have hAo := A_odd n
  have hBe := even_pos B_odd B_even n
  have hBo := B_odd n
  simp only [Ez]
  rw [show 2*(n+1)+2 = 2*n+4 from by ring, show 2*(n+1)+1 = 2*n+3 from by ring]
  have zAe : (A340738 (2*n+4):ℤ) = (2*(n:ℤ)+5)*(A340738 (2*n+2):ℤ)+2*((n:ℤ)+2)^2*(A340738 (2*n+1):ℤ) := by
    exact_mod_cast hAe
  have zAo : (A340738 (2*n+3):ℤ) = 2*(A340738 (2*n+2):ℤ)+(2*(n:ℤ)+3)*(A340738 (2*n+1):ℤ) := by
    exact_mod_cast hAo
  have zBe : (A340737 (2*n+4):ℤ) = (2*(n:ℤ)+5)*(A340737 (2*n+2):ℤ)+2*((n:ℤ)+2)^2*(A340737 (2*n+1):ℤ) := by
    exact_mod_cast hBe
  have zBo : (A340737 (2*n+3):ℤ) = 2*(A340737 (2*n+2):ℤ)+(2*(n:ℤ)+3)*(A340737 (2*n+1):ℤ) := by
    exact_mod_cast hBo
  rw [zAe, zAo, zBe, zBo]
  ring

lemma Ez_eq (n : ℕ) : Ez n = (-1)^(n+1) := by
  induction n with
  | zero => decide
  | succ m ih => rw [Ez_rec, ih]; ring

lemma Ez_abs (n : ℕ) : |(Ez n : ℝ)| = 1 := by
  rw [Ez_eq]
  push_cast
  rw [abs_pow, abs_neg, abs_one, one_pow]

/- ### Convergence -/

lemma A_odd_pos (n : ℕ) : ((n:ℝ)+1) ≤ (A340738 (2*n+1):ℝ) := by
  exact_mod_cast (A_pos n).1

lemma A_odd_ne (n : ℕ) : (A340738 (2*n+1):ℝ) ≠ 0 := by
  have h : ((n:ℝ)+1) ≤ (A340738 (2*n+1):ℝ) := A_odd_pos n
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have : (0:ℝ) < (A340738 (2*n+1):ℝ) := by linarith
  exact ne_of_gt this

lemma T_abs_le' (n : ℕ) : |T n| ≤ (Real.exp 1 - 1)/((n:ℝ)+1) := by
  refine le_trans (T_abs_le n) ?_
  have h1 : ((n:ℝ)+1) ≤ (Nat.factorial (n+1) : ℝ) := by
    have := Nat.self_le_factorial (n+1)
    push_cast at this ⊢
    exact_mod_cast this
  have h0 : (0:ℝ) ≤ Real.exp 1 - 1 := by
    have := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1); linarith
  gcongr

lemma seq_odd_sub (n : ℕ) :
    sequence_of_fractions (2*n+1) - Real.exp 1 = T n / (A340738 (2*n+1):ℝ) := by
  have ha : (A340738 (2*n+1):ℝ) ≠ 0 := A_odd_ne n
  rw [← S_eq_T']
  simp only [sequence_of_fractions, S, e]
  field_simp

lemma tendsto_odd :
    Tendsto (fun n => sequence_of_fractions (2*n+1)) atTop (nhds (Real.exp 1)) := by
  have hlim : Tendsto (fun n:ℕ => (Real.exp 1 - 1)/((n:ℝ)+1)) atTop (nhds 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := h.const_mul (Real.exp 1 - 1)
    simpa [mul_one_div] using h2
  have hbound : ∀ n, ‖sequence_of_fractions (2*n+1) - Real.exp 1‖
      ≤ (Real.exp 1 - 1)/((n:ℝ)+1) := by
    intro n
    have hA1 : (1:ℝ) ≤ (A340738 (2*n+1):ℝ) := by
      have := A_odd_pos n; have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
    have hApos : (0:ℝ) < (A340738 (2*n+1):ℝ) := by linarith
    rw [Real.norm_eq_abs, seq_odd_sub n, abs_div, abs_of_pos hApos]
    calc |T n| / (A340738 (2*n+1):ℝ) ≤ |T n| := div_le_self (abs_nonneg _) hA1
      _ ≤ (Real.exp 1 - 1)/((n:ℝ)+1) := T_abs_le' n
  have hz := squeeze_zero_norm hbound hlim
  have := hz.add_const (Real.exp 1)
  simpa using this

lemma seq_even_sub (n : ℕ) :
    sequence_of_fractions (2*n+2) - sequence_of_fractions (2*n+1)
      = (Ez n : ℝ)/((A340738 (2*n+2):ℝ)*(A340738 (2*n+1):ℝ)) := by
  have ha1 : (A340738 (2*n+1):ℝ) ≠ 0 := A_odd_ne n
  have ha2 : (A340738 (2*n+2):ℝ) ≠ 0 := by
    have : (1:ℝ) ≤ (A340738 (2*n+2):ℝ) := by exact_mod_cast (A_pos n).2
    positivity
  simp only [sequence_of_fractions, Ez]
  push_cast
  rw [div_sub_div _ _ ha2 ha1]

lemma tendsto_even :
    Tendsto (fun n => sequence_of_fractions (2*n+2)) atTop (nhds (Real.exp 1)) := by
  have hlim : Tendsto (fun n:ℕ => 1/((n:ℝ)+1) + (Real.exp 1 - 1)/((n:ℝ)+1)) atTop (nhds 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := h.const_mul (Real.exp 1 - 1)
    have := h.add (by simpa [mul_one_div] using h2)
    simpa using this
  have hbound : ∀ n, ‖sequence_of_fractions (2*n+2) - Real.exp 1‖
      ≤ 1/((n:ℝ)+1) + (Real.exp 1 - 1)/((n:ℝ)+1) := by
    intro n
    have hA1 : ((n:ℝ)+1) ≤ (A340738 (2*n+1):ℝ) := A_odd_pos n
    have hA2 : (1:ℝ) ≤ (A340738 (2*n+2):ℝ) := by exact_mod_cast (A_pos n).2
    have hn0 : (0:ℝ) < (n:ℝ)+1 := by positivity
    have hprod : ((n:ℝ)+1) ≤ (A340738 (2*n+2):ℝ)*(A340738 (2*n+1):ℝ) := by
      calc ((n:ℝ)+1) = 1 * ((n:ℝ)+1) := by ring
        _ ≤ (A340738 (2*n+2):ℝ)*(A340738 (2*n+1):ℝ) := by
            apply mul_le_mul hA2 hA1 (by linarith) (by linarith)
    have hprodpos : (0:ℝ) < (A340738 (2*n+2):ℝ)*(A340738 (2*n+1):ℝ) := by linarith
    have hstep : ‖sequence_of_fractions (2*n+2) - sequence_of_fractions (2*n+1)‖
        ≤ 1/((n:ℝ)+1) := by
      rw [Real.norm_eq_abs, seq_even_sub n, abs_div, Ez_abs, abs_of_pos hprodpos]
      exact one_div_le_one_div_of_le hn0 hprod
    have hodd : ‖sequence_of_fractions (2*n+1) - Real.exp 1‖ ≤ (Real.exp 1 - 1)/((n:ℝ)+1) := by
      have hA1' : (1:ℝ) ≤ (A340738 (2*n+1):ℝ) := by
        have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
      have hApos : (0:ℝ) < (A340738 (2*n+1):ℝ) := by linarith
      rw [Real.norm_eq_abs, seq_odd_sub n, abs_div, abs_of_pos hApos]
      calc |T n| / (A340738 (2*n+1):ℝ) ≤ |T n| := div_le_self (abs_nonneg _) hA1'
        _ ≤ (Real.exp 1 - 1)/((n:ℝ)+1) := T_abs_le' n
    calc ‖sequence_of_fractions (2*n+2) - Real.exp 1‖
        = ‖(sequence_of_fractions (2*n+2) - sequence_of_fractions (2*n+1))
            + (sequence_of_fractions (2*n+1) - Real.exp 1)‖ := by ring_nf
      _ ≤ ‖sequence_of_fractions (2*n+2) - sequence_of_fractions (2*n+1)‖
            + ‖sequence_of_fractions (2*n+1) - Real.exp 1‖ := norm_add_le _ _
      _ ≤ 1/((n:ℝ)+1) + (Real.exp 1 - 1)/((n:ℝ)+1) := by
            apply add_le_add hstep hodd
  have hz := squeeze_zero_norm hbound hlim
  have := hz.add_const (Real.exp 1)
  simpa using this

theorem tendsto_all :
    Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp tendsto_odd) ε hε
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp tendsto_even) ε hε
  refine ⟨2*(N1+N2)+2, ?_⟩
  intro m hm
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- m = k + k, even
    have hk2 : m = 2*(k-1)+2 := by omega
    have hkN : k - 1 ≥ N2 := by omega
    rw [hk2]
    exact hN2 (k-1) hkN
  · -- m = 2*k+1, odd
    have hkN : k ≥ N1 := by omega
    rw [hk]
    exact hN1 k hkN

end OEIS340738

/-- oeis_340738_conjecture_0: "The convergence is conjectured."
Formally, the sequence of fractions $A340737(n) / A340738(n)$ converges to $e$.
-/
theorem oeis_340738_conjecture_0 :
  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) :=
by exact OEIS340738.tendsto_all
