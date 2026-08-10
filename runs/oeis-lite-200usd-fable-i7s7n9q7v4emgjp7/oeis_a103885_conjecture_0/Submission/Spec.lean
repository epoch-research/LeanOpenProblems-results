import FormalConjectures.Util.ProblemImports

set_option Elab.async false
set_option warn.sorry false
set_option linter.all false

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

/--
A103885: $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$.
The sequence is given by the combinatorial identity:
$$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$$
with $a(0) = 1$.
-/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

-- The sequence b(n) = a(m*n) lifted to ℝ
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

-- The indices k = 1 to 2m, used in the product
private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))


-- ===== Dev.Basic =====
/-!
# Basic scalar functions and 2×2 matrix machinery for the A103885 conjecture

The three-term recurrence for `a(n) = A103885 n` is
`cP n * a(n+1) + c0 n * a(n) + cM n * a(n-1) = 0`.
-/

namespace Bala

section Scalars

variable {R : Type*} [CommRing R]

/-- `p1 x = 5x² - 5x + 1`, the polynomial `P(2,·)` of the conjecture. -/
def p1 (x : R) : R := 5*x^2 - 5*x + 1

/-- Coefficient of `a(ν+1)` in the base recurrence. -/
def cP (x : R) : R := (2*x+1)*(2*x+2)*(5*x^2-5*x+1)

/-- Coefficient of `a(ν)` in the base recurrence. -/
def c0 (x : R) : R := -(220*x^4 - 136*x^2 + 12)

/-- Coefficient of `a(ν-1)` in the base recurrence. -/
def cM (x : R) : R := -((2*x-1)*(2*x-2)*(5*x^2+5*x+1))

lemma cP_eq_lin_mul_p1 (x : R) : cP x = (2*x+1)*(2*x+2)*p1 x := by
  simp only [cP, p1]

lemma cM_eq_lin_mul_p1 (x : R) : cM x = -((2*x-1)*(2*x-2)*p1 (x+1)) := by
  simp only [cM, p1]; ring

/-- Reflection: `p1 (-x) = p1 (x+1)`. -/
lemma p1_neg (x : R) : p1 (-x) = p1 (x+1) := by simp only [p1]; ring

/-- Symmetry: `p1 (1-x) = p1 x`. -/
lemma p1_one_sub (x : R) : p1 (1-x) = p1 x := by simp only [p1]; ring

/-- Transposition relation: `cP (-x) = -(cM x)`. -/
lemma cP_neg (x : R) : cP (-x) = -(cM x) := by simp only [cP, cM]; ring

/-- Transposition relation: `cM (-x) = -(cP x)`. -/
lemma cM_neg (x : R) : cM (-x) = -(cP x) := by simp only [cP, cM]; ring

/-- Evenness: `c0 (-x) = c0 x`. -/
lemma c0_neg (x : R) : c0 (-x) = c0 x := by simp only [c0]; ring

/-- Magic identity 1: `p1 x` divides `c0 x * c0 (x-1) - cM x * cP (x-1)`,
with explicit cofactor. -/
lemma magic1 (x : R) :
    c0 x * c0 (x-1) - cM x * cP (x-1) =
      p1 x * (9760*x^6 - 29280*x^5 + 15252*x^4 + 18296*x^3 - 12448*x^2 - 1580*x + 1152) := by
  simp only [c0, cM, cP, p1]; ring

/-- Magic identity 2: `cM (x-1) = -((2x-3)(2x-4)) * p1 x`. -/
lemma magic2 (x : R) : cM (x-1) = -((2*x-3)*(2*x-4)) * p1 x := by
  simp only [cM, p1]; ring

/-- Bézout certificate: `p1 y` and `p1 (y+d)` generate `5d³ - d`. -/
lemma p1_bezout (y d : R) :
    (2*y+3*d-1) * p1 y + (-(2*y)+d+1) * p1 (y+d) = 5*d^3 - d := by
  simp only [p1]; ring

end Scalars

/-! ## Compatibility of the scalar functions with ring homomorphisms,
polynomial evaluation, composition and mapping. -/

section Homs

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] lemma map_cP (f : R →+* S) (x : R) : f (cP x) = cP (f x) := by
  simp only [cP, map_ofNat, f.map_add, f.map_sub, f.map_mul, f.map_pow, f.map_one]

@[simp] lemma map_c0 (f : R →+* S) (x : R) : f (c0 x) = c0 (f x) := by
  simp only [c0, map_ofNat, f.map_neg, f.map_add, f.map_sub, f.map_mul, f.map_pow]

@[simp] lemma map_cM (f : R →+* S) (x : R) : f (cM x) = cM (f x) := by
  simp only [cM, map_ofNat, f.map_neg, f.map_add, f.map_sub, f.map_mul, f.map_pow, f.map_one]

open Polynomial

@[simp] lemma eval_p1 (p : R[X]) (t : R) : (p1 p).eval t = p1 (p.eval t) := by
  simp only [p1, eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat, eval_one]

@[simp] lemma eval_cP (p : R[X]) (t : R) : (cP p).eval t = cP (p.eval t) := by
  simp only [cP, eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat, eval_one]

@[simp] lemma eval_c0 (p : R[X]) (t : R) : (c0 p).eval t = c0 (p.eval t) := by
  simp only [c0, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat]

@[simp] lemma comp_p1 (p q : R[X]) : (p1 p).comp q = p1 (p.comp q) := by
  simp only [p1, add_comp, sub_comp, mul_comp, pow_comp, ofNat_comp, one_comp, Nat.cast_ofNat]

end Homs

/-! ## A bare-bones 2×2 matrix structure -/

/-- A 2×2 matrix with entries `a b / c d`. -/
structure M2 (R : Type*) where
  a : R
  b : R
  c : R
  d : R
  deriving Repr

namespace M2

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Matrix product. -/
def mul (A B : M2 R) : M2 R :=
  ⟨A.a*B.a + A.b*B.c, A.a*B.b + A.b*B.d, A.c*B.a + A.d*B.c, A.c*B.b + A.d*B.d⟩

/-- Identity matrix. -/
def one : M2 R := ⟨1, 0, 0, 1⟩

/-- Transpose. -/
def transpose (A : M2 R) : M2 R := ⟨A.a, A.c, A.b, A.d⟩

/-- Action on a column vector (represented as a pair). -/
def act (A : M2 R) (v : R × R) : R × R :=
  (A.a*v.1 + A.b*v.2, A.c*v.1 + A.d*v.2)

/-- Entry-wise application of a map. -/
def emap (f : R → S) (A : M2 R) : M2 S := ⟨f A.a, f A.b, f A.c, f A.d⟩

/-- Determinant. -/
def det (A : M2 R) : R := A.a*A.d - A.b*A.c

@[ext] lemma ext {A B : M2 R} (ha : A.a = B.a) (hb : A.b = B.b)
    (hc : A.c = B.c) (hd : A.d = B.d) : A = B := by
  cases A; cases B; simp_all

@[simp] lemma mul_a (A B : M2 R) : (A.mul B).a = A.a*B.a + A.b*B.c := rfl
@[simp] lemma mul_b (A B : M2 R) : (A.mul B).b = A.a*B.b + A.b*B.d := rfl
@[simp] lemma mul_c (A B : M2 R) : (A.mul B).c = A.c*B.a + A.d*B.c := rfl
@[simp] lemma mul_d (A B : M2 R) : (A.mul B).d = A.c*B.b + A.d*B.d := rfl

@[simp] lemma one_a : (one : M2 R).a = 1 := rfl
@[simp] lemma one_b : (one : M2 R).b = 0 := rfl
@[simp] lemma one_c : (one : M2 R).c = 0 := rfl
@[simp] lemma one_d : (one : M2 R).d = 1 := rfl

lemma mul_assoc (A B C : M2 R) : (A.mul B).mul C = A.mul (B.mul C) := by
  ext <;> simp only [mul_a, mul_b, mul_c, mul_d] <;> ring

@[simp] lemma mul_one (A : M2 R) : A.mul one = A := by
  ext <;> simp only [mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c, one_d,
    _root_.mul_one, mul_zero, add_zero, zero_add]

@[simp] lemma one_mul (A : M2 R) : one.mul A = A := by
  ext <;> simp only [mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c, one_d,
    _root_.one_mul, zero_mul, add_zero, zero_add]

lemma act_mul (A B : M2 R) (v : R × R) : (A.mul B).act v = A.act (B.act v) := by
  simp only [act, mul_a, mul_b, mul_c, mul_d, Prod.mk.injEq]
  constructor <;> ring

@[simp] lemma act_one (v : R × R) : (one : M2 R).act v = v := by
  simp only [act, one, _root_.one_mul, zero_mul, add_zero, zero_add]

@[simp] lemma transpose_one : (one : M2 R).transpose = one := rfl

lemma transpose_mul (A B : M2 R) : (A.mul B).transpose = B.transpose.mul A.transpose := by
  ext <;> simp only [transpose, mul_a, mul_b, mul_c, mul_d] <;> ring

@[simp] lemma transpose_a (A : M2 R) : A.transpose.a = A.a := rfl

lemma emap_mul (f : R →+* S) (A B : M2 R) :
    emap f (A.mul B) = (emap f A).mul (emap f B) := by
  ext <;> simp only [emap, mul_a, mul_b, mul_c, mul_d, f.map_add, f.map_mul]

@[simp] lemma emap_one (f : R →+* S) : emap f (one : M2 R) = one := by
  ext <;> simp only [emap, one, f.map_one, f.map_zero]

lemma det_mul (A B : M2 R) : (A.mul B).det = A.det * B.det := by
  simp only [det, mul_a, mul_b, mul_c, mul_d]; ring

@[simp] lemma det_one : (one : M2 R).det = 1 := by
  simp only [det, one]; ring

end M2

end Bala

-- ===== Dev.Windows =====
/-!
# Transfer-matrix windows

`Wnd b len = M(b+len-1) ⋯ M(b+1) M(b)` where `M(p) = [[-c0 p, -cM p],[cP p, 0]]`.
-/

namespace Bala

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The step matrix `M(p)`. -/
def Mstep (p : R) : M2 R := ⟨-(c0 p), -(cM p), cP p, 0⟩

@[simp] lemma Mstep_a (p : R) : (Mstep p).a = -(c0 p) := rfl
@[simp] lemma Mstep_b (p : R) : (Mstep p).b = -(cM p) := rfl
@[simp] lemma Mstep_c (p : R) : (Mstep p).c = cP p := rfl
@[simp] lemma Mstep_d (p : R) : (Mstep p).d = 0 := rfl

lemma Mstep_neg (p : R) : Mstep (-p) = (Mstep p).transpose := by
  ext <;> simp [Mstep, M2.transpose, cP_neg, cM_neg, c0_neg]

lemma Mstep_emap (f : R →+* S) (p : R) :
    M2.emap f (Mstep p) = Mstep (f p) := by
  ext <;> simp only [Mstep, M2.emap, f.map_neg, f.map_zero, map_c0, map_cM, map_cP]

lemma Mstep_det (p : R) : (Mstep p).det = cP p * cM p := by
  simp [Mstep, M2.det]; ring

/-- The window `Wnd b len = M(b+len-1) ⋯ M(b+1) M(b)`. -/
def Wnd (b : R) : ℕ → M2 R
  | 0 => M2.one
  | (len+1) => (Mstep (b + (len : R))).mul (Wnd b len)

@[simp] lemma Wnd_zero (b : R) : Wnd b 0 = M2.one := rfl

lemma Wnd_succ (b : R) (len : ℕ) :
    Wnd b (len+1) = (Mstep (b + (len : R))).mul (Wnd b len) := rfl

@[simp] lemma Wnd_one (b : R) : Wnd b 1 = Mstep b := by
  rw [Wnd_succ]
  simp

/-- Peel off the bottom (first-applied) factor. -/
lemma Wnd_bottom (b : R) (len : ℕ) :
    Wnd b (len+1) = (Wnd (b+1) len).mul (Mstep b) := by
  induction len with
  | zero => simp
  | succ n ih =>
    rw [Wnd_succ, ih, ← M2.mul_assoc]
    have h1 : b + ((n : R) + 1) = (b + 1) + (n : R) := by ring
    rw [show ((n+1 : ℕ) : R) = ((n : R) + 1) by push_cast; ring, h1, ← Wnd_succ]

/-- Split a window into an upper and a lower part. -/
lemma Wnd_split (b : R) (l₁ l₂ : ℕ) :
    Wnd b (l₁ + l₂) = (Wnd (b + (l₁ : R)) l₂).mul (Wnd b l₁) := by
  induction l₂ with
  | zero => simp
  | succ n ih =>
    have : l₁ + (n + 1) = (l₁ + n) + 1 := by omega
    rw [this, Wnd_succ, ih, ← M2.mul_assoc, Wnd_succ]
    congr 2
    push_cast
    ring

lemma Wnd_emap (f : R →+* S) (b : R) (len : ℕ) :
    M2.emap f (Wnd b len) = Wnd (f b) len := by
  induction len with
  | zero => simp [Wnd]
  | succ n ih =>
    rw [Wnd_succ, M2.emap_mul, ih, Mstep_emap, Wnd_succ]
    congr 2
    simp

/-- Transposition-reversal duality for windows. -/
lemma Wnd_transpose (b : R) (len : ℕ) :
    (Wnd b len).transpose = Wnd (1 - b - (len : R)) len := by
  induction len with
  | zero => simp [Wnd]
  | succ n ih =>
    rw [Wnd_succ, M2.transpose_mul, ih, ← Mstep_neg]
    have h1 : -(b + (n : R)) = (-b - (n : R) + 1) - 1 := by ring
    have h2 : (1 : R) - b - (n : R) = (-b - (n:R) + 1 - 1) + 1 := by ring
    rw [h1, h2, ← Wnd_bottom]
    congr 1
    push_cast
    ring

lemma Wnd_det (b : R) (len : ℕ) :
    (Wnd b len).det = ∏ i ∈ Finset.range len, (cP (b + (i:R)) * cM (b + (i:R))) := by
  induction len with
  | zero => simp [Wnd]
  | succ n ih =>
    rw [Wnd_succ, M2.det_mul, ih, Mstep_det, Finset.prod_range_succ]
    ring

/-- The `c`-entry of a window peels the top factor. -/
lemma Wnd_c_peel (b : R) (len : ℕ) :
    (Wnd b (len+1)).c = cP (b + (len : R)) * (Wnd b len).a := by
  rw [Wnd_succ]
  simp

/-! ## Action on a solution of the base recurrence -/

section Action

variable (u : ℕ → ℚ)

/-- Divisionless window action: applying the window `Wnd b len` to
`(u b, u (b-1))` yields `∏ cP • (u (b+len), u (b+len-1))`. -/
lemma Wnd_act
    (hrec : ∀ N : ℕ, 1 ≤ N →
      cP (N:ℚ) * u (N+1) + c0 (N:ℚ) * u N + cM (N:ℚ) * u (N-1) = 0)
    (b : ℕ) (hb : 1 ≤ b) (len : ℕ) :
    (Wnd (b:ℚ) len).act (u b, u (b-1)) =
      ((∏ i ∈ Finset.range len, cP ((b:ℚ) + (i:ℚ))) * u (b+len),
       (∏ i ∈ Finset.range len, cP ((b:ℚ) + (i:ℚ))) * u (b+len-1)) := by
  induction len with
  | zero => simp [M2.act_one]
  | succ n ih =>
    rw [Wnd_succ, M2.act_mul, ih]
    have hN : 1 ≤ b + n := by omega
    have hstep := hrec (b+n) hN
    have hcast : ((b + n : ℕ) : ℚ) = (b:ℚ) + (n:ℚ) := by push_cast; ring
    rw [hcast] at hstep
    have hsub1 : b + (n+1) - 1 = b + n := by omega
    simp only [M2.act, Mstep_a, Mstep_b, Mstep_c, Mstep_d, Finset.prod_range_succ,
      Prod.mk.injEq]
    rw [hsub1]
    have hidx : b + (n+1) = (b + n) + 1 := by omega
    rw [hidx]
    constructor
    · linear_combination (-(∏ i ∈ Finset.range n, cP ((b:ℚ) + (i:ℚ)))) * hstep
    · ring

/-- Scalar three-term contraction: a relation between
`u (μ+m) = b(n+1)`, `u μ = b(n)`, `u (μ-m) = b(n-1)`. -/
lemma contraction
    (hrec : ∀ N : ℕ, 1 ≤ N →
      cP (N:ℚ) * u (N+1) + c0 (N:ℚ) * u N + cM (N:ℚ) * u (N-1) = 0)
    (μ m : ℕ) (hm : 1 ≤ m) (hmμ : m ≤ μ) :
    (∏ i ∈ Finset.range m, cP ((μ:ℚ)+1+(i:ℚ))) *
      (∏ i ∈ Finset.range m, cP ((μ:ℚ)-(m:ℚ)+1+(i:ℚ))) *
      (Wnd ((μ:ℚ)-(m:ℚ)+1) m).c * u (μ+m)
    + (Wnd ((μ:ℚ)+1) m).c * (Wnd ((μ:ℚ)-(m:ℚ)+1) m).det * u (μ-m)
    = (∏ i ∈ Finset.range m, cP ((μ:ℚ)-(m:ℚ)+1+(i:ℚ))) *
      ((Wnd ((μ:ℚ)+1) m).mul (Wnd ((μ:ℚ)-(m:ℚ)+1) m)).c * u μ := by
  have hcast : ((μ - m + 1 : ℕ) : ℚ) = (μ:ℚ) - (m:ℚ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hmμ]; norm_num
  have h1 := Wnd_act u hrec (μ+1) (by omega) m
  have h2 := Wnd_act u hrec (μ-m+1) (by omega) m
  rw [hcast] at h2
  have e1 : μ + 1 - 1 = μ := by omega
  have e2 : μ + 1 + m - 1 = μ + m := by omega
  have e3 : μ - m + 1 + m = μ + 1 := by omega
  have e4 : μ - m + 1 + m - 1 = μ := by omega
  have e5 : μ - m + 1 - 1 = μ - m := by omega
  rw [e1, e2] at h1
  rw [e4, e3, e5] at h2
  have hc1 : ((μ + 1 : ℕ) : ℚ) = (μ:ℚ) + 1 := by push_cast; ring
  rw [hc1] at h1
  simp only [M2.act, Prod.mk.injEq] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  simp only [M2.det, M2.mul_c]
  linear_combination
    (-((∏ i ∈ Finset.range m, cP ((μ:ℚ)-(m:ℚ)+1+(i:ℚ))) *
        (Wnd ((μ:ℚ)-(m:ℚ)+1) m).c)) * h1b
    - ((Wnd ((μ:ℚ)+1) m).c * (Wnd ((μ:ℚ)-(m:ℚ)+1) m).c) * h2a
    + ((Wnd ((μ:ℚ)+1) m).c * (Wnd ((μ:ℚ)-(m:ℚ)+1) m).a) * h2b

end Action

end Bala

attribute [irreducible] Bala.Wnd Bala.Mstep Bala.M2.mul Bala.cP Bala.cM Bala.c0 Bala.p1
-- ===== Dev.Series =====
/-!
# The three-term base recurrence for A103885

We prove `cP N * a(N+1) + c0 N * a(N) + cM N * a(N-1) = 0` for `N ≥ 1`,
via a power-series certificate.
-/

namespace Bala

open Nat Finset Polynomial PowerSeries

/-- Local copy of the OEIS sequence definition (identical to the one in the
problem statement file). -/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

/-- The sequence as rationals. -/
def aq (n : ℕ) : ℚ := (A103885 n : ℚ)

/-- `Dser N = (1-x)^{-(N+1)} = ∑_j C(N+j, N) x^j`. -/
def Dser (N : ℕ) : ℚ⟦X⟧ := PowerSeries.mk fun j => ((N+j).choose N : ℚ)

lemma coeff_Dser (N j : ℕ) : (PowerSeries.coeff j) (Dser N) = ((N+j).choose N : ℚ) :=
  coeff_mk j _

/-- `(1-x) ⬝ Dser (M+1) = Dser M`. -/
lemma D_shift (M : ℕ) : (1 - PowerSeries.X) * Dser (M+1) = Dser M := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero => simp [coeff_Dser]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_Dser, coeff_Dser, coeff_Dser]
    have h1 : M + 1 + (n+1) = (M + 1 + n) + 1 := by omega
    rw [h1, Nat.choose_succ_succ' (M+1+n) M]
    have h2 : M + 1 + n = M + (n + 1) := by omega
    push_cast [h2]
    ring

/-- `(1-x) ⬝ Dser 0 = 1`. -/
lemma D_shift0 : (1 - PowerSeries.X) * Dser 0 = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero => simp [coeff_Dser]
  | succ n => simp [coeff_succ_X_mul, coeff_Dser]

/-- Derivative of `Dser`. -/
lemma D_deriv (N : ℕ) :
    d⁄dX ℚ (Dser N) = PowerSeries.C ((N:ℚ)+1) * Dser (N+1) := by
  ext j
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, coeff_Dser, coeff_Dser]
  -- (j+1) * C(N+j+1, N) = (N+1) * C(N+1+j, N+1), both = (N+j+1)*C(N+j,N)
  have key1 : (N + j + 1) * ((N+j).choose j) = (N+(j+1)).choose (j+1) * (j+1) :=
    Nat.succ_mul_choose_eq (N+j) j
  have key2 : (N + j + 1) * ((N+j).choose N) = (N+j+1).choose (N+1) * (N+1) :=
    Nat.succ_mul_choose_eq (N+j) N
  have symm1 : (N+j).choose j = (N+j).choose N := by
    have := Nat.choose_symm (n := N+j) (k := j) (by omega)
    simpa [show N + j - j = N by omega] using this.symm
  have e1 : N + (j+1) = N + j + 1 := by omega
  rw [e1] at key1
  rw [symm1] at key1
  have : ((N+j+1).choose N : ℚ) * ((j:ℚ)+1) = ((N:ℚ)+1) * ((N+1+j).choose (N+1) : ℚ) := by
    have symm2 : (N+j+1).choose N = (N+j+1).choose (j+1) := by
      have := Nat.choose_symm (n := N+j+1) (k := j+1) (by omega)
      simpa [show N + j + 1 - (j+1) = N by omega] using this
    rw [symm2]
    have e2 : N + 1 + j = N + j + 1 := by omega
    rw [e2]
    have k1q : ((N:ℚ)+(j:ℚ)+1) * ((N+j).choose N : ℚ)
        = ((N+j+1).choose (j+1) : ℚ) * ((j:ℚ)+1) := by exact_mod_cast key1
    have k2q : ((N:ℚ)+(j:ℚ)+1) * ((N+j).choose N : ℚ)
        = ((N+j+1).choose (N+1) : ℚ) * ((N:ℚ)+1) := by exact_mod_cast key2
    linarith [k1q, k2q]
  simpa using this

/-- Coefficient-extraction: `a (K+1)` is a coefficient of `(1+x)^{K+1} Dser K`. -/
lemma aq_coeff (K : ℕ) :
    aq (K+1) =
      (PowerSeries.coeff (2*K+2))
        ((((1+Polynomial.X)^(K+1) : ℚ[X]) : ℚ⟦X⟧) * Dser K) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- RHS = ∑_{i ∈ range (2K+3)} C(K+1, i) * C(K + (2K+2-i), K)
  have hcoe : ∀ i, (PowerSeries.coeff i) (((1+Polynomial.X)^(K+1) : ℚ[X]) : ℚ⟦X⟧)
      = ((K+1).choose i : ℚ) := by
    intro i
    rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  have step1 : ∀ i ∈ Finset.range (2*K+3),
      (PowerSeries.coeff i) (((1+Polynomial.X)^(K+1) : ℚ[X]) : ℚ⟦X⟧) *
        (PowerSeries.coeff (2*K+2-i)) (Dser K)
      = ((K+1).choose i : ℚ) * ((3*K+2-i).choose K : ℚ) := by
    intro i hi
    have hi' : i ≤ 2*K+2 := by
      have := Finset.mem_range.mp hi
      omega
    rw [hcoe, coeff_Dser, show K + (2*K+2-i) = 3*K+2-i by omega]
  rw [Finset.sum_congr rfl step1]
  -- truncate the sum to `range (K+2)`
  rw [show (2*K+3) = (K+2) + (K+1) by omega]
  rw [Finset.sum_range_add]
  have zero2 : ∑ i ∈ Finset.range (K+1),
      (((K+1).choose (K+2+i) : ℚ) * ((3*K+2-(K+2+i)).choose K : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have : (K+1).choose (K+2+i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [this]
    push_cast
    ring
  rw [zero2, add_zero]
  -- reflect the sum
  rw [← Finset.sum_range_reflect]
  unfold aq A103885
  simp only [Nat.succ_ne_zero, if_neg]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ K + 1 := by
    have := Finset.mem_range.mp hk
    omega
  rw [Nat.choose_symm hk', show 3*K+2-(K+1-k) = 2*K+1+k by omega,
    show 2*(K+1)+k-1 = 2*K+1+k by omega]



/-! ## The generating-series certificate -/

noncomputable section

open PowerSeries

/-- `hser M = (1+x)^M / (1-x)^{M+2}`. -/
def hser (M : ℕ) : ℚ⟦X⟧ := (((1+Polynomial.X)^M : ℚ[X]) : ℚ⟦X⟧) * Dser (M+1)

lemma dmul (f g : ℚ⟦X⟧) :
    d⁄dX ℚ (f * g) = f * (d⁄dX ℚ g) + g * (d⁄dX ℚ f) := by
  have := PowerSeries.derivativeFun_mul f g
  simpa [smul_eq_mul] using this

/-- The hypergeometric ODE satisfied by `hser`. -/
lemma ode (M : ℕ) :
    (1 - PowerSeries.X^2) * (d⁄dX ℚ (hser M)) =
      (2*PowerSeries.C ((M:ℚ)+1) + 2*PowerSeries.X) * hser M := by
  unfold hser
  rw [dmul, D_deriv (M+1), PowerSeries.derivative_coe, Polynomial.derivative_pow]
  simp only [Polynomial.derivative_add, Polynomial.derivative_one, Polynomial.derivative_X,
    zero_add, mul_one, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
    Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  -- normalize all `C`-constants to expressions in `((M:ℚ⟦X⟧))`
  push_cast
  simp only [map_add, map_one, map_natCast]
  cases M with
  | zero =>
    simp only [Nat.cast_zero, pow_zero, one_mul, zero_add, map_zero, zero_mul, mul_zero, add_zero]
    have hs := D_shift 1
    linear_combination (2*(1+PowerSeries.X)) * hs
  | succ M' =>
    rw [Nat.add_sub_cancel]
    have hs := D_shift (M'+2)
    push_cast
    linear_combination
      ((((M' : ℚ⟦X⟧))+3) * (1+PowerSeries.X)^(M'+1) * (1+PowerSeries.X)) * hs

/-- Horner-form constructor for explicit polynomials. -/
def polyOf : List ℚ → ℚ[X]
  | [] => 0
  | a :: l => Polynomial.C a + Polynomial.X * polyOf l

/-- The degree-6 polynomial certificate `ū`. -/
def ubar (ν : ℚ) : ℚ[X] :=
  polyOf [ν*(-10*ν^3+5*ν^2+3*ν-1),
          ν*(-30*ν^3+10*ν^2+14*ν-4),
          70*ν^4-5*ν^3-41*ν^2+ν+4,
          ν*(60*ν^3-28*ν),
          -70*ν^4-5*ν^3+41*ν^2+ν-4,
          ν*(-30*ν^3-10*ν^2+14*ν+4),
          ν*(10*ν^3+5*ν^2-3*ν-1)]

/-- The symbol polynomial `W`. -/
def Wcert (ν : ℚ) : ℚ[X] :=
  cP (Polynomial.C ν) * (1+Polynomial.X)^2
  + c0 (Polynomial.C ν) * (Polynomial.X^2*(1-Polynomial.X^2))
  + cM (Polynomial.C ν) * (Polynomial.X^4*(1-Polynomial.X)^2)

/-- The certificate identity `(★)`. -/
lemma star (ν : ℚ) :
    Polynomial.C ν * (1 - Polynomial.X^2) * Wcert ν =
      Polynomial.X*(1-Polynomial.X^2) * Polynomial.derivative (ubar ν) +
      (2*Polynomial.X^2 + 2*Polynomial.C ν*Polynomial.X
        - (2*Polynomial.C ν+2)*(1-Polynomial.X^2)) * ubar ν := by
  unfold Wcert ubar
  simp only [polyOf, cP, c0, cM, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg,
    Polynomial.C_mul, Polynomial.C_pow, map_ofNat, Polynomial.C_1]
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.derivative_one, Polynomial.derivative_ofNat, Polynomial.derivative_neg,
    Polynomial.derivative_zero,
    map_ofNat, map_natCast, Nat.cast_ofNat]
  ring

lemma one_sub_X_sq_ne_zero : (1 - PowerSeries.X^2 : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.constantCoeff) h
  simp at this

/-- The master identity: `ν • (W ⬝ h) = x (ū h)' - (2ν+2) (ū h)`. -/
lemma main_series (M : ℕ) :
    PowerSeries.C ((M:ℚ)+1) * ((Wcert ((M:ℚ)+1) : ℚ⟦X⟧) * hser M)
      = PowerSeries.X * d⁄dX ℚ ((ubar ((M:ℚ)+1) : ℚ⟦X⟧) * hser M)
        - (2*PowerSeries.C ((M:ℚ)+1)+2) * ((ubar ((M:ℚ)+1) : ℚ⟦X⟧) * hser M) := by
  apply mul_left_cancel₀ one_sub_X_sq_ne_zero
  rw [dmul, PowerSeries.derivative_coe]
  have hode := ode M
  have hstar := congrArg (fun p : ℚ[X] => (p : ℚ⟦X⟧)) (star ((M:ℚ)+1))
  push_cast at hstar
  have coe_two : ((2:ℚ[X]) : ℚ⟦X⟧) = 2 := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat]
  rw [coe_two] at hstar
  linear_combination hser M * hstar
    - (PowerSeries.X * ((ubar ((M:ℚ)+1) : ℚ[X]) : ℚ⟦X⟧)) * hode

end

/-! ## Extraction of the three-term recurrence -/

lemma coeff_piece1 (M : ℕ) :
    (PowerSeries.coeff (2*M+4)) ((((1+Polynomial.X)^2 : ℚ[X]) : ℚ⟦X⟧) * hser M)
      = aq (M+2) := by
  unfold hser
  rw [← mul_assoc, ← Polynomial.coe_mul, ← pow_add]
  have h := aq_coeff (M+1)
  rw [show 2*(M+1)+2 = 2*M+4 by omega] at h
  rw [show 2 + M = M + 2 by omega]
  exact h.symm

lemma one_sub_sq_hser (M : ℕ) :
    (1 - PowerSeries.X^2) * hser M
      = (((1+Polynomial.X)^(M+1) : ℚ[X]) : ℚ⟦X⟧) * Dser M := by
  unfold hser
  have hs := D_shift M
  have hp : (((1+Polynomial.X)^(M+1) : ℚ[X]) : ℚ⟦X⟧)
      = (((1+Polynomial.X)^M : ℚ[X]) : ℚ⟦X⟧) * (1 + PowerSeries.X) := by
    rw [pow_succ]
    push_cast
    ring
  rw [hp]
  linear_combination ((((1+Polynomial.X)^M : ℚ[X]) : ℚ⟦X⟧) * (1+PowerSeries.X)) * hs

lemma coeff_piece2 (M : ℕ) :
    (PowerSeries.coeff (2*M+4))
      ((((Polynomial.X^2*(1-Polynomial.X^2)) : ℚ[X]) : ℚ⟦X⟧) * hser M) = aq (M+1) := by
  have hcoe : (((Polynomial.X^2*(1-Polynomial.X^2)) : ℚ[X]) : ℚ⟦X⟧) * hser M
      = PowerSeries.X^2 * ((1 - PowerSeries.X^2) * hser M) := by
    push_cast
    ring
  rw [hcoe, one_sub_sq_hser, show 2*M+4 = 2*M+2+2 by omega,
    PowerSeries.coeff_X_pow_mul]
  exact (aq_coeff M).symm

lemma coeff_piece3 (M : ℕ) :
    (PowerSeries.coeff (2*M+4))
      ((((Polynomial.X^4*(1-Polynomial.X)^2) : ℚ[X]) : ℚ⟦X⟧) * hser M) = aq M := by
  have hcoe : (((Polynomial.X^4*(1-Polynomial.X)^2) : ℚ[X]) : ℚ⟦X⟧) * hser M
      = PowerSeries.X^4 * ((1-PowerSeries.X) * ((1-PowerSeries.X) * hser M)) := by
    push_cast
    ring
  have hs1 : (1-PowerSeries.X) * hser M
      = (((1+Polynomial.X)^M : ℚ[X]) : ℚ⟦X⟧) * Dser M := by
    unfold hser
    have hs := D_shift M
    linear_combination (((1+Polynomial.X)^M : ℚ[X]) : ℚ⟦X⟧) * hs
  rw [hcoe, hs1, show 2*M+4 = 2*M+4 by omega]
  cases M with
  | zero =>
    rw [show (2*0+4) = 0+4 by omega, PowerSeries.coeff_X_pow_mul]
    have h0 : (1-PowerSeries.X) * ((((1+Polynomial.X)^0 : ℚ[X]) : ℚ⟦X⟧) * Dser 0) = 1 := by
      have := D_shift0
      push_cast
      linear_combination this
    rw [h0]
    simp [aq, A103885]
  | succ M' =>
    have hs2 : (1-PowerSeries.X) * ((((1+Polynomial.X)^(M'+1) : ℚ[X]) : ℚ⟦X⟧) * Dser (M'+1))
        = (((1+Polynomial.X)^(M'+1) : ℚ[X]) : ℚ⟦X⟧) * Dser M' := by
      have hs := D_shift M'
      linear_combination (((1+Polynomial.X)^(M'+1) : ℚ[X]) : ℚ⟦X⟧) * hs
    rw [hs2, show 2*(M'+1)+4 = (2*M'+2)+4 by omega, PowerSeries.coeff_X_pow_mul]
    exact (aq_coeff M').symm

/-- The base three-term recurrence, in the form used downstream. -/
theorem base_rec (N : ℕ) (hN : 1 ≤ N) :
    cP (N:ℚ) * aq (N+1) + c0 (N:ℚ) * aq N + cM (N:ℚ) * aq (N-1) = 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M+1 := ⟨N-1, by omega⟩
  set ν : ℚ := (M:ℚ)+1 with hν
  have hmain := congrArg (PowerSeries.coeff (2*M+4)) (main_series M)
  -- right side vanishes
  have hXd : ∀ g : ℚ⟦X⟧, (PowerSeries.coeff (2*M+4)) (PowerSeries.X * d⁄dX ℚ g)
      = ((2*M+4 : ℕ) : ℚ) * (PowerSeries.coeff (2*M+4)) g := by
    intro g
    rw [show 2*M+4 = (2*M+3)+1 by omega, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_derivative]
    push_cast
    ring
  have hC : (2*PowerSeries.C ((M:ℚ)+1)+2 : ℚ⟦X⟧) = PowerSeries.C (2*((M:ℚ)+1)+2) := by
    simp [map_add, map_mul, map_ofNat]
  rw [map_sub, hXd, hC, PowerSeries.coeff_C_mul] at hmain
  rw [PowerSeries.coeff_C_mul] at hmain
  have hz : ((M:ℚ)+1) * (PowerSeries.coeff (2*M+4)) ((Wcert ν : ℚ⟦X⟧) * hser M) = 0 := by
    rw [hν, hmain]
    push_cast
    ring
  have hW : (PowerSeries.coeff (2*M+4)) ((Wcert ν : ℚ⟦X⟧) * hser M) = 0 := by
    have hne : ((M:ℚ)+1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hz).resolve_left hne
  -- expand W into the three pieces
  have hsplit : ((Wcert ν : ℚ[X]) : ℚ⟦X⟧) * hser M
      = PowerSeries.C (cP ν) * ((((1+Polynomial.X)^2 : ℚ[X]) : ℚ⟦X⟧) * hser M)
      + PowerSeries.C (c0 ν) * ((((Polynomial.X^2*(1-Polynomial.X^2)) : ℚ[X]) : ℚ⟦X⟧) * hser M)
      + PowerSeries.C (cM ν) * ((((Polynomial.X^4*(1-Polynomial.X)^2) : ℚ[X]) : ℚ⟦X⟧) * hser M) := by
    unfold Wcert
    rw [← map_cP Polynomial.C ν, ← map_c0 Polynomial.C ν, ← map_cM Polynomial.C ν]
    push_cast
    ring
  rw [hsplit] at hW
  rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, coeff_piece1, coeff_piece2, coeff_piece3] at hW
  have eN : ((M+1 : ℕ) : ℚ) = ν := by rw [hν]; push_cast; ring
  rw [eN, show M+1+1 = M+2 by omega, show M+1-1 = M by omega]
  exact hW


end Bala

-- ===== Dev.Products =====
/-!
# Product bookkeeping over integer ranges

Definitions of the window polynomials `Θ', Θ↑, Θ̂`, the content products, and
the three content identities.
-/

namespace Bala

open Polynomial Finset

/-! ## Generic product helpers over `ℤ` -/

section Helpers

variable {M : Type*} [CommMonoid M] (f : ℤ → M)

lemma Ioc_congr {a b c d : ℤ} (h1 : a = c) (h2 : b = d) :
    Finset.Ioc a b = Finset.Ioc c d := by rw [h1, h2]

lemma Ioc_singleton (a : ℤ) : Finset.Ioc (a-1) a = {a} := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_singleton]
  omega

lemma Ioc_succ_single (b : ℤ) : Finset.Ioc b (b+1) = {b+1} := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_singleton]
  omega

lemma prod_Ioc_glue {a b c : ℤ} (h1 : a ≤ b) (h2 : b ≤ c) :
    (∏ j ∈ Finset.Ioc a b, f j) * (∏ j ∈ Finset.Ioc b c, f j)
      = ∏ j ∈ Finset.Ioc a c, f j := by
  rw [← Finset.prod_union (by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Ioc] at hx hx'
    omega), Finset.Ioc_union_Ioc_eq_Ioc h1 h2]

lemma prod_Ioc_top {a b : ℤ} (h : a ≤ b) :
    ∏ j ∈ Finset.Ioc a (b+1), f j = (∏ j ∈ Finset.Ioc a b, f j) * f (b+1) := by
  rw [← prod_Ioc_glue f h (by omega : b ≤ b+1), Ioc_succ_single, Finset.prod_singleton]

lemma prod_Ioc_bot {a b : ℤ} (h : a ≤ b) :
    ∏ j ∈ Finset.Ioc (a-1) b, f j = f a * (∏ j ∈ Finset.Ioc a b, f j) := by
  rw [← prod_Ioc_glue f (by omega : a-1 ≤ a) h, Ioc_singleton, Finset.prod_singleton]

lemma prod_Ioc_shift (a b c : ℤ) :
    ∏ j ∈ Finset.Ioc a b, f (j + c) = ∏ j ∈ Finset.Ioc (a+c) (b+c), f j := by
  rw [← Finset.map_add_right_Ioc, Finset.prod_map]
  rfl

lemma prod_Ioc_reflect (a b c : ℤ) :
    ∏ j ∈ Finset.Ioc a b, f (c - j) = ∏ j ∈ Finset.Ioc (c-b-1) (c-a-1), f j := by
  refine Finset.prod_nbij' (fun j => c - j) (fun j => c - j) ?_ ?_ ?_ ?_ ?_ <;>
    · intro x hx
      simp only [Finset.mem_Ioc] at hx ⊢
      try omega

end Helpers

/-! ## The window polynomials and content products -/

/-- The argument polynomial `m·X + k`. -/
noncomputable def pa (m : ℕ) (k : ℤ) : ℚ[X] := (m : ℚ[X]) * X + (k : ℚ[X])

lemma pa_add_nat (m : ℕ) (k : ℤ) (i : ℕ) :
    pa m k + (i : ℚ[X]) = pa m (k + i) := by
  simp only [pa]
  push_cast
  ring

lemma pa_add_one (m : ℕ) (k : ℤ) : pa m k + 1 = pa m (k+1) := by
  simpa using pa_add_nat m k 1

lemma pa_add_int (m : ℕ) (k d : ℤ) : pa m k + (d : ℚ[X]) = pa m (k + d) := by
  simp only [pa]
  push_cast
  ring

/-- Evaluation of the argument polynomial. -/
@[simp] lemma pa_eval (m : ℕ) (k : ℤ) (t : ℚ) : (pa m k).eval t = m*t + k := by
  simp [pa]

/-- `Θ' m` : the lower window numerator (bottom args `m X + (2-m) … m X - 1`). -/
noncomputable def ThetaLow (m : ℕ) : ℚ[X] := (Wnd (pa m (1-m)) (m-1)).a

/-- `Θ↑ m` : the upper window numerator. -/
noncomputable def ThetaUp (m : ℕ) : ℚ[X] := (Wnd (pa m 1) (m-1)).a

/-- `Θ̂ m` : the long window numerator. -/
noncomputable def ThetaHat (m : ℕ) : ℚ[X] := (Wnd (pa m (1-m)) (2*m-1)).a

/-- `Φ m` : the upper transfer window. -/
noncomputable def PhiW (m : ℕ) : M2 ℚ[X] := Wnd (pa m 1) m

/-- `Ψ m` : the lower transfer window. -/
noncomputable def PsiW (m : ℕ) : M2 ℚ[X] := Wnd (pa m (1-m)) m

/-- Content of `Θ'`. -/
noncomputable def contL (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Ioc (1-m : ℤ) (-1), p1 (pa m j)

/-- Content of `Θ↑`. -/
noncomputable def contU (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Ioc (1 : ℤ) (m-1), p1 (pa m j)

/-- Content of `Θ̂`. -/
noncomputable def contH (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Ioc (1-m : ℤ) (m-1), p1 (pa m j)

/-- The `p1`-part of the common content `𝒞`. -/
noncomputable def bigP1 (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Ioc (1-m : ℤ) m, p1 (pa m j)

/-- `∏_{j=1-m}^{0} cP(mX+j)`. -/
noncomputable def PipM (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Ioc (-m : ℤ) 0, cP (pa m j)

/-- `∏_{j=1}^{m} cP(mX+j)`. -/
noncomputable def PipP (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Ioc (0 : ℤ) m, cP (pa m j)

/-- `∏_{j=1-m}^{0} cM(mX+j)`. -/
noncomputable def DetProd (m : ℕ) : ℚ[X] := ∏ j ∈ Finset.Ioc (-m : ℤ) 0, cM (pa m j)

/-- The linear factor `2m·X + k`. -/
noncomputable def Lm (m : ℕ) (k : ℤ) : ℚ[X] := (2*m : ℚ[X]) * X + (k : ℚ[X])

@[simp] lemma Lm_eval (m : ℕ) (k : ℤ) (t : ℚ) : (Lm m k).eval t = 2*m*t + k := by
  simp [Lm]

/-- `∏_{k=1}^{2m} (2mX + k)`. -/
noncomputable def Aplus (m : ℕ) : ℚ[X] := ∏ k ∈ Finset.Ioc (0 : ℤ) (2*m), Lm m k

/-- `∏_{k=1}^{2m} (2mX - k)`. -/
noncomputable def Aminus (m : ℕ) : ℚ[X] := ∏ k ∈ Finset.Ioc (0 : ℤ) (2*m), Lm m (-k)

lemma two_pa_add_one (m : ℕ) (j : ℤ) : 2 * pa m j + 1 = Lm m (2*j+1) := by
  simp only [pa, Lm]
  push_cast
  ring

lemma two_pa_add_two (m : ℕ) (j : ℤ) : 2 * pa m j + 2 = Lm m (2*j+2) := by
  simp only [pa, Lm]
  push_cast
  ring

lemma two_pa_sub_one (m : ℕ) (j : ℤ) : 2 * pa m j - 1 = Lm m (2*j-1) := by
  simp only [pa, Lm]
  push_cast
  ring

lemma two_pa_sub_two (m : ℕ) (j : ℤ) : 2 * pa m j - 2 = Lm m (2*j-2) := by
  simp only [pa, Lm]
  push_cast
  ring

/-- Splitting of `cP` at an argument `pa m j`. -/
lemma cP_pa_split (m : ℕ) (j : ℤ) :
    cP (pa m j) = Lm m (2*j+1) * Lm m (2*j+2) * p1 (pa m j) := by
  rw [cP_eq_lin_mul_p1, two_pa_add_one, two_pa_add_two]

/-- Splitting of `cM` at an argument `pa m j`. -/
lemma cM_pa_split (m : ℕ) (j : ℤ) :
    cM (pa m j) = -(Lm m (2*j-1) * Lm m (2*j-2) * p1 (pa m (j+1))) := by
  rw [cM_eq_lin_mul_p1, two_pa_sub_one, two_pa_sub_two, pa_add_one]

/-! ## The three content identities -/

section MergeLemmas

variable {M : Type*} [CommMonoid M] (g : ℤ → M)

lemma merge_cp {a b : ℤ} (hab : a ≤ b) :
    ∏ j ∈ Finset.Ioc a b, (g (2*j+1) * g (2*j+2))
      = ∏ k ∈ Finset.Ioc (2*a+2) (2*b+2), g k := by
  induction b, hab using Int.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [prod_Ioc_top _ hb, ih, show (2*(b+1)+2 : ℤ) = (2*b+3)+1 by ring,
      prod_Ioc_top g (by omega : (2*a+2:ℤ) ≤ 2*b+3),
      show (2*b+3 : ℤ) = (2*b+2)+1 by ring,
      prod_Ioc_top g (by omega : (2*a+2:ℤ) ≤ 2*b+2),
      show (2*(b+1)+1 : ℤ) = 2*b+2+1 by ring, mul_assoc]

lemma merge_cm {a b : ℤ} (hab : a ≤ b) :
    ∏ j ∈ Finset.Ioc a b, (g (2*j-2) * g (2*j-1))
      = ∏ k ∈ Finset.Ioc (2*a-1) (2*b-1), g k := by
  induction b, hab using Int.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [prod_Ioc_top _ hb, ih, show (2*(b+1)-1 : ℤ) = (2*b)+1 by ring,
      prod_Ioc_top g (by omega : (2*a-1:ℤ) ≤ 2*b),
      show (2*b : ℤ) = (2*b-1)+1 by ring,
      prod_Ioc_top g (by omega : (2*a-1:ℤ) ≤ 2*b-1),
      show (2*(b+1)-2 : ℤ) = 2*b-1+1 by ring, mul_assoc,
      show (2*b-1+1-1 : ℤ) = 2*b-1 by ring]

end MergeLemmas

section ContentIds

variable (m : ℕ)

/-- Product of `cP` over `Ioc (-1) m` merges the linear factors. -/
lemma cP_prod_split (hm : 1 ≤ m) :
    ∏ j ∈ Finset.Ioc (-1 : ℤ) m, cP (pa m j)
      = (∏ k ∈ Finset.Ioc (0:ℤ) (2*m+2), Lm m k) *
        ∏ j ∈ Finset.Ioc (-1 : ℤ) m, p1 (pa m j) := by
  have step1 : ∏ j ∈ Finset.Ioc (-1 : ℤ) m, cP (pa m j)
      = ∏ j ∈ Finset.Ioc (-1 : ℤ) m, ((Lm m (2*j+1) * Lm m (2*j+2)) * p1 (pa m j)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [cP_pa_split]
  rw [step1, Finset.prod_mul_distrib]
  refine congrArg₂ (· * ·) ?_ rfl
  rw [merge_cp (Lm m) (by omega : (-1:ℤ) ≤ m)]
  exact Finset.prod_congr (Ioc_congr (by omega) (by omega)) (fun _ _ => rfl)

/-- Identity `I₊`. -/
lemma idPlus (hm : 2 ≤ m) :
    PipP m * cP (pa m 0) * contL m
      = Lm m (2*m+1) * Lm m (2*m+2) * bigP1 m * Aplus m := by
  have ha : PipP m * cP (pa m 0) = ∏ j ∈ Finset.Ioc (-1 : ℤ) m, cP (pa m j) := by
    rw [show (-1:ℤ) = 0-1 by ring, prod_Ioc_bot _ (by omega : (0:ℤ) ≤ m)]
    unfold PipP
    ring
  rw [ha, cP_prod_split m (by omega)]
  have hd : ∏ k ∈ Finset.Ioc (0:ℤ) (2*m+2), Lm m k
      = Aplus m * Lm m (2*m+1) * Lm m (2*m+2) := by
    have t1 := prod_Ioc_top (Lm m) (by omega : (0:ℤ) ≤ 2*m+1)
    have t2 := prod_Ioc_top (Lm m) (by omega : (0:ℤ) ≤ 2*m)
    rw [show (2*(m:ℤ)+1)+1 = 2*m+2 by ring] at t1
    rw [show (2*(m:ℤ))+1 = 2*m+1 by ring] at t2
    rw [t1, t2]
    unfold Aplus
    ring
  have he : contL m * ∏ j ∈ Finset.Ioc (-1 : ℤ) m, p1 (pa m j) = bigP1 m := by
    unfold contL bigP1
    exact prod_Ioc_glue _ (by omega : (1-(m:ℤ)) ≤ -1) (by omega : (-1:ℤ) ≤ m)
  calc (∏ k ∈ Finset.Ioc (0:ℤ) (2*m+2), Lm m k) *
        (∏ j ∈ Finset.Ioc (-1 : ℤ) m, p1 (pa m j)) * contL m
      = (∏ k ∈ Finset.Ioc (0:ℤ) (2*m+2), Lm m k) *
        (contL m * ∏ j ∈ Finset.Ioc (-1 : ℤ) m, p1 (pa m j)) := by ring
    _ = _ := by rw [he, hd]; ring

/-- Top-append for the big `p1` product. -/
lemma bigP1_top (hm : 2 ≤ m) : bigP1 m = contH m * p1 (pa m m) := by
  have t := prod_Ioc_top (fun j => p1 (pa m j)) (by omega : (1-(m:ℤ)) ≤ m-1)
  rw [show ((m:ℤ)-1)+1 = m by ring] at t
  unfold bigP1 contH
  rw [t]

/-- Identity `I_c`. -/
lemma idC (hm : 2 ≤ m) :
    cP (pa m m) * contH m = Lm m (2*m+1) * Lm m (2*m+2) * bigP1 m := by
  rw [cP_pa_split, bigP1_top m hm]
  ring

/-- Identity `I₋`. -/
lemma idMinus (hm : 2 ≤ m) :
    cP (pa m m) * contU m * DetProd m
      = Lm m (2*m+1) * Lm m (2*m+2) * bigP1 m * ((-1)^m * Aminus m) := by
  -- split cM factors
  have hsplit : DetProd m = (-1)^m *
      ((∏ k ∈ Finset.Ioc (-2*(m:ℤ)-1) (-1), Lm m k) *
       ∏ j ∈ Finset.Ioc (1-(m:ℤ)) 1, p1 (pa m j)) := by
    unfold DetProd
    have step1 : ∏ j ∈ Finset.Ioc (-(m:ℤ)) 0, cM (pa m j)
        = ∏ j ∈ Finset.Ioc (-(m:ℤ)) 0,
            ((-1) * ((Lm m (2*j-2) * Lm m (2*j-1)) * p1 (pa m (j+1)))) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [cM_pa_split]
      ring
    rw [step1, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    have hcard : (Finset.Ioc (-(m:ℤ)) 0).card = m := by
      rw [Int.card_Ioc]
      omega
    rw [hcard]
    refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) ?_ ?_)
    · -- linear part
      rw [merge_cm (Lm m) (by omega : (-(m:ℤ)) ≤ 0)]
      exact Finset.prod_congr (Ioc_congr (by omega) (by omega)) (fun _ _ => rfl)
    · -- p1 part
      have hsh := prod_Ioc_shift (fun j => p1 (pa m j)) (-(m:ℤ)) 0 1
      rw [show -(m:ℤ)+1 = 1-m by ring, show ((0:ℤ)+1) = 1 by norm_num] at hsh
      exact hsh
  -- Aminus reversal
  have hrev : Aminus m = ∏ k ∈ Finset.Ioc (-2*(m:ℤ)-1) (-1), Lm m k := by
    unfold Aminus
    have hr := prod_Ioc_reflect (Lm m) 0 (2*m) 0
    have : ∀ k : ℤ, Lm m (-k) = Lm m (0 - k) := fun k => by rw [zero_sub]
    rw [Finset.prod_congr rfl (fun k _ => this k), hr]
    exact Finset.prod_congr (Ioc_congr (by omega) (by omega)) (fun _ _ => rfl)
  -- p1 glue
  have hp1 : (∏ j ∈ Finset.Ioc (1-(m:ℤ)) 1, p1 (pa m j)) * contU m * p1 (pa m m)
      = bigP1 m := by
    unfold contU
    rw [prod_Ioc_glue _ (by omega : (1-(m:ℤ)) ≤ 1) (by omega : (1:ℤ) ≤ m-1),
      bigP1_top m hm]
    unfold contH
    rfl
  rw [cP_pa_split, hsplit, ← hrev, ← hp1]
  ring

end ContentIds


/-! ## Peeling and determinant lemmas -/

section Peel

variable (m : ℕ)

lemma PsiW_c (hm : 1 ≤ m) : (PsiW m).c = cP (pa m 0) * ThetaLow m := by
  unfold PsiW ThetaLow
  obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
  rw [show m'+1-1 = m' by omega, Wnd_c_peel, pa_add_nat,
    show (1 - ((m'+1 : ℕ):ℤ) + (m' : ℤ)) = 0 by omega]

lemma PhiW_c (hm : 1 ≤ m) : (PhiW m).c = cP (pa m m) * ThetaUp m := by
  unfold PhiW ThetaUp
  obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
  rw [show m'+1-1 = m' by omega, Wnd_c_peel, pa_add_nat,
    show ((1 : ℤ) + (m' : ℤ)) = ((m'+1 : ℕ) : ℤ) by omega]

lemma PhiPsi (hm : 1 ≤ m) : (PhiW m).mul (PsiW m) = Wnd (pa m (1-m)) (2*m) := by
  unfold PhiW PsiW
  rw [show 2*m = m + m by omega, Wnd_split, pa_add_nat,
    show (1 - (m:ℤ) + (m : ℤ)) = 1 by omega]

lemma PhiPsi_c (hm : 1 ≤ m) :
    ((PhiW m).mul (PsiW m)).c = cP (pa m m) * ThetaHat m := by
  rw [PhiPsi m hm]
  unfold ThetaHat
  obtain ⟨L, hL⟩ : ∃ L, 2*m = L+1 := ⟨2*m-1, by omega⟩
  rw [show 2*m-1 = L by omega, hL, Wnd_c_peel, pa_add_nat,
    show (1 - (m:ℤ) + (L : ℤ)) = (m:ℤ) by omega]

lemma prod_range_to_Ioc {M : Type*} [CommMonoid M] (F : ℤ → M) (k₀ : ℤ) (n : ℕ) :
    ∏ i ∈ Finset.range n, F (k₀ + i) = ∏ j ∈ Finset.Ioc (k₀-1) (k₀-1+n), F j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih,
      show (k₀-1+((n+1):ℕ) : ℤ) = (k₀-1+n)+1 by push_cast; ring,
      prod_Ioc_top F (by omega : k₀-1 ≤ k₀-1+n)]
    congr 2
    omega

lemma PsiW_det (hm : 1 ≤ m) : (PsiW m).det = PipM m * DetProd m := by
  unfold PsiW PipM DetProd
  rw [Wnd_det]
  have step : ∀ i ∈ Finset.range m,
      cP (pa m (1-m) + (i:ℚ[X])) * cM (pa m (1-m) + (i:ℚ[X]))
        = (fun j => cP (pa m j) * cM (pa m j)) ((1-(m:ℤ)) + i) := by
    intro i _
    rw [pa_add_nat]
  rw [Finset.prod_congr rfl step,
    prod_range_to_Ioc (fun j => cP (pa m j) * cM (pa m j)) (1-(m:ℤ)) m,
    Finset.prod_mul_distrib]
  congr 1 <;>
    exact Finset.prod_congr (Ioc_congr (by omega) (by omega)) (fun _ _ => rfl)

end Peel

/-! ## Divisibility of the window numerators by the contents -/

section Dvd

/-- The two-step divisibility kernel. -/
lemma p1_dvd_Wnd (b : ℚ[X]) (s : ℕ) :
    (p1 (b + (s:ℚ[X]) + 1) ∣ (Wnd b (s+2)).a) ∧
    (p1 (b + (s:ℚ[X]) + 1) ∣ (Wnd b (s+2)).c) := by
  set p : ℚ[X] := b + (s:ℚ[X]) + 1 with hp
  have e1 : b + ((s+1 : ℕ) : ℚ[X]) = p := by rw [hp]; push_cast; ring
  have e2 : b + ((s : ℕ) : ℚ[X]) = p - 1 := by rw [hp]; ring
  have htop : Wnd b (s+2) = (Mstep p).mul ((Mstep (p-1)).mul (Wnd b s)) := by
    rw [show s+2 = (s+1)+1 from rfl, Wnd_succ, Wnd_succ, e1, e2]
  constructor
  · rw [htop]
    have key : ((Mstep p).mul ((Mstep (p-1)).mul (Wnd b s))).a
        = p1 p * ((9760*p^6 - 29280*p^5 + 15252*p^4 + 18296*p^3 - 12448*p^2 - 1580*p + 1152)
              * (Wnd b s).a
            + (c0 p * (-((2*p-3)*(2*p-4)))) * (Wnd b s).c) := by
      have h1 := magic1 p
      have h2 := magic2 p
      simp only [M2.mul_a, M2.mul_c, Mstep_a, Mstep_b, Mstep_c, Mstep_d]
      linear_combination (Wnd b s).a * h1 + ((c0 p) * (Wnd b s).c) * h2
    exact ⟨_, key⟩
  · rw [htop]
    have key : ((Mstep p).mul ((Mstep (p-1)).mul (Wnd b s))).c
        = p1 p * (((2*p+1)*(2*p+2)) * ((Mstep (p-1)).mul (Wnd b s)).a) := by
      simp only [M2.mul_c, Mstep_c, Mstep_d]
      rw [cP_eq_lin_mul_p1]
      ring
    exact ⟨_, key⟩

lemma p1_dvd_Wnd_a (b : ℚ[X]) (s rest : ℕ) :
    p1 (b + (s:ℚ[X]) + 1) ∣ (Wnd b (s+2+rest)).a := by
  rw [Wnd_split b (s+2) rest, M2.mul_a]
  exact dvd_add ((p1_dvd_Wnd b s).1.mul_left _) ((p1_dvd_Wnd b s).2.mul_left _)

/-- Any interior `p1`-factor divides the window numerator. -/
lemma p1_pa_dvd_theta (m : ℕ) (L : ℕ) (j : ℤ) (h1 : 2-(m:ℤ) ≤ j)
    (h2 : j ≤ 1-(m:ℤ)+L-1) :
    p1 (pa m j) ∣ (Wnd (pa m (1-(m:ℤ))) L).a := by
  set t : ℕ := (j - (1-(m:ℤ))).toNat with ht
  have htz : (t:ℤ) = j - (1-(m:ℤ)) := by
    rw [ht]
    omega
  have h1t : 1 ≤ t := by omega
  have hL : L = (t-1)+2+(L-1-t) := by omega
  have harg : pa m j = pa m (1-(m:ℤ)) + ((t-1 : ℕ) : ℚ[X]) + 1 := by
    rw [pa_add_nat, pa_add_one]
    congr 1
    omega
  rw [hL, harg]
  exact p1_dvd_Wnd_a _ _ _

/-- Distinct `p1 (pa m ·)` factors are coprime. -/
lemma p1_pa_coprime (m : ℕ) {j j' : ℤ} (h : j < j') :
    IsCoprime (p1 (pa m j)) (p1 (pa m j')) := by
  set d : ℤ := j' - j with hd
  have hd1 : 1 ≤ d := by omega
  have hb := p1_bezout (pa m j) ((d : ℚ[X]))
  rw [pa_add_int, show j + d = j' by omega] at hb
  set c : ℚ := 5*(d:ℚ)^3 - (d:ℚ) with hc
  have hcne : c ≠ 0 := by
    have h1 : (1:ℚ) ≤ (d:ℚ) := by exact_mod_cast hd1
    have hpos : (0:ℚ) ≤ ((d:ℚ)-1) * (5*(d:ℚ)^2+5*(d:ℚ)+4) :=
      mul_nonneg (by linarith) (by linarith [sq_nonneg ((d:ℚ))])
    have h4 : (4:ℚ) ≤ c := by
      rw [hc]
      linarith [hpos]
    linarith
  have hCc : (5*((d:ℚ[X]))^3 - ((d:ℤ) : ℚ[X])) = C c := by
    rw [hc]
    simp only [Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, map_ofNat, Polynomial.C_eq_intCast]
  refine ⟨C c⁻¹ * (2*(pa m j)+3*((d:ℚ[X]))-1), C c⁻¹ * (-(2*(pa m j))+((d:ℚ[X]))+1), ?_⟩
  have hone : C c⁻¹ * C c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hcne, map_one]
  calc C c⁻¹ * (2*(pa m j)+3*((d:ℚ[X]))-1) * p1 (pa m j)
        + C c⁻¹ * (-(2*(pa m j))+((d:ℚ[X]))+1) * p1 (pa m j')
      = C c⁻¹ * ((2*(pa m j)+3*((d:ℚ[X]))-1) * p1 (pa m j)
          + (-(2*(pa m j))+((d:ℚ[X]))+1) * p1 (pa m j')) := by ring
    _ = C c⁻¹ * C c := by rw [hb, hCc]
    _ = 1 := hone

lemma contL_dvd (m : ℕ) : contL m ∣ ThetaLow m := by
  unfold contL ThetaLow
  apply Finset.prod_dvd_of_coprime
  · intro x hx y hy hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact p1_pa_coprime m h
    · exact (p1_pa_coprime m h).symm
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    exact p1_pa_dvd_theta m (m-1) j (by omega) (by push_cast; omega)

lemma contH_dvd (m : ℕ) : contH m ∣ ThetaHat m := by
  unfold contH ThetaHat
  apply Finset.prod_dvd_of_coprime
  · intro x hx y hy hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact p1_pa_coprime m h
    · exact (p1_pa_coprime m h).symm
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    exact p1_pa_dvd_theta m (2*m-1) j (by omega) (by push_cast; omega)

end Dvd


/-! ## Duality via composition -/

section Duality

open Polynomial

/-- Composition with a fixed polynomial, as a ring homomorphism. -/
noncomputable def compHom (q : ℚ[X]) : ℚ[X] →+* ℚ[X] := eval₂RingHom C q

lemma compHom_apply (q p : ℚ[X]) : compHom q p = p.comp q := rfl

lemma Wnd_a_comp (b q : ℚ[X]) (len : ℕ) :
    ((Wnd b len).a).comp q = (Wnd (b.comp q) len).a := by
  have h := Wnd_emap (compHom q) b len
  calc ((Wnd b len).a).comp q = (M2.emap (compHom q) (Wnd b len)).a := rfl
    _ = (Wnd (compHom q b) len).a := by rw [h]
    _ = (Wnd (b.comp q) len).a := by rw [compHom_apply]

lemma prod_comp (s : Finset ℤ) (f : ℤ → ℚ[X]) (q : ℚ[X]) :
    (∏ j ∈ s, f j).comp q = ∏ j ∈ s, (f j).comp q :=
  map_prod (compHom q) f s

variable (m : ℕ)

/-- `Θ'(-X) = Θ↑`. -/
lemma theta_up_eq (hm : 1 ≤ m) : (ThetaLow m).comp (-X) = ThetaUp m := by
  unfold ThetaLow ThetaUp
  rw [Wnd_a_comp]
  rw [show (pa m (1-(m:ℤ))).comp (-X) = 1 - pa m 1 - ((m-1:ℕ) : ℚ[X]) by
    simp only [pa, add_comp, mul_comp, natCast_comp, intCast_comp, X_comp]
    push_cast [Nat.cast_sub hm]
    ring]
  rw [← Wnd_transpose, M2.transpose_a]

/-- `Θ'(1-X) = Θ'`. -/
lemma theta_symm (hm : 1 ≤ m) : (ThetaLow m).comp (1-X) = ThetaLow m := by
  unfold ThetaLow
  rw [Wnd_a_comp]
  rw [show (pa m (1-(m:ℤ))).comp (1-X) = 1 - pa m (1-(m:ℤ)) - ((m-1:ℕ) : ℚ[X]) by
    simp only [pa, add_comp, mul_comp, natCast_comp, intCast_comp, X_comp, one_comp,
      sub_comp]
    push_cast [Nat.cast_sub hm]
    ring]
  rw [← Wnd_transpose, M2.transpose_a]

/-- `Θ̂(-X) = Θ̂`. -/
lemma thetahat_even (hm : 1 ≤ m) : (ThetaHat m).comp (-X) = ThetaHat m := by
  unfold ThetaHat
  rw [Wnd_a_comp]
  rw [show (pa m (1-(m:ℤ))).comp (-X) = 1 - pa m (1-(m:ℤ)) - ((2*m-1:ℕ) : ℚ[X]) by
    simp only [pa, add_comp, mul_comp, natCast_comp, intCast_comp, X_comp]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2*m)]
    ring]
  rw [← Wnd_transpose, M2.transpose_a]

lemma p1_pa_comp_neg (j : ℤ) : (p1 (pa m j)).comp (-X) = p1 (pa m (1-j)) := by
  rw [comp_p1]
  rw [show (pa m j).comp (-X) = -(pa m (-j)) by
    simp only [pa, add_comp, mul_comp, natCast_comp, intCast_comp, X_comp]
    push_cast
    ring]
  rw [p1_neg, pa_add_one, show -j+1 = 1-j by ring]

lemma p1_pa_comp_reflect (j : ℤ) :
    (p1 (pa m j)).comp (1-X) = p1 (pa m (1-(m:ℤ)-j)) := by
  rw [comp_p1]
  rw [show (pa m j).comp (1-X) = -(pa m (-(m:ℤ)-j)) by
    simp only [pa, add_comp, mul_comp, natCast_comp, intCast_comp, X_comp, one_comp,
      sub_comp]
    push_cast
    ring]
  rw [p1_neg, pa_add_one, show -(m:ℤ)-j+1 = 1-(m:ℤ)-j by ring]

/-- `contL(-X) = contU`. -/
lemma contL_comp_neg : (contL m).comp (-X) = contU m := by
  unfold contL contU
  rw [prod_comp]
  calc ∏ j ∈ Finset.Ioc (1-(m:ℤ)) (-1), (p1 (pa m j)).comp (-X)
      = ∏ j ∈ Finset.Ioc (1-(m:ℤ)) (-1), p1 (pa m (1-j)) :=
        Finset.prod_congr rfl (fun j _ => p1_pa_comp_neg m j)
    _ = ∏ j ∈ Finset.Ioc (1:ℤ) (m-1), p1 (pa m j) :=
        (prod_Ioc_reflect (fun j => p1 (pa m j)) (1-(m:ℤ)) (-1) 1).trans
          (Finset.prod_congr (Ioc_congr (by omega) (by omega)) (fun _ _ => rfl))

/-- `contL(1-X) = contL`. -/
lemma contL_comp_reflect : (contL m).comp (1-X) = contL m := by
  unfold contL
  rw [prod_comp]
  calc ∏ j ∈ Finset.Ioc (1-(m:ℤ)) (-1), (p1 (pa m j)).comp (1-X)
      = ∏ j ∈ Finset.Ioc (1-(m:ℤ)) (-1), p1 (pa m (1-(m:ℤ)-j)) :=
        Finset.prod_congr rfl (fun j _ => p1_pa_comp_reflect m j)
    _ = ∏ j ∈ Finset.Ioc (1-(m:ℤ)) (-1), p1 (pa m j) :=
        (prod_Ioc_reflect (fun j => p1 (pa m j)) (1-(m:ℤ)) (-1) (1-(m:ℤ))).trans
          (Finset.prod_congr (Ioc_congr (by omega) (by omega)) (fun _ _ => rfl))

/-- `contH(-X) = contH`. -/
lemma contH_comp_neg : (contH m).comp (-X) = contH m := by
  unfold contH
  rw [prod_comp]
  calc ∏ j ∈ Finset.Ioc (1-(m:ℤ)) (m-1), (p1 (pa m j)).comp (-X)
      = ∏ j ∈ Finset.Ioc (1-(m:ℤ)) (m-1), p1 (pa m (1-j)) :=
        Finset.prod_congr rfl (fun j _ => p1_pa_comp_neg m j)
    _ = ∏ j ∈ Finset.Ioc (1-(m:ℤ)) (m-1), p1 (pa m j) :=
        (prod_Ioc_reflect (fun j => p1 (pa m j)) (1-(m:ℤ)) (m-1) 1).trans
          (Finset.prod_congr (Ioc_congr (by omega) (by omega)) (fun _ _ => rfl))

end Duality

/-! ## Degrees -/

section Degrees

open Polynomial

lemma pa_eq_C (m : ℕ) (k : ℤ) : pa m k = C (m:ℚ) * X + C (k:ℚ) := by
  rw [pa, Polynomial.C_eq_natCast, Polynomial.C_eq_intCast]

lemma pa_natDegree_le (m : ℕ) (k : ℤ) : (pa m k).natDegree ≤ 1 := by
  rw [pa_eq_C]
  compute_degree

lemma pa_coeff_one (m : ℕ) (k : ℤ) : (pa m k).coeff 1 = m := by
  rw [pa_eq_C, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]
  norm_num

lemma term_natDegree_le (q : ℚ[X]) (hq : q.natDegree ≤ 1) (r : ℚ) (k : ℕ) (hk : k ≤ 4) :
    (C r * q^k).natDegree ≤ 4 := by
  refine natDegree_mul_le.trans ?_
  have h1 : (q^k).natDegree ≤ k * q.natDegree := natDegree_pow_le
  have h2 : k * q.natDegree ≤ k * 1 := Nat.mul_le_mul_left k hq
  simp only [natDegree_C]
  omega

lemma term_coeff4 (q : ℚ[X]) (hq : q.natDegree ≤ 1) (r : ℚ) (k : ℕ) (hk : k ≤ 3) :
    (C r * q^k).coeff 4 = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h1 : (q^k).natDegree ≤ k * q.natDegree := natDegree_pow_le
  have h2 : k * q.natDegree ≤ k * 1 := Nat.mul_le_mul_left k hq
  calc (C r * q^k).natDegree ≤ (C r).natDegree + (q^k).natDegree := natDegree_mul_le
    _ < 4 := by simp only [natDegree_C]; omega

lemma coeff_smul_pow4' (q : ℚ[X]) (hq : q.natDegree ≤ 1) (r : ℚ) :
    (C r * q^4).coeff 4 = r * (q.coeff 1)^4 := by
  rw [coeff_C_mul, show (4:ℕ) = 4*1 by norm_num, coeff_pow_of_natDegree_le hq]

/-- Entry `A = -c0` of the step matrix: degree data. -/
lemma entryA_facts (q : ℚ[X]) (hq : q.natDegree ≤ 1) :
    (-(c0 q)).natDegree ≤ 4 ∧ (-(c0 q)).coeff 4 = 220 * (q.coeff 1)^4 := by
  have he : -(c0 q) = C 220 * q^4 + (C (-136) * q^2 + C 12 * q^0) := by
    simp only [c0, Polynomial.C_neg, map_ofNat]
    ring
  constructor
  · rw [he]
    exact natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
      (natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
        (term_natDegree_le q hq _ _ (by norm_num)))
  · rw [he, coeff_add, coeff_add, coeff_smul_pow4' q hq,
      term_coeff4 q hq _ _ (by norm_num), term_coeff4 q hq _ _ (by norm_num)]
    ring

/-- Entry `B = -cM` of the step matrix: degree data. -/
lemma entryB_facts (q : ℚ[X]) (hq : q.natDegree ≤ 1) :
    (-(cM q)).natDegree ≤ 4 ∧ (-(cM q)).coeff 4 = 20 * (q.coeff 1)^4 := by
  have he : -(cM q) = C 20 * q^4 + (C (-10) * q^3 + (C (-16) * q^2 +
      (C 4 * q^1 + C 2 * q^0))) := by
    simp only [cM, Polynomial.C_neg, map_ofNat]
    ring
  constructor
  · rw [he]
    exact natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
      (natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
        (natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
          (natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
            (term_natDegree_le q hq _ _ (by norm_num)))))
  · rw [he, coeff_add, coeff_add, coeff_add, coeff_add, coeff_smul_pow4' q hq,
      term_coeff4 q hq _ _ (by norm_num), term_coeff4 q hq _ _ (by norm_num),
      term_coeff4 q hq _ _ (by norm_num), term_coeff4 q hq _ _ (by norm_num)]
    ring

/-- Entry `C = cP` of the step matrix: degree data. -/
lemma entryC_facts (q : ℚ[X]) (hq : q.natDegree ≤ 1) :
    (cP q).natDegree ≤ 4 ∧ (cP q).coeff 4 = 20 * (q.coeff 1)^4 := by
  have he : cP q = C 20 * q^4 + (C 10 * q^3 + (C (-16) * q^2 +
      (C (-4) * q^1 + C 2 * q^0))) := by
    simp only [cP, Polynomial.C_neg, map_ofNat]
    ring
  constructor
  · rw [he]
    exact natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
      (natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
        (natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
          (natDegree_add_le_of_degree_le (term_natDegree_le q hq _ _ (by norm_num))
            (term_natDegree_le q hq _ _ (by norm_num)))))
  · rw [he, coeff_add, coeff_add, coeff_add, coeff_add, coeff_smul_pow4' q hq,
      term_coeff4 q hq _ _ (by norm_num), term_coeff4 q hq _ _ (by norm_num),
      term_coeff4 q hq _ _ (by norm_num), term_coeff4 q hq _ _ (by norm_num)]
    ring

/-- Window entry degree invariant: for a window with linear argument `b`
(with `b.coeff 1 = c > 0`), the `a`-entry has `natDegree ≤ 4·len` with
strictly positive coefficient there, and the `c`-entry has `natDegree ≤ 4·len`
with nonnegative coefficient there. -/
lemma Wnd_deg (b : ℚ[X]) (hb : b.natDegree ≤ 1) (c : ℚ) (hc : 0 < c)
    (hbc : b.coeff 1 = c) (len : ℕ) :
    (Wnd b len).a.natDegree ≤ 4*len ∧ 0 < (Wnd b len).a.coeff (4*len) ∧
    (Wnd b len).c.natDegree ≤ 4*len ∧ 0 ≤ (Wnd b len).c.coeff (4*len) := by
  induction len with
  | zero =>
    simp [M2.one]
  | succ n ih =>
    obtain ⟨ha1, ha2, hc1, hc2⟩ := ih
    have harg : (b + (n:ℚ[X])).natDegree ≤ 1 := by
      refine natDegree_add_le_of_degree_le hb ?_
      simp
    have hargc : (b + (n:ℚ[X])).coeff 1 = c := by
      rw [coeff_add, hbc, Polynomial.coeff_natCast_ite]
      norm_num
    obtain ⟨hA1, hA2⟩ := entryA_facts _ harg
    obtain ⟨hB1, hB2⟩ := entryB_facts _ harg
    obtain ⟨hC1, hC2⟩ := entryC_facts _ harg
    rw [hargc] at hA2 hB2 hC2
    rw [Wnd_succ]
    have hmul : ∀ (f g : ℚ[X]), f.natDegree ≤ 4 → g.natDegree ≤ 4*n →
        (f*g).natDegree ≤ 4*(n+1) ∧ (f*g).coeff (4*(n+1)) = f.coeff 4 * g.coeff (4*n) := by
      intro f g hf hg
      constructor
      · exact natDegree_mul_le.trans (by omega)
      · rw [show 4*(n+1) = 4 + 4*n by ring]
        exact coeff_mul_add_eq_of_natDegree_le hf hg
    have hc4 : (0:ℚ) < c^4 := by positivity
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [M2.mul_a, Mstep_a, Mstep_b]
      exact natDegree_add_le_of_degree_le (hmul _ _ hA1 ha1).1 (hmul _ _ hB1 hc1).1
    · rw [M2.mul_a, Mstep_a, Mstep_b]
      rw [coeff_add, (hmul _ _ hA1 ha1).2, (hmul _ _ hB1 hc1).2, hA2, hB2]
      have t1 : 0 < 220 * c^4 * (Wnd b n).a.coeff (4*n) := by positivity
      have t2 : 0 ≤ 20 * c^4 * (Wnd b n).c.coeff (4*n) := by positivity
      linarith
    · rw [M2.mul_c, Mstep_c, Mstep_d]
      rw [zero_mul, add_zero]
      exact (hmul _ _ hC1 ha1).1
    · rw [M2.mul_c, Mstep_c, Mstep_d]
      rw [zero_mul, add_zero, (hmul _ _ hC1 ha1).2, hC2]
      positivity

end Degrees



end Bala

-- ===== Dev.Theta =====
/-!
# Degrees of the window numerators, and the quotients `Pq`, `Qhat`

`Pq m` is the polynomial `P(2m, ·)` of the conjecture (over `ℚ`), obtained
as `ThetaLow m / contL m`; `Qhat m = ThetaHat m / contH m` is `Q(2m, ·²)`.
-/

namespace Bala

open Polynomial Finset

section TermHelpers

/-- `(C r * q^k).natDegree ≤ d` for linear `q` and `k ≤ d`. -/
lemma term_natDegree_le_gen (q : ℚ[X]) (hq : q.natDegree ≤ 1) (r : ℚ) (k d : ℕ)
    (hk : k ≤ d) : (C r * q^k).natDegree ≤ d := by
  refine natDegree_mul_le.trans ?_
  have h1 : (q^k).natDegree ≤ k * q.natDegree := natDegree_pow_le
  have h2 : k * q.natDegree ≤ k * 1 := Nat.mul_le_mul_left k hq
  simp only [natDegree_C]
  omega

lemma term_coeff_gen (q : ℚ[X]) (hq : q.natDegree ≤ 1) (r : ℚ) (k d : ℕ)
    (hk : k < d) : (C r * q^k).coeff d = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  have h1 : (q^k).natDegree ≤ k * q.natDegree := natDegree_pow_le
  have h2 : k * q.natDegree ≤ k * 1 := Nat.mul_le_mul_left k hq
  calc (C r * q^k).natDegree ≤ (C r).natDegree + (q^k).natDegree := natDegree_mul_le
    _ < d := by simp only [natDegree_C]; omega

lemma coeff_smul_pow_top (q : ℚ[X]) (hq : q.natDegree ≤ 1) (r : ℚ) (d : ℕ) :
    (C r * q^d).coeff d = r * (q.coeff 1)^d := by
  rw [coeff_C_mul]
  have h := coeff_pow_of_natDegree_le (m := d) hq
  norm_num at h
  rw [h]

end TermHelpers

section DegreeFacts

variable (m : ℕ)

/-- Degree data for `Θ'`. -/
lemma ThetaLow_deg (hm : 1 ≤ m) :
    (ThetaLow m).natDegree = 4*(m-1) ∧ 0 < (ThetaLow m).coeff (4*(m-1)) := by
  have hc : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have h := Wnd_deg (pa m (1-(m:ℤ))) (pa_natDegree_le m _) m hc (pa_coeff_one m _) (m-1)
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero h.1 (ne_of_gt h.2.1), h.2.1⟩

/-- Degree data for `Θ̂`. -/
lemma ThetaHat_deg (hm : 1 ≤ m) :
    (ThetaHat m).natDegree = 4*(2*m-1) ∧ 0 < (ThetaHat m).coeff (4*(2*m-1)) := by
  have hc : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have h := Wnd_deg (pa m (1-(m:ℤ))) (pa_natDegree_le m _) m hc (pa_coeff_one m _) (2*m-1)
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero h.1 (ne_of_gt h.2.1), h.2.1⟩

lemma ThetaLow_ne_zero (hm : 1 ≤ m) : ThetaLow m ≠ 0 := by
  intro h
  have := (ThetaLow_deg m hm).2
  rw [h] at this
  simp at this

lemma ThetaHat_ne_zero (hm : 1 ≤ m) : ThetaHat m ≠ 0 := by
  intro h
  have := (ThetaHat_deg m hm).2
  rw [h] at this
  simp at this

/-- Degree data for `p1` of a linear argument. -/
lemma p1_deg_facts (q : ℚ[X]) (hq : q.natDegree ≤ 1) :
    (p1 q).natDegree ≤ 2 ∧ (p1 q).coeff 2 = 5 * (q.coeff 1)^2 := by
  have he : p1 q = C 5 * q^2 + (C (-5) * q^1 + C 1 * q^0) := by
    simp only [p1, Polynomial.C_neg, map_ofNat, Polynomial.C_1]
    ring
  constructor
  · rw [he]
    exact natDegree_add_le_of_degree_le (term_natDegree_le_gen q hq _ _ _ (by norm_num))
      (natDegree_add_le_of_degree_le (term_natDegree_le_gen q hq _ _ _ (by norm_num))
        (term_natDegree_le_gen q hq _ _ _ (by norm_num)))
  · rw [he, coeff_add, coeff_add, coeff_smul_pow_top q hq,
      term_coeff_gen q hq _ _ _ (by norm_num), term_coeff_gen q hq _ _ _ (by norm_num)]
    ring

lemma p1_pa_natDegree (hm : 1 ≤ m) (j : ℤ) : (p1 (pa m j)).natDegree = 2 := by
  have hc : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have h := p1_deg_facts (pa m j) (pa_natDegree_le m j)
  refine natDegree_eq_of_le_of_coeff_ne_zero h.1 ?_
  rw [h.2, pa_coeff_one]
  positivity

lemma p1_pa_leadingCoeff (hm : 1 ≤ m) (j : ℤ) :
    (p1 (pa m j)).leadingCoeff = 5 * (m:ℚ)^2 := by
  rw [leadingCoeff, p1_pa_natDegree m hm j, (p1_deg_facts (pa m j) (pa_natDegree_le m j)).2,
    pa_coeff_one]

lemma p1_pa_ne_zero (hm : 1 ≤ m) (j : ℤ) : p1 (pa m j) ≠ 0 := by
  have hc : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  intro h
  have := p1_pa_leadingCoeff m hm j
  rw [h] at this
  simp only [leadingCoeff_zero] at this
  linarith [mul_pos hc hc]

/-- Degree data for products of `p1 (pa m ·)`. -/
lemma prod_p1_deg (hm : 1 ≤ m) (s : Finset ℤ) :
    (∏ j ∈ s, p1 (pa m j)).natDegree = 2 * s.card ∧
    0 < (∏ j ∈ s, p1 (pa m j)).leadingCoeff := by
  have hc : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  constructor
  · rw [natDegree_prod _ _ (fun j _ => p1_pa_ne_zero m hm j),
      Finset.sum_congr rfl (fun j _ => p1_pa_natDegree m hm j), Finset.sum_const,
      smul_eq_mul, mul_comm]
  · rw [leadingCoeff_prod]
    apply Finset.prod_pos
    intro j _
    rw [p1_pa_leadingCoeff m hm j]
    positivity

lemma contL_card (hm : 1 ≤ m) : (Finset.Ioc (1-(m:ℤ)) (-1)).card = m-2 := by
  rw [Int.card_Ioc]
  omega

lemma contH_card (hm : 1 ≤ m) : (Finset.Ioc (1-(m:ℤ)) ((m:ℤ)-1)).card = 2*m-2 := by
  rw [Int.card_Ioc]
  omega

lemma contL_facts (hm : 1 ≤ m) :
    (contL m).natDegree = 2*(m-2) ∧ 0 < (contL m).leadingCoeff := by
  have h := prod_p1_deg m hm (Finset.Ioc (1-(m:ℤ)) (-1))
  rw [contL_card m hm] at h
  exact ⟨h.1, h.2⟩

lemma contH_facts (hm : 1 ≤ m) :
    (contH m).natDegree = 2*(2*m-2) ∧ 0 < (contH m).leadingCoeff := by
  have h := prod_p1_deg m hm (Finset.Ioc (1-(m:ℤ)) ((m:ℤ)-1))
  rw [contH_card m hm] at h
  exact ⟨h.1, h.2⟩

lemma contL_ne_zero (hm : 1 ≤ m) : contL m ≠ 0 :=
  leadingCoeff_ne_zero.mp (ne_of_gt (contL_facts m hm).2)

lemma contH_ne_zero (hm : 1 ≤ m) : contH m ≠ 0 :=
  leadingCoeff_ne_zero.mp (ne_of_gt (contH_facts m hm).2)

end DegreeFacts

/-! ## The quotients -/

section Quotients

open scoped Classical in
/-- `P(2m, ·)` : the quotient of `Θ'` by its content. -/
noncomputable def Pq (m : ℕ) : ℚ[X] :=
  if h : contL m ∣ ThetaLow m then h.choose else 1

open scoped Classical in
/-- `Q(2m, ·²)` : the quotient of `Θ̂` by its content. -/
noncomputable def Qhat (m : ℕ) : ℚ[X] :=
  if h : contH m ∣ ThetaHat m then h.choose else 1

lemma Pq_spec (m : ℕ) : ThetaLow m = contL m * Pq m := by
  have h := contL_dvd m
  rw [Pq, dif_pos h]
  exact h.choose_spec

lemma Qhat_spec (m : ℕ) : ThetaHat m = contH m * Qhat m := by
  have h := contH_dvd m
  rw [Qhat, dif_pos h]
  exact h.choose_spec

variable (m : ℕ)

lemma Pq_ne_zero (hm : 1 ≤ m) : Pq m ≠ 0 := by
  intro h
  apply ThetaLow_ne_zero m hm
  rw [Pq_spec m, h, mul_zero]

lemma Qhat_ne_zero (hm : 1 ≤ m) : Qhat m ≠ 0 := by
  intro h
  apply ThetaHat_ne_zero m hm
  rw [Qhat_spec m, h, mul_zero]

lemma Pq_natDegree (hm : 2 ≤ m) : (Pq m).natDegree = 2*m := by
  have hm1 : 1 ≤ m := by omega
  have h := (ThetaLow_deg m hm1).1
  rw [Pq_spec m, natDegree_mul (contL_ne_zero m hm1) (Pq_ne_zero m hm1),
    (contL_facts m hm1).1] at h
  omega

lemma Qhat_natDegree (hm : 1 ≤ m) : (Qhat m).natDegree = 4*m := by
  have h := (ThetaHat_deg m hm).1
  rw [Qhat_spec m, natDegree_mul (contH_ne_zero m hm) (Qhat_ne_zero m hm),
    (contH_facts m hm).1] at h
  omega

end Quotients

/-! ## Symmetries of the quotients -/

section QuotSym

open Polynomial

variable (m : ℕ)

/-- `P(2m, 1-X) = P(2m, X)`. -/
lemma Pq_comp_reflect (hm : 1 ≤ m) : (Pq m).comp (1-X) = Pq m := by
  have h := theta_symm m hm
  nth_rewrite 2 [Pq_spec m] at h
  rw [Pq_spec m, mul_comp, contL_comp_reflect] at h
  exact mul_left_cancel₀ (contL_ne_zero m hm) h

/-- `Θ↑ = contU · P(2m, -X)`. -/
lemma ThetaUp_eq (hm : 1 ≤ m) : ThetaUp m = contU m * (Pq m).comp (-X) := by
  rw [← theta_up_eq m hm, Pq_spec m, mul_comp, contL_comp_neg]

/-- `Q̂(-X) = Q̂(X)`. -/
lemma Qhat_comp_neg (hm : 1 ≤ m) : (Qhat m).comp (-X) = Qhat m := by
  have h := thetahat_even m hm
  nth_rewrite 2 [Qhat_spec m] at h
  rw [Qhat_spec m, mul_comp, contH_comp_neg] at h
  exact mul_left_cancel₀ (contH_ne_zero m hm) h

end QuotSym

/-! ## The even part: constructing `Q` with `Q(X²) = Q̂` -/

section EvenPart

open Polynomial

lemma coeff_comp_neg (f : ℚ[X]) (n : ℕ) :
    (f.comp (-X)).coeff n = (-1)^n * f.coeff n := by
  rw [show (-X : ℚ[X]) = C (-1) * X by rw [Polynomial.C_neg, Polynomial.C_1]; ring,
    Polynomial.comp_C_mul_X_coeff]
  ring

/-- Odd coefficients of an even polynomial vanish. -/
lemma even_coeff_odd (f : ℚ[X]) (hf : f.comp (-X) = f) (k : ℕ) :
    f.coeff (2*k+1) = 0 := by
  have h := coeff_comp_neg f (2*k+1)
  rw [hf] at h
  have hs : (-1:ℚ)^(2*k+1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [hs] at h
  linarith

/-- The even-part decomposition: if all odd coefficients of `f` vanish and
`f.natDegree < 2N`, then `g(X²) = f` for `g = ∑_{i<N} f_{2i} X^i`. -/
lemma even_decompose (f : ℚ[X]) (N : ℕ) (hdeg : f.natDegree < 2*N)
    (hodd : ∀ k, f.coeff (2*k+1) = 0) :
    (∑ i ∈ Finset.range N, C (f.coeff (2*i)) * X^i).comp (X^2) = f := by
  have hcomp : (∑ i ∈ Finset.range N, C (f.coeff (2*i)) * X^i).comp (X^2)
      = ∑ i ∈ Finset.range N, C (f.coeff (2*i)) * X^(2*i) := by
    rw [← compHom_apply, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [compHom_apply, mul_comp, C_comp, X_pow_comp, ← pow_mul]
  rw [hcomp]
  ext k
  rw [finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rcases Nat.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · subst ht
    by_cases hter : t < N
    · rw [Finset.sum_eq_single t]
      · rw [if_pos (two_mul t).symm, two_mul]
      · intro i _ hit
        exact if_neg (by omega)
      · intro h
        exact absurd (Finset.mem_range.mpr hter) h
    · rw [Finset.sum_eq_zero, eq_comm]
      · apply coeff_eq_zero_of_natDegree_lt
        omega
      · intro i hi
        rw [Finset.mem_range] at hi
        exact if_neg (by omega)
  · subst ht
    rw [Finset.sum_eq_zero, eq_comm]
    · exact hodd t
    · intro i hi
      exact if_neg (by omega)

/-- The conjecture's polynomial `Q(2m, ·)` over `ℚ`. -/
noncomputable def Qsmall (m : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (2*m+1), C ((Qhat m).coeff (2*i)) * X^i

lemma Qsmall_comp (m : ℕ) (hm : 1 ≤ m) : (Qsmall m).comp (X^2) = Qhat m := by
  apply even_decompose
  · rw [Qhat_natDegree m hm]
    omega
  · exact even_coeff_odd (Qhat m) (Qhat_comp_neg m hm)

lemma Qsmall_ne_zero (m : ℕ) (hm : 1 ≤ m) : Qsmall m ≠ 0 := by
  intro h
  apply Qhat_ne_zero m hm
  rw [← Qsmall_comp m hm, h, zero_comp]

lemma Qsmall_natDegree (m : ℕ) (hm : 1 ≤ m) : (Qsmall m).natDegree = 2*m := by
  have h := Qhat_natDegree m hm
  rw [← Qsmall_comp m hm, natDegree_comp, natDegree_pow, natDegree_X] at h
  omega

end EvenPart

end Bala

-- ===== Dev.Recurrence =====
/-!
# The three-term recurrence for `b(n) = a(m·n)`
-/

namespace Bala

open Polynomial Finset

section TIdent

variable (m : ℕ)

/-- The common cofactor `𝒞`. -/
noncomputable def CC (m : ℕ) : ℚ[X] :=
  PipM m * (Lm m (2*m+1) * (Lm m (2*m+2) * bigP1 m))

lemma Tp_eq (hm : 2 ≤ m) :
    PipM m * PipP m * (PsiW m).c = CC m * (Aplus m * Pq m) := by
  rw [PsiW_c m (by omega), Pq_spec m]
  simp only [CC]
  linear_combination (PipM m * Pq m) * idPlus m hm

lemma Tm_eq (hm : 2 ≤ m) :
    (PhiW m).c * (PsiW m).det
      = CC m * ((-1)^m * (Aminus m * (Pq m).comp (-X))) := by
  rw [PhiW_c m (by omega), ThetaUp_eq m (by omega), PsiW_det m (by omega)]
  simp only [CC]
  linear_combination (PipM m * (Pq m).comp (-X)) * idMinus m hm

lemma Tc_eq (hm : 2 ≤ m) :
    PipM m * ((PhiW m).mul (PsiW m)).c = CC m * Qhat m := by
  rw [PhiPsi_c m (by omega), Qhat_spec m]
  simp only [CC]
  linear_combination (PipM m * Qhat m) * idC m hm

end TIdent

/-! ## Evaluation bridges -/

section EvalBridge

lemma M2_det_emap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (A : M2 R) :
    (M2.emap f A).det = f A.det := by
  simp [M2.det, M2.emap]

lemma emap_eval_Wnd (b : ℚ[X]) (len : ℕ) (t : ℚ) :
    M2.emap (evalRingHom t) (Wnd b len) = Wnd (b.eval t) len := by
  rw [Wnd_emap]
  rfl

lemma eval_Wnd_c (b : ℚ[X]) (len : ℕ) (t : ℚ) :
    (Wnd b len).c.eval t = (Wnd (b.eval t) len).c := by
  rw [← emap_eval_Wnd]
  rfl

lemma eval_Wnd_det (b : ℚ[X]) (len : ℕ) (t : ℚ) :
    (Wnd b len).det.eval t = (Wnd (b.eval t) len).det := by
  rw [← emap_eval_Wnd b len t, M2_det_emap]
  rfl

lemma eval_Wnd_mul_c (b b' : ℚ[X]) (len len' : ℕ) (t : ℚ) :
    ((Wnd b len).mul (Wnd b' len')).c.eval t
      = ((Wnd (b.eval t) len).mul (Wnd (b'.eval t) len')).c := by
  rw [← emap_eval_Wnd b len t, ← emap_eval_Wnd b' len' t, ← M2.emap_mul]
  rfl

variable (m n : ℕ)

lemma PsiW_c_eval :
    (PsiW m).c.eval (n:ℚ) = (Wnd (((m*n:ℕ):ℚ)-(m:ℚ)+1) m).c := by
  unfold PsiW
  rw [eval_Wnd_c]
  congr 1
  rw [pa_eval]
  push_cast
  ring

lemma PhiW_c_eval :
    (PhiW m).c.eval (n:ℚ) = (Wnd (((m*n:ℕ):ℚ)+1) m).c := by
  unfold PhiW
  rw [eval_Wnd_c]
  congr 1
  rw [pa_eval]
  push_cast
  ring

lemma PsiW_det_eval :
    (PsiW m).det.eval (n:ℚ) = (Wnd (((m*n:ℕ):ℚ)-(m:ℚ)+1) m).det := by
  unfold PsiW
  rw [eval_Wnd_det]
  congr 1
  rw [pa_eval]
  push_cast
  ring

lemma PhiPsi_c_eval :
    ((PhiW m).mul (PsiW m)).c.eval (n:ℚ)
      = ((Wnd (((m*n:ℕ):ℚ)+1) m).mul (Wnd (((m*n:ℕ):ℚ)-(m:ℚ)+1) m)).c := by
  unfold PhiW PsiW
  rw [eval_Wnd_mul_c]
  congr 2 <;> (rw [pa_eval]; push_cast; ring)

/-- Bridge an `Ioc`-product of `cP (pa m ·)` evaluations to `range`-form. -/
lemma prod_cP_eval_bridge (a : ℤ) :
    (∏ j ∈ Finset.Ioc a (a+(m:ℤ)), cP (pa m j)).eval (n:ℚ)
      = ∏ i ∈ Finset.range m, cP (((m*n:ℕ):ℚ) + (a:ℚ) + 1 + (i:ℚ)) := by
  rw [eval_prod]
  rw [Finset.prod_congr rfl (fun j (_ : j ∈ Finset.Ioc a (a+(m:ℤ))) => by
    rw [eval_cP, pa_eval]
    exact congrArg cP (by push_cast; ring) :
      ∀ j ∈ Finset.Ioc a (a+(m:ℤ)),
        (cP (pa m j)).eval (n:ℚ) = (fun j : ℤ => cP (((m*n:ℕ):ℚ) + (j:ℚ))) j)]
  rw [show Finset.Ioc a (a+(m:ℤ)) = Finset.Ioc ((a+1)-1) ((a+1)-1+(m:ℤ)) by
    congr 1 <;> ring]
  rw [← prod_range_to_Ioc (fun j : ℤ => cP (((m*n:ℕ):ℚ) + (j:ℚ))) (a+1) m]
  exact Finset.prod_congr rfl (fun i _ => congrArg cP (by push_cast; ring))

lemma PipP_eval :
    (PipP m).eval (n:ℚ) = ∏ i ∈ Finset.range m, cP (((m*n:ℕ):ℚ)+1+(i:ℚ)) := by
  unfold PipP
  rw [show Finset.Ioc (0:ℤ) (m:ℤ) = Finset.Ioc (0:ℤ) (0+(m:ℤ)) by congr 1; ring,
    prod_cP_eval_bridge m n 0]
  exact Finset.prod_congr rfl (fun i _ => congrArg cP (by push_cast; ring))

lemma PipM_eval :
    (PipM m).eval (n:ℚ)
      = ∏ i ∈ Finset.range m, cP (((m*n:ℕ):ℚ)-(m:ℚ)+1+(i:ℚ)) := by
  unfold PipM
  rw [show Finset.Ioc (-(m:ℤ)) (0:ℤ) = Finset.Ioc (-(m:ℤ)) (-(m:ℤ)+(m:ℤ)) by
    congr 1; ring,
    prod_cP_eval_bridge m n (-(m:ℤ))]
  exact Finset.prod_congr rfl (fun i _ => congrArg cP (by push_cast; ring))

end EvalBridge

/-! ## Positivity of the cofactor -/

section Positivity

lemma cP_pos (x : ℚ) (hx : 1 ≤ x) : 0 < cP x := by
  simp only [cP]
  have h1 : (0:ℚ) < 2*x+1 := by linarith
  have h2 : (0:ℚ) < 2*x+2 := by linarith
  have h3 : (0:ℚ) < 5*x^2-5*x+1 := by
    linarith [mul_nonneg (by linarith : (0:ℚ) ≤ 5*x) (by linarith : (0:ℚ) ≤ x-1)]
  positivity

lemma p1_pos (x : ℚ) (hx : 1 ≤ x) : 0 < p1 x := by
  simp only [p1]
  linarith [mul_nonneg (by linarith : (0:ℚ) ≤ 5*x) (by linarith : (0:ℚ) ≤ x-1)]

lemma CC_eval_pos (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : 0 < (CC m).eval (n:ℚ) := by
  have hm' : (1:ℚ) ≤ m := by exact_mod_cast hm
  have hn' : (1:ℚ) ≤ n := by exact_mod_cast hn
  simp only [CC, eval_mul]
  have h1 : 0 < (PipM m).eval (n:ℚ) := by
    unfold PipM
    rw [eval_prod]
    apply Finset.prod_pos
    intro j hj
    simp only [Finset.mem_Ioc] at hj
    rw [eval_cP, pa_eval]
    apply cP_pos
    have hj' : (1:ℚ) - m ≤ (j:ℚ) := by
      have : (1:ℤ) - m ≤ j := by omega
      exact_mod_cast this
    linarith [mul_nonneg (by linarith : (0:ℚ) ≤ (m:ℚ)) (by linarith : (0:ℚ) ≤ (n:ℚ)-1)]
  have h2 : 0 < (Lm m (2*m+1)).eval (n:ℚ) := by
    rw [Lm_eval]
    push_cast
    linarith [mul_nonneg (by linarith : (0:ℚ) ≤ 2*(m:ℚ)) (by linarith : (0:ℚ) ≤ (n:ℚ))]
  have h3 : 0 < (Lm m (2*m+2)).eval (n:ℚ) := by
    rw [Lm_eval]
    push_cast
    linarith [mul_nonneg (by linarith : (0:ℚ) ≤ 2*(m:ℚ)) (by linarith : (0:ℚ) ≤ (n:ℚ))]
  have h4 : 0 < (bigP1 m).eval (n:ℚ) := by
    unfold bigP1
    rw [eval_prod]
    apply Finset.prod_pos
    intro j hj
    simp only [Finset.mem_Ioc] at hj
    rw [eval_p1, pa_eval]
    apply p1_pos
    have hj' : (2:ℚ) - m ≤ (j:ℚ) := by
      have : (2:ℤ) - m ≤ j := by omega
      exact_mod_cast this
    linarith [mul_nonneg (by linarith : (0:ℚ) ≤ (m:ℚ)) (by linarith : (0:ℚ) ≤ (n:ℚ)-1)]
  exact mul_pos h1 (mul_pos h2 (mul_pos h3 h4))

end Positivity

/-! ## The scalar recurrence over `ℚ` -/

theorem scalar_rec (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (Aplus m).eval (n:ℚ) * (Pq m).eval (n:ℚ) * aq (m*n+m)
      + (-1:ℚ)^m * ((Aminus m).eval (n:ℚ) * (Pq m).eval (-(n:ℚ))) * aq (m*n-m)
      = (Qhat m).eval (n:ℚ) * aq (m*n) := by
  have hmμ : m ≤ m*n := Nat.le_mul_of_pos_right m hn
  have hC := contraction aq base_rec (m*n) m (by omega) hmμ
  have hTp := congrArg (Polynomial.eval (n:ℚ)) (Tp_eq m hm)
  have hTm := congrArg (Polynomial.eval (n:ℚ)) (Tm_eq m hm)
  have hTc := congrArg (Polynomial.eval (n:ℚ)) (Tc_eq m hm)
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_comp, eval_neg, eval_X] at hTp hTm hTc
  rw [PipM_eval, PipP_eval, PsiW_c_eval] at hTp
  rw [PhiW_c_eval, PsiW_det_eval] at hTm
  rw [PipM_eval, PhiPsi_c_eval] at hTc
  have hCC := CC_eval_pos m n (by omega) hn
  refine mul_left_cancel₀ (ne_of_gt hCC) ?_
  linear_combination hC - aq (m*n+m) * hTp - aq (m*n-m) * hTm + aq (m*n) * hTc

end Bala

-- ===== Dev.RealRec =====
/-!
# The recurrence over `ℝ`, in the exact shape of the conjecture
-/

namespace Bala

open Polynomial Finset

section IocBridge

lemma prod_Ioc_int_to_nat {M : Type*} [CommMonoid M] (f : ℤ → M) (K : ℕ) :
    ∏ j ∈ Finset.Ioc (0:ℤ) (K:ℤ), f j = ∏ k ∈ Finset.Ioc 0 K, f (k:ℤ) := by
  refine Finset.prod_nbij' (fun j => j.toNat) (fun k => (k:ℤ)) ?_ ?_ ?_ ?_ ?_ <;>
    · intro x hx
      simp only [Finset.mem_Ioc] at hx ⊢
      first
      | omega
      | (congr 1; omega)

end IocBridge

section RealDefs

/-- The conjecture's `P(2m, ·)` over `ℝ` (valid for `m ≥ 2`). -/
noncomputable def PR (m : ℕ) : ℝ[X] := (Pq m).map (algebraMap ℚ ℝ)

/-- The conjecture's `Q(2m, ·)` over `ℝ`. -/
noncomputable def QR (m : ℕ) : ℝ[X] := (Qsmall m).map (algebraMap ℚ ℝ)

lemma algebraMap_rat_real (t : ℚ) : algebraMap ℚ ℝ t = (t:ℝ) := by
  simp

lemma map_eval_rat (p : ℚ[X]) (t : ℚ) :
    (p.map (algebraMap ℚ ℝ)).eval ((t:ℝ)) = ((p.eval t : ℚ) : ℝ) := by
  rw [show ((t:ℝ)) = algebraMap ℚ ℝ t from (algebraMap_rat_real t).symm,
    eval_map, eval₂_at_apply, algebraMap_rat_real]

end RealDefs

section EvalProducts

variable (m n : ℕ)

lemma Aplus_eval_real :
    (((Aplus m).eval (n:ℚ) : ℚ) : ℝ)
      = ∏ k ∈ Finset.Ioc 0 (2*m), ((2*(m:ℝ)*(n:ℝ)) + (k:ℝ)) := by
  unfold Aplus
  rw [eval_prod, Rat.cast_prod]
  have h := prod_Ioc_int_to_nat (fun j => (((Lm m j).eval (n:ℚ) : ℚ):ℝ)) (2*m)
  rw [show (((2*m:ℕ)):ℤ) = 2*(m:ℤ) by push_cast; ring] at h
  rw [h]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  dsimp only
  rw [Lm_eval]
  push_cast
  ring

lemma Aminus_eval_real :
    (((Aminus m).eval (n:ℚ) : ℚ) : ℝ)
      = ∏ k ∈ Finset.Ioc 0 (2*m), ((2*(m:ℝ)*(n:ℝ)) - (k:ℝ)) := by
  unfold Aminus
  rw [eval_prod, Rat.cast_prod]
  have h := prod_Ioc_int_to_nat (fun j => (((Lm m (-j)).eval (n:ℚ) : ℚ):ℝ)) (2*m)
  rw [show (((2*m:ℕ)):ℤ) = 2*(m:ℤ) by push_cast; ring] at h
  rw [h]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  dsimp only
  rw [Lm_eval]
  push_cast
  ring

end EvalProducts

/-! ## The real recurrence (m ≥ 2) -/

theorem real_rec (m n : ℕ) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    ((∏ k ∈ Finset.Ioc 0 (2*m), ((2*(m:ℝ)*(n:ℝ)) + (k:ℝ))) * (PR m).eval ((n:ℝ)))
        * (A103885 (m*(n+1)) : ℝ)
      + ((-1:ℝ)^m * (∏ k ∈ Finset.Ioc 0 (2*m), ((2*(m:ℝ)*(n:ℝ)) - (k:ℝ)))
          * (PR m).eval (-(n:ℝ))) * (A103885 (m*(n-1)) : ℝ)
      = (QR m).eval ((n:ℝ)^2) * (A103885 (m*n) : ℝ) := by
  have hs := scalar_rec m n hm hn
  have hcast := congrArg (fun x : ℚ => (x : ℝ)) hs
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg, Rat.cast_one] at hcast
  rw [Aplus_eval_real, Aminus_eval_real] at hcast
  -- rewrite the polynomial evaluations
  have hP1 : (((Pq m).eval (n:ℚ) : ℚ) : ℝ) = (PR m).eval ((n:ℝ)) := by
    rw [show ((n:ℝ)) = (((n:ℚ)):ℝ) from by norm_cast, PR, map_eval_rat]
  have hP2 : (((Pq m).eval (-(n:ℚ)) : ℚ) : ℝ) = (PR m).eval (-(n:ℝ)) := by
    rw [show (-(n:ℝ)) = (((-(n:ℚ)):ℚ):ℝ) from by push_cast; ring, PR, map_eval_rat]
  have hQ : (((Qhat m).eval (n:ℚ) : ℚ) : ℝ) = (QR m).eval ((n:ℝ)^2) := by
    rw [← Qsmall_comp m (by omega), eval_comp, eval_pow, eval_X,
      show ((n:ℝ)^2) = ((((n:ℚ)^2):ℚ):ℝ) from by push_cast; ring, QR, map_eval_rat]
  rw [hP1, hP2, hQ] at hcast
  -- rewrite the sequence values
  have haq : ∀ k : ℕ, ((aq k : ℚ) : ℝ) = (A103885 k : ℝ) := by
    intro k
    simp [aq]
  rw [haq, haq, haq] at hcast
  have e1 : m*(n+1) = m*n+m := by ring
  have e2 : m*(n-1) = m*n-m := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
    simp [Nat.mul_succ]
  rw [e1, e2]
  linear_combination hcast

end Bala

-- ===== Dev.Roots =====
/-!
# From sign alternation to real-rootedness

If a real polynomial of degree `d` alternates in sign at `d+1` increasing
points, it splits over `ℝ` with all roots strictly between the first and last
point; hence all complex roots of its image in `ℂ[X]` are real.
-/

namespace Bala

open Polynomial Finset

section Alternation

lemma xchain {d : ℕ} (x : ℕ → ℝ) (hmono : ∀ i, i+1 ≤ d → x i < x (i+1)) :
    ∀ i j, i ≤ j → j ≤ d → x i ≤ x j := by
  intro i j hij hjd
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge i (k+1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hmono k (by omega)))
    · have : i = k+1 := by omega
      subst this
      rfl

/-- Sign alternation at `d+1` points forces splitting with all roots in
`(x 0, x d)`. -/
lemma alternation_roots (f : ℝ[X]) (d : ℕ) (hd : f.natDegree = d) (hd0 : 0 < d)
    (x : ℕ → ℝ) (hmono : ∀ i, i+1 ≤ d → x i < x (i+1))
    (hsign : ∀ i, i ≤ d → 0 < (-1:ℝ)^i * f.eval (x i)) :
    f.Splits ∧ ∀ r ∈ f.roots, x 0 < r ∧ r < x d := by
  have hf0 : f ≠ 0 := by
    intro h
    have h0 := hsign 0 (by omega)
    rw [h] at h0
    simp at h0
  -- a root in each interval
  have hex : ∀ i, ∃ r, i+1 ≤ d → (r ∈ Set.Ioo (x i) (x (i+1)) ∧ f.eval r = 0) := by
    intro i
    by_cases hi : i+1 ≤ d
    · have hcont : ContinuousOn (fun t => f.eval t) (Set.Icc (x i) (x (i+1))) :=
        f.continuous.continuousOn
    -- sign split
      rcases Nat.even_or_odd i with he | ho
      · have h1 : 0 < f.eval (x i) := by
          have := hsign i (by omega)
          rwa [he.neg_one_pow, one_mul] at this
        have h2 : f.eval (x (i+1)) < 0 := by
          have := hsign (i+1) hi
          rw [pow_succ, he.neg_one_pow] at this
          linarith
        have h0 : (0:ℝ) ∈ Set.Ioo (f.eval (x (i+1))) (f.eval (x i)) := ⟨h2, h1⟩
        have := intermediate_value_Ioo' (le_of_lt (hmono i hi)) hcont h0
        obtain ⟨r, hr, hr0⟩ := this
        exact ⟨r, fun _ => ⟨hr, hr0⟩⟩
      · have h1 : f.eval (x i) < 0 := by
          have := hsign i (by omega)
          rw [ho.neg_one_pow] at this
          linarith
        have h2 : 0 < f.eval (x (i+1)) := by
          have := hsign (i+1) hi
          rw [pow_succ, ho.neg_one_pow] at this
          linarith
        have h0 : (0:ℝ) ∈ Set.Ioo (f.eval (x i)) (f.eval (x (i+1))) := ⟨h1, h2⟩
        have := intermediate_value_Ioo (le_of_lt (hmono i hi)) hcont h0
        obtain ⟨r, hr, hr0⟩ := this
        exact ⟨r, fun _ => ⟨hr, hr0⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose r hr using hex
  -- the image finset
  have hrmono : ∀ i j, i < j → j < d → r i < r j := by
    intro i j hij hjd
    have hi := hr i (by omega)
    have hj := hr j (by omega)
    calc r i < x (i+1) := hi.1.2
      _ ≤ x j := xchain x hmono (i+1) j (by omega) (by omega)
      _ < r j := hj.1.1
  have hinj : Set.InjOn r (Finset.range d) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · exact absurd hab (ne_of_lt (hrmono a b h hb))
    · have : b < a := by omega
      exact absurd hab.symm (ne_of_lt (hrmono b a this ha))
  set S : Finset ℝ := (Finset.range d).image r with hS
  have hScard : S.card = d := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hSsub : S ⊆ f.roots.toFinset := by
    intro ρ hρ
    rw [hS, Finset.mem_image] at hρ
    obtain ⟨i, hi, rfl⟩ := hρ
    rw [Finset.mem_range] at hi
    rw [Multiset.mem_toFinset, mem_roots hf0]
    exact (hr i (by omega)).2
  have hcard1 : d ≤ f.roots.toFinset.card := hScard ▸ Finset.card_le_card hSsub
  have hcard2 : f.roots.toFinset.card ≤ f.roots.card := f.roots.toFinset_card_le
  have hcard3 : f.roots.card ≤ d := hd ▸ f.card_roots'
  have hsplits : f.Splits := splits_iff_card_roots.mpr (by omega)
  have hSeq : f.roots.toFinset = S :=
    (Finset.eq_of_subset_of_card_le hSsub (by omega)).symm
  refine ⟨hsplits, fun ρ hρ => ?_⟩
  have : ρ ∈ S := hSeq ▸ Multiset.mem_toFinset.mpr hρ
  rw [hS, Finset.mem_image] at this
  obtain ⟨i, hi, rfl⟩ := this
  rw [Finset.mem_range] at hi
  have hri := hr i (by omega)
  constructor
  · calc x 0 ≤ x i := xchain x hmono 0 i (by omega) (by omega)
      _ < r i := hri.1.1
  · calc r i < x (i+1) := hri.1.2
      _ ≤ x d := xchain x hmono (i+1) d (by omega) (by omega)

/-- All complex roots of a sign-alternating real polynomial are real, in
`(x 0, x d)`. -/
lemma complex_roots_of_alternation (f : ℝ[X]) (d : ℕ) (hd : f.natDegree = d)
    (hd0 : 0 < d) (x : ℕ → ℝ) (hmono : ∀ i, i+1 ≤ d → x i < x (i+1))
    (hsign : ∀ i, i ≤ d → 0 < (-1:ℝ)^i * f.eval (x i)) :
    ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ x 0 < z.re ∧ z.re < x d := by
  obtain ⟨hsplit, hroots⟩ := alternation_roots f d hd hd0 x hmono hsign
  intro z hz
  have hf0 : f ≠ 0 := by
    intro h
    have h0 := hsign 0 (by omega)
    rw [h] at h0
    simp at h0
  have hzmem : z ∈ (f.map (algebraMap ℝ ℂ)).roots :=
    (mem_roots (map_ne_zero hf0)).mpr hz
  rw [hsplit.map_roots] at hzmem
  obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hzmem
  obtain ⟨h1, h2⟩ := hroots ρ hρ
  refine ⟨by simp, ?_, ?_⟩
  · simpa using h1
  · simpa using h2

end Alternation

end Bala

-- ===== Dev.Cones =====
/-!
# Cone certificates for the transfer-matrix journeys

`DownState` is an invariant cone for steps with argument `ν ≤ -3`;
`UpCone` for steps with argument `ν ≥ 11/10`.  All inequalities are certified
by edge decompositions whose edge values are polynomials with nonnegative
coefficients in the shifted variable `s ≥ 0`.
-/

namespace Bala

/-- The downward-phase cone: `v₁/v₂ ∈ [10.9, 14]`, `v₂ > 0`. -/
def DownState (v : ℚ × ℚ) : Prop :=
  0 < v.2 ∧ 109*v.2 ≤ 10*v.1 ∧ 10*v.1 ≤ 140*v.2

/-- The upward-phase cone: `v₁/v₂ ∈ [7.5, 11.6]`, `v₂ > 0`. -/
def UpCone (v : ℚ × ℚ) : Prop :=
  0 < v.2 ∧ 75*v.2 ≤ 10*v.1 ∧ 10*v.1 ≤ 116*v.2

lemma cP_down_pos (ν : ℚ) (hν : ν ≤ -3) : 0 < cP ν := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ ν = -3-s := ⟨-3-ν, by linarith only [hν], by ring⟩
  have h : cP (-3-s) = 1220 + 1798*s + 974*s^2 + 230*s^3 + 20*s^4 := by
    simp only [cP]
    ring
  rw [h]
  positivity

lemma cP_up_pos (ν : ℚ) (hν : 11/10 ≤ ν) : 0 < cP ν := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ ν = 11/10+s := ⟨ν-11/10, sub_nonneg.mpr hν, by ring⟩
  have h : cP (11/10+s)
      = (2604/125:ℚ) + (5179/50:ℚ)*s + (811/5:ℚ)*s^2 + 98*s^3 + 20*s^4 := by
    simp only [cP]
    ring
  rw [h]
  positivity

/-- Entering the down cone from `(1,0)`. -/
lemma down_start (ν : ℚ) (hν : ν ≤ -3) : DownState ((Mstep ν).act (1, 0)) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ ν = -3-s := ⟨-3-ν, by linarith only [hν], by ring⟩
  have hw : (Mstep (-3-s)).act (1, 0) = (-(c0 (-3-s)), cP (-3-s)) := by
    simp [Mstep, M2.act]
  rw [hw, DownState]
  refine ⟨cP_down_pos _ (by linarith only [hs]), ?_, ?_⟩
  · have h : 10*(-(c0 (-3-s))) - 109*(cP (-3-s))
        = 33100 + 33458*s + 11274*s^2 + 1330*s^3 + 20*s^4 := by
      simp only [c0, cP]
      ring
    linarith only [hs, sq_nonneg s, pow_nonneg hs 3, pow_nonneg hs 4, h]
  · have h : 140*(cP (-3-s)) - 10*(-(c0 (-3-s)))
        = 4720 + 22280*s + 18920*s^2 + 5800*s^3 + 600*s^4 := by
      simp only [c0, cP]
      ring
    linarith only [hs, sq_nonneg s, pow_nonneg hs 3, pow_nonneg hs 4, h]

/-- The down cone is invariant under steps with argument `≤ -3`. -/
lemma down_step (ν : ℚ) (hν : ν ≤ -3) (v : ℚ × ℚ) (hv : DownState v) :
    DownState ((Mstep ν).act v) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ ν = -3-s := ⟨-3-ν, by linarith only [hν], by ring⟩
  obtain ⟨h1, h2, h3⟩ := hv
  obtain ⟨v₁, v₂⟩ := v
  simp only at h1 h2 h3
  have ha : (0:ℚ) ≤ 14*v₂ - v₁ := by linarith only [h2, h3]
  have hb : (0:ℚ) ≤ 10*v₁ - 109*v₂ := by linarith only [h2]
  have hv₁ : 0 < v₁ := by linarith only [h1, h2]
  have hs2 : (0:ℚ) ≤ s^2 := sq_nonneg s
  have hs3 : (0:ℚ) ≤ s^3 := pow_nonneg hs 3
  have hs4 : (0:ℚ) ≤ s^4 := pow_nonneg hs 4
  have hw : (Mstep (-3-s)).act (v₁, v₂)
      = (-(c0 (-3-s))*v₁ - cM (-3-s)*v₂, cP (-3-s)*v₁) := by
    simp only [M2.act, Mstep_a, Mstep_b, Mstep_c, Mstep_d, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  rw [hw, DownState]
  refine ⟨mul_pos (cP_down_pos (-3-s) (by linarith only [hs])) hv₁, ?_, ?_⟩
  · have key : 31*(10*(-(c0 (-3-s))*v₁ - cM (-3-s)*v₂) - 109*(cP (-3-s)*v₁))
        = (14*v₂-v₁) * (3781500 + 3879922*s + 1344266*s^2 + 169970*s^3 + 4180*s^4)
          + (10*v₁-109*v₂) * (480760 + 491712*s + 169376*s^2 + 21120*s^3 + 480*s^4) := by
      simp only [c0, cM, cP]
      ring
    have k1 : (0:ℚ) ≤ (14*v₂-v₁) * (3781500 + 3879922*s + 1344266*s^2 + 169970*s^3 + 4180*s^4) :=
      mul_nonneg ha (by linarith only [hs, hs2, hs3, hs4])
    have k2 : (0:ℚ) ≤ (10*v₁-109*v₂) * (480760 + 491712*s + 169376*s^2 + 21120*s^3 + 480*s^4) :=
      mul_nonneg hb (by linarith only [hs, hs2, hs3, hs4])
    linarith only [key, k1, k2]
  · have key : 31*(140*(cP (-3-s)*v₁) - 10*(-(c0 (-3-s))*v₁ - cM (-3-s)*v₂))
        = (14*v₂-v₁) * (340880 + 2195520*s + 1946880*s^2 + 607200*s^3 + 63400*s^4)
          + (10*v₁-109*v₂) * (48720 + 288620*s + 253340*s^2 + 78700*s^3 + 8200*s^4) := by
      simp only [c0, cM, cP]
      ring
    have k1 : (0:ℚ) ≤ (14*v₂-v₁) * (340880 + 2195520*s + 1946880*s^2 + 607200*s^3 + 63400*s^4) :=
      mul_nonneg ha (by linarith only [hs, hs2, hs3, hs4])
    have k2 : (0:ℚ) ≤ (10*v₁-109*v₂) * (48720 + 288620*s + 253340*s^2 + 78700*s^3 + 8200*s^4) :=
      mul_nonneg hb (by linarith only [hs, hs2, hs3, hs4])
    linarith only [key, k1, k2]

/-- The up cone is invariant under steps with argument `≥ 11/10`. -/
lemma up_step (ν : ℚ) (hν : 11/10 ≤ ν) (v : ℚ × ℚ) (hv : UpCone v) :
    UpCone ((Mstep ν).act v) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ ν = 11/10+s := ⟨ν-11/10, sub_nonneg.mpr hν, by ring⟩
  obtain ⟨h1, h2, h3⟩ := hv
  obtain ⟨v₁, v₂⟩ := v
  simp only at h1 h2 h3
  have ha : (0:ℚ) ≤ 58*v₂ - 5*v₁ := by linarith only [h3]
  have hb : (0:ℚ) ≤ 2*v₁ - 15*v₂ := by linarith only [h2]
  have hv₁ : 0 < v₁ := by linarith only [h1, h2]
  have hs2 : (0:ℚ) ≤ s^2 := sq_nonneg s
  have hs3 : (0:ℚ) ≤ s^3 := pow_nonneg hs 3
  have hs4 : (0:ℚ) ≤ s^4 := pow_nonneg hs 4
  have hw : (Mstep (11/10+s)).act (v₁, v₂)
      = (-(c0 (11/10+s))*v₁ - cM (11/10+s)*v₂, cP (11/10+s)*v₁) := by
    simp only [M2.act, Mstep_a, Mstep_b, Mstep_c, Mstep_d, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  rw [hw, UpCone]
  refine ⟨mul_pos (cP_up_pos (11/10+s) (by linarith only [hs])) hv₁, ?_, ?_⟩
  · have key : 2050*(10*(-(c0 (11/10+s))*v₁ - cM (11/10+s)*v₂) - 75*(cP (11/10+s)*v₁))
        = (58*v₂-5*v₁) * (102777 + 753205*s + 1931450*s^2 + 1825500*s^3 + 545000*s^4)
          + (2*v₁-15*v₂) * (393288 + 2859120*s + 7336800*s^2 + 6952000*s^3 + 2080000*s^4) := by
      simp only [c0, cM, cP]
      ring
    have k1 : (0:ℚ) ≤ (58*v₂-5*v₁) * (102777 + 753205*s + 1931450*s^2 + 1825500*s^3 + 545000*s^4) :=
      mul_nonneg ha (by linarith only [hs, hs2, hs3, hs4])
    have k2 : (0:ℚ) ≤ (2*v₁-15*v₂) * (393288 + 2859120*s + 7336800*s^2 + 6952000*s^3 + 2080000*s^4) :=
      mul_nonneg hb (by linarith only [hs, hs2, hs3, hs4])
    linarith only [key, k1, k2]
  · have key : 20500*(116*(cP (11/10+s)*v₁) - 10*(-(c0 (11/10+s))*v₁ - cM (11/10+s)*v₂))
        = (58*v₂-5*v₁) * (5378070 + 24318800*s + 30562000*s^2 + 11880000*s^3 + 700000*s^4)
          + (2*v₁-15*v₂) * (20836368 + 94565420*s + 119487800*s^2 + 47002000*s^3 + 2980000*s^4) := by
      simp only [c0, cM, cP]
      ring
    have k1 : (0:ℚ) ≤ (58*v₂-5*v₁) * (5378070 + 24318800*s + 30562000*s^2 + 11880000*s^3 + 700000*s^4) :=
      mul_nonneg ha (by linarith only [hs, hs2, hs3, hs4])
    have k2 : (0:ℚ) ≤ (2*v₁-15*v₂) * (20836368 + 94565420*s + 119487800*s^2 + 47002000*s^3 + 2980000*s^4) :=
      mul_nonneg hb (by linarith only [hs, hs2, hs3, hs4])
    linarith only [key, k1, k2]

/-! ## Runs -/

/-- A full down-phase run: all arguments `b, b+1, …, b+k-1 ≤ -3`, start `(1,0)`. -/
lemma down_run (b : ℚ) (k : ℕ) (hk : 1 ≤ k) (harg : b + k - 1 ≤ -3) :
    DownState ((Wnd b k).act (1, 0)) := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · have : n = 0 := by omega
      subst this
      rw [Wnd_one]
      apply down_start
      push_cast at harg
      linarith
    · have hn : 1 ≤ n := by omega
      have harg' : b + n - 1 ≤ -3 := by
        push_cast at harg ⊢
        linarith
      rw [Wnd_succ, M2.act_mul]
      apply down_step
      · push_cast at harg
        linarith
      · exact ih hn harg'

/-- A full up-phase run: all arguments `≥ 11/10`. -/
lemma up_run (b : ℚ) (hb : 11/10 ≤ b) (k : ℕ) (v : ℚ × ℚ) (hv : UpCone v) :
    UpCone ((Wnd b k).act v) := by
  induction k with
  | zero => simpa using hv
  | succ n ih =>
    rw [Wnd_succ, M2.act_mul]
    apply up_step
    · have : (0:ℚ) ≤ n := by positivity
      linarith
    · exact ih

/-- The up cone forces a positive first component. -/
lemma UpCone_pos_fst (v : ℚ × ℚ) (hv : UpCone v) : 0 < v.1 := by
  obtain ⟨h1, h2, h3⟩ := hv
  linarith

/-! ## Rational cones spanned by two vectors -/

/-- Membership in the closed convex cone spanned by `U` and `W` (nonzero
combinations only). -/
def ConeAt (U W v : ℚ × ℚ) : Prop :=
  ∃ α β : ℚ, 0 ≤ α ∧ 0 ≤ β ∧ 0 < α + β ∧
    v = (α*U.1 + β*W.1, α*U.2 + β*W.2)

/-- Transport of a two-vector cone through one matrix step, given edge
certificates. -/
lemma cone_step {ν : ℚ} {U W U' W' : ℚ × ℚ} {cu0 cu1 cw0 cw1 : ℚ}
    (hcu0 : 0 ≤ cu0) (hcu1 : 0 ≤ cu1) (hcw0 : 0 ≤ cw0) (hcw1 : 0 ≤ cw1)
    (hsU : 0 < cu0 + cu1) (hsW : 0 < cw0 + cw1)
    (hU : (Mstep ν).act U = (cu0*U'.1 + cu1*W'.1, cu0*U'.2 + cu1*W'.2))
    (hW : (Mstep ν).act W = (cw0*U'.1 + cw1*W'.1, cw0*U'.2 + cw1*W'.2))
    {v : ℚ × ℚ} (hv : ConeAt U W v) : ConeAt U' W' ((Mstep ν).act v) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hv
  refine ⟨α*cu0 + β*cw0, α*cu1 + β*cw1, by positivity, by positivity, ?_, ?_⟩
  · rcases le_or_gt α 0 with h | h
    · have hα0 : α = 0 := le_antisymm h hα
      subst hα0
      have hβ' : 0 < β := by linarith
      linarith [mul_pos hβ' hsW]
    · linarith [mul_pos h hsU, mul_nonneg hβ hcw0, mul_nonneg hβ hcw1]
  · have h1 := congrArg Prod.fst hU
    have h2 := congrArg Prod.snd hU
    have h3 := congrArg Prod.fst hW
    have h4 := congrArg Prod.snd hW
    simp only [M2.act, Mstep_a, Mstep_b, Mstep_c, Mstep_d, Prod.mk.injEq] at h1 h2 h3 h4 ⊢
    constructor
    · linear_combination α * h1 + β * h3
    · linear_combination α * h2 + β * h4

/-- Entry into the two-vector cone from the down cone. -/
lemma down_to_cone (v : ℚ × ℚ) (hv : DownState v) :
    ConeAt (109, 10) (14, 1) v := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨(14*v.2 - v.1)/31, (10*v.1 - 109*v.2)/31, by linarith only [h2, h3],
    by linarith only [h2], ?_, ?_⟩
  · rw [div_add_div_same, lt_div_iff₀ (by norm_num : (0:ℚ) < 31)]
    linarith only [h1, h2]
  · obtain ⟨v₁, v₂⟩ := v
    simp only [Prod.mk.injEq]
    constructor <;> ring

/-- Exit from a two-vector cone into a signed up cone, given numeric facts
about the two spanning vectors. -/
lemma cone_to_up {U W : ℚ × ℚ} (σ : ℚ)
    (hU2 : 0 < σ*U.2) (hW2 : 0 < σ*W.2)
    (hUa : 75*(σ*U.2) ≤ 10*(σ*U.1)) (hUb : 10*(σ*U.1) ≤ 116*(σ*U.2))
    (hWa : 75*(σ*W.2) ≤ 10*(σ*W.1)) (hWb : 10*(σ*W.1) ≤ 116*(σ*W.2))
    {v : ℚ × ℚ} (hv : ConeAt U W v) : UpCone (σ*v.1, σ*v.2) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hv
  simp only
  refine ⟨?_, ?_, ?_⟩
  · rcases le_or_gt α 0 with h | h
    · have hα0 : α = 0 := le_antisymm h hα
      subst hα0
      have hβ' : 0 < β := by linarith
      linarith [mul_pos hβ' hW2]
    · linarith [mul_pos h hU2, mul_nonneg hβ (le_of_lt hW2)]
  · linarith [mul_nonneg hα (by linarith : (0:ℚ) ≤ 10*(σ*U.1) - 75*(σ*U.2)),
      mul_nonneg hβ (by linarith : (0:ℚ) ≤ 10*(σ*W.1) - 75*(σ*W.2))]
  · linarith [mul_nonneg hα (by linarith : (0:ℚ) ≤ 116*(σ*U.2) - 10*(σ*U.1)),
      mul_nonneg hβ (by linarith : (0:ℚ) ≤ 116*(σ*W.2) - 10*(σ*W.1))]

/-- Exit from a two-vector cone with a definite sign of the first component
(end-early case). -/
lemma cone_fst_sign {U W : ℚ × ℚ} (σ : ℚ)
    (hU1 : 0 < σ*U.1) (hW1 : 0 < σ*W.1)
    {v : ℚ × ℚ} (hv : ConeAt U W v) : 0 < σ*v.1 := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hv
  simp only
  rcases le_or_gt α 0 with h | h
  · have hα0 : α = 0 := le_antisymm h hα
    subst hα0
    have hβ' : 0 < β := by linarith
    linarith [mul_pos hβ' hW1]
  · linarith [mul_pos h hU1, mul_nonneg hβ (le_of_lt hW1)]

end Bala

-- ===== Dev.Zones =====
/-!
# Zone-chain certificates and journey lemmas (generated data)
-/

namespace Bala

/-! ## Small window-action normal forms -/

lemma a_eq_act (A : M2 ℚ) : A.a = (A.act (1,0)).1 := by
  simp [M2.act]

lemma act_smul (A : M2 ℚ) (c : ℚ) (v : ℚ × ℚ) :
    A.act (c*v.1, c*v.2) = (c*(A.act v).1, c*(A.act v).2) := by
  simp only [M2.act, Prod.mk.injEq]
  constructor <;> ring

lemma Wnd_act_two (b : ℚ) (v : ℚ × ℚ) :
    (Wnd b 2).act v = (Mstep (b+1)).act ((Mstep b).act v) := by
  show (Wnd b (1+1)).act v = _
  rw [Wnd_succ, M2.act_mul, Wnd_one, Nat.cast_one]

lemma Wnd_act_three (b : ℚ) (v : ℚ × ℚ) :
    (Wnd b 3).act v
      = (Mstep (b+2)).act ((Mstep (b+1)).act ((Mstep b).act v)) := by
  show (Wnd b (2+1)).act v = _
  rw [Wnd_succ, M2.act_mul, Wnd_act_two, Nat.cast_ofNat]

lemma Wnd_act_four (b : ℚ) (v : ℚ × ℚ) :
    (Wnd b 4).act v
      = (Mstep (b+3)).act ((Mstep (b+2)).act ((Mstep (b+1)).act ((Mstep b).act v))) := by
  show (Wnd b (3+1)).act v = _
  rw [Wnd_succ, M2.act_mul, Wnd_act_three, Nat.cast_ofNat]

lemma Wnd_act_five (b : ℚ) (v : ℚ × ℚ) :
    (Wnd b 5).act v
      = (Mstep (b+4)).act ((Mstep (b+3)).act ((Mstep (b+2)).act ((Mstep (b+1)).act
          ((Mstep b).act v)))) := by
  show (Wnd b (4+1)).act v = _
  rw [Wnd_succ, M2.act_mul, Wnd_act_four, Nat.cast_ofNat]

/-! ## Generated zone-step certificates -/

lemma zstep_p320_0 {v : ℚ × ℚ}
    (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((19949:ℚ), (1428:ℚ)) ((99742:ℚ), (7175:ℚ)) ((Mstep ((3/20:ℚ) - 3)).act v) :=
  cone_step (ν := ((3/20:ℚ) - 3)) (cu0 := ((293579938177:ℚ)/5619992000)) (cu1 := ((24509707739:ℚ)/5619992000)) (cw0 := ((2094708081:ℚ)/802856000)) (cw1 := ((552461789:ℚ)/401428000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p320_1 {v : ℚ × ℚ}
    (hv : ConeAt ((19949:ℚ), (1428:ℚ)) ((99742:ℚ), (7175:ℚ)) v) :
    ConeAt ((99829:ℚ), (5847:ℚ)) ((99828:ℚ), (5867:ℚ)) ((Mstep (((3/20:ℚ) - 3) + 1)).act v) :=
  cone_step (ν := (((3/20:ℚ) - 3) + 1)) (cu0 := ((3282641892717:ℚ)/16019416000)) (cu1 := ((1784778805161:ℚ)/8009708000)) (cw0 := ((16805143474173:ℚ)/16019416000)) (cw1 := ((17456161329009:ℚ)/16019416000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p320_2 {v : ℚ × ℚ}
    (hv : ConeAt ((99829:ℚ), (5847:ℚ)) ((99828:ℚ), (5867:ℚ)) v) :
    ConeAt ((99791:ℚ), (-6460:ℚ)) ((1782:ℚ), (-115:ℚ)) ((Mstep (((3/20:ℚ) - 3) + 2)).act v) :=
  cone_step (ν := (((3/20:ℚ) - 3) + 2)) (cu0 := ((2106235401:ℚ)/143020000)) (cu1 := ((225495871389:ℚ)/286040000)) (cw0 := ((4145600169:ℚ)/286040000)) (cw1 := ((3581994177:ℚ)/4469375))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p310_0 {v : ℚ × ℚ}
    (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((99753:ℚ), (7019:ℚ)) ((99751:ℚ), (7054:ℚ)) ((Mstep ((3/10:ℚ) - 3)).act v) :=
  cone_step (ν := ((3/10:ℚ) - 3)) (cu0 := ((3637027863:ℚ)/438174125)) (cu1 := ((6167107021:ℚ)/1752696500)) (cw0 := ((182696474:ℚ)/438174125)) (cw1 := ((962119511:ℚ)/876348250))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p310_1 {v : ℚ × ℚ}
    (hv : ConeAt ((99753:ℚ), (7019:ℚ)) ((99751:ℚ), (7054:ℚ)) v) :
    ConeAt ((99851:ℚ), (5463:ℚ)) ((99850:ℚ), (5483:ℚ)) ((Mstep (((3/10:ℚ) - 3) + 1)).act v) :=
  cone_step (ν := (((3/10:ℚ) - 3) + 1)) (cu0 := ((705319994871:ℚ)/1001241500)) (cu1 := ((763108919577:ℚ)/1001241500)) (cw0 := ((28848575619:ℚ)/40049660)) (cw1 := ((747243111261:ℚ)/1001241500))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p310_2 {v : ℚ × ℚ}
    (hv : ConeAt ((99851:ℚ), (5463:ℚ)) ((99850:ℚ), (5483:ℚ)) v) :
    ConeAt ((-74103:ℚ), (-67147:ℚ)) ((-6174:ℚ), (-5597:ℚ)) ((Mstep (((3/10:ℚ) - 3) + 2)).act v) :=
  cone_step (ν := (((3/10:ℚ) - 3) + 2)) (cu0 := ((34147617:ℚ)/31485500)) (cu1 := ((105450999:ℚ)/6297100)) (cw0 := ((20890009:ℚ)/15742750)) (cw1 := ((217839991:ℚ)/15742750))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p310_3 {v : ℚ × ℚ}
    (hv : ConeAt ((-74103:ℚ), (-67147:ℚ)) ((-6174:ℚ), (-5597:ℚ)) v) :
    ConeAt ((-99766:ℚ), (6839:ℚ)) ((-99767:ℚ), (6817:ℚ)) ((Mstep (((3/10:ℚ) - 3) + 3)).act v) :=
  cone_step (ν := (((3/10:ℚ) - 3) + 3)) (cu0 := ((1302911909:ℚ)/1100845500)) (cu1 := ((1181925173:ℚ)/1100845500)) (cw0 := ((4709957:ℚ)/55042275)) (cw1 := ((28218757:ℚ)/275211375))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p310_4 {v : ℚ × ℚ}
    (hv : ConeAt ((-99766:ℚ), (6839:ℚ)) ((-99767:ℚ), (6817:ℚ)) v) :
    ConeAt ((-99297:ℚ), (-11837:ℚ)) ((-99295:ℚ), (-11857:ℚ)) ((Mstep (((3/10:ℚ) - 3) + 4)).act v) :=
  cone_step (ν := (((3/10:ℚ) - 3) + 4)) (cu0 := ((102690313827:ℚ)/502403500)) (cu1 := ((103993689309:ℚ)/502403500)) (cw0 := ((41477201463:ℚ)/200961400)) (cw1 := ((205989521469:ℚ)/1004807000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p12_0 {v : ℚ × ℚ}
    (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((99766:ℚ), (6831:ℚ)) ((99764:ℚ), (6865:ℚ)) ((Mstep ((1/2:ℚ) - 3)).act v) :=
  cone_step (ν := ((1/2:ℚ) - 3)) (cu0 := ((83881407:ℚ)/13622824)) (cu1 := ((32686215:ℚ)/13622824)) (cw0 := ((536949:ℚ)/1702853)) (cw1 := ((1330539:ℚ)/1702853))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p12_1 {v : ℚ × ℚ}
    (hv : ConeAt ((99766:ℚ), (6831:ℚ)) ((99764:ℚ), (6865:ℚ)) v) :
    ConeAt ((99886:ℚ), (4765:ℚ)) ((6659:ℚ), (319:ℚ)) ((Mstep (((1/2:ℚ) - 3) + 1)).act v) :=
  cone_step (ν := (((1/2:ℚ) - 3) + 1)) (cu0 := ((108693067:ℚ)/266998)) (cu1 := ((1674770449:ℚ)/266998)) (cw0 := ((55379964:ℚ)/133499)) (cw1 := ((821915498:ℚ)/133499))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p12_2 {v : ℚ × ℚ}
    (hv : ConeAt ((99886:ℚ), (4765:ℚ)) ((6659:ℚ), (319:ℚ)) v) :
    ConeAt ((-10000:ℚ), (1:ℚ)) ((-10000:ℚ), (-1:ℚ)) ((Mstep (((1/2:ℚ) - 3) + 2)).act v) :=
  cone_step (ν := (((1/2:ℚ) - 3) + 2)) (cu0 := ((831207:ℚ)/20000)) (cu1 := ((831207:ℚ)/20000)) (cw0 := ((221661:ℚ)/80000)) (cw1 := ((221661:ℚ)/80000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p12_3 {v : ℚ × ℚ}
    (hv : ConeAt ((-10000:ℚ), (1:ℚ)) ((-10000:ℚ), (-1:ℚ)) v) :
    ConeAt ((98389:ℚ), (17879:ℚ)) ((32795:ℚ), (5966:ℚ)) ((Mstep (((1/2:ℚ) - 3) + 3)).act v) :=
  cone_step (ν := (((1/2:ℚ) - 3) + 3)) (cu0 := ((270000:ℚ)/646969)) (cu1 := ((817500:ℚ)/646969)) (cw0 := ((270000:ℚ)/646969)) (cw1 := ((817500:ℚ)/646969))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p12_4 {v : ℚ × ℚ}
    (hv : ConeAt ((98389:ℚ), (17879:ℚ)) ((32795:ℚ), (5966:ℚ)) v) :
    ConeAt ((33116:ℚ), (3801:ℚ)) ((99345:ℚ), (11423:ℚ)) ((Mstep (((1/2:ℚ) - 3) + 4)).act v) :=
  cone_step (ν := (((1/2:ℚ) - 3) + 4)) (cu0 := ((3235705799:ℚ)/2694892)) (cu1 := ((1128435307:ℚ)/2694892)) (cw0 := ((1090392659:ℚ)/2694892)) (cw1 := ((372180767:ℚ)/2694892))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p710_0 {v : ℚ × ℚ}
    (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((49891:ℚ), (3300:ℚ)) ((19956:ℚ), (1327:ℚ)) ((Mstep ((7/10:ℚ) - 3)).act v) :=
  cone_step (ν := ((7/10:ℚ) - 3)) (cu0 := ((1486513209:ℚ)/175278500)) (cu1 := ((776105667:ℚ)/87639250)) (cw0 := ((39843153:ℚ)/87639250)) (cw1 := ((119001141:ℚ)/43819625))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p710_1 {v : ℚ × ℚ}
    (hv : ConeAt ((49891:ℚ), (3300:ℚ)) ((19956:ℚ), (1327:ℚ)) v) :
    ConeAt ((24983:ℚ), (922:ℚ)) ((99931:ℚ), (3708:ℚ)) ((Mstep (((7/10:ℚ) - 3) + 1)).act v) :=
  cone_step (ν := (((7/10:ℚ) - 3) + 1)) (cu0 := ((24817754613:ℚ)/62572750)) (cu1 := ((13440826983:ℚ)/125145500)) (cw0 := ((5043001131:ℚ)/31286375)) (cw1 := ((2648551203:ℚ)/62572750))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p710_2 {v : ℚ × ℚ}
    (hv : ConeAt ((24983:ℚ), (922:ℚ)) ((99931:ℚ), (3708:ℚ)) v) :
    ConeAt ((13612:ℚ), (14653:ℚ)) ((17011:ℚ), (18320:ℚ)) ((Mstep (((7/10:ℚ) - 3) + 2)).act v) :=
  cone_step (ν := (((7/10:ℚ) - 3) + 2)) (cu0 := ((41465031:ℚ)/27414250)) (cu1 := ((57189031:ℚ)/54828500)) (cw0 := ((146770507:ℚ)/27414250)) (cw1 := ((51857663:ℚ)/10965700))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p710_3 {v : ℚ × ℚ}
    (hv : ConeAt ((13612:ℚ), (14653:ℚ)) ((17011:ℚ), (18320:ℚ)) v) :
    ConeAt ((-99370:ℚ), (-11207:ℚ)) ((-99367:ℚ), (-11229:ℚ)) ((Mstep (((7/10:ℚ) - 3) + 3)).act v) :=
  cone_step (ν := (((7/10:ℚ) - 3) + 3)) (cu0 := ((118980087:ℚ)/554940250)) (cu1 := ((31143639:ℚ)/110988050)) (cw0 := ((372823743:ℚ)/1109880500)) (cw1 := ((313908327:ℚ)/1109880500))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p710_4 {v : ℚ × ℚ}
    (hv : ConeAt ((-99370:ℚ), (-11207:ℚ)) ((-99367:ℚ), (-11229:ℚ)) v) :
    ConeAt ((-33124:ℚ), (-3729:ℚ)) ((-99370:ℚ), (-11207:ℚ)) ((Mstep (((7/10:ℚ) - 3) + 4)).act v) :=
  cone_step (ν := (((7/10:ℚ) - 3) + 4)) (cu0 := ((364329922227:ℚ)/167484500)) (cu1 := ((124002393471:ℚ)/167484500)) (cw0 := ((738710759427:ℚ)/334969000)) (cw1 := ((244645653879:ℚ)/334969000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p1720_0 {v : ℚ × ℚ}
    (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((99796:ℚ), (6391:ℚ)) ((99793:ℚ), (6425:ℚ)) ((Mstep ((17/20:ℚ) - 3)).act v) :=
  cone_step (ν := ((17/20:ℚ) - 3)) (cu0 := ((42755289219:ℚ)/13648948000)) (cu1 := ((7496666133:ℚ)/5459579200)) (cw0 := ((4460684823:ℚ)/27297896000)) (cw1 := ((11302182969:ℚ)/27297896000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p1720_1 {v : ℚ × ℚ}
    (hv : ConeAt ((99796:ℚ), (6391:ℚ)) ((99793:ℚ), (6425:ℚ)) v) :
    ConeAt ((33324:ℚ), (791:ℚ)) ((99971:ℚ), (2393:ℚ)) ((Mstep (((17/20:ℚ) - 3) + 1)).act v) :=
  cone_step (ν := (((17/20:ℚ) - 3) + 1)) (cu0 := ((344365777197:ℚ)/1067633600)) (cu1 := ((591006168597:ℚ)/5338168000)) (cw0 := ((1739076779481:ℚ)/5338168000)) (cw1 := ((292635023007:ℚ)/2669084000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p1720_2 {v : ℚ × ℚ}
    (hv : ConeAt ((33324:ℚ), (791:ℚ)) ((99971:ℚ), (2393:ℚ)) v) :
    ConeAt ((97149:ℚ), (23710:ℚ)) ((48572:ℚ), (11865:ℚ)) ((Mstep (((17/20:ℚ) - 3) + 2)).act v) :=
  cone_step (ν := (((17/20:ℚ) - 3) + 2)) (cu0 := ((12277986357:ℚ)/8246120000)) (cu1 := ((13398012503:ℚ)/4123060000)) (cw0 := ((9723415247:ℚ)/2061530000)) (cw1 := ((76270602709:ℚ)/8246120000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p1720_3 {v : ℚ × ℚ}
    (hv : ConeAt ((97149:ℚ), (23710:ℚ)) ((48572:ℚ), (11865:ℚ)) v) :
    ConeAt ((99183:ℚ), (12760:ℚ)) ((551:ℚ), (71:ℚ)) ((Mstep (((17/20:ℚ) - 3) + 3)).act v) :=
  cone_step (ν := (((17/20:ℚ) - 3) + 3)) (cu0 := ((128251731:ℚ)/8986400)) (cu1 := ((214794351417:ℚ)/89864000)) (cw0 := ((126001893:ℚ)/17972800)) (cw1 := ((27351850569:ℚ)/22466000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zstep_p1720_4 {v : ℚ × ℚ}
    (hv : ConeAt ((99183:ℚ), (12760:ℚ)) ((551:ℚ), (71:ℚ)) v) :
    ConeAt ((99391:ℚ), (11019:ℚ)) ((5231:ℚ), (581:ℚ)) ((Mstep (((17/20:ℚ) - 3) + 4)).act v) :=
  cone_step (ν := (((17/20:ℚ) - 3) + 4)) (cu0 := ((3714731307:ℚ)/3385024)) (cu1 := ((4171703475609:ℚ)/211564000)) (cw0 := ((5225306931:ℚ)/846256000)) (cw1 := ((91447828473:ℚ)/846256000))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    hv

lemma zone_run_p310 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((-99297:ℚ), (-11837:ℚ)) ((-99295:ℚ), (-11857:ℚ)) ((Wnd ((3/10:ℚ) - 3) 5).act v) := by
  rw [Wnd_act_five]
  exact zstep_p310_4 (zstep_p310_3 (zstep_p310_2 (zstep_p310_1 (zstep_p310_0 hv))))

lemma zone_up_p310 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    UpCone ((-1:ℚ) * ((Wnd ((3/10:ℚ) - 3) 5).act v).1, (-1:ℚ) * ((Wnd ((3/10:ℚ) - 3) 5).act v).2) :=
  cone_to_up (-1:ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (zone_run_p310 hv)

lemma zone_run_p12 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((33116:ℚ), (3801:ℚ)) ((99345:ℚ), (11423:ℚ)) ((Wnd ((1/2:ℚ) - 3) 5).act v) := by
  rw [Wnd_act_five]
  exact zstep_p12_4 (zstep_p12_3 (zstep_p12_2 (zstep_p12_1 (zstep_p12_0 hv))))

lemma zone_up_p12 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    UpCone ((1:ℚ) * ((Wnd ((1/2:ℚ) - 3) 5).act v).1, (1:ℚ) * ((Wnd ((1/2:ℚ) - 3) 5).act v).2) :=
  cone_to_up (1:ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (zone_run_p12 hv)

lemma zone_run_p710 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((-33124:ℚ), (-3729:ℚ)) ((-99370:ℚ), (-11207:ℚ)) ((Wnd ((7/10:ℚ) - 3) 5).act v) := by
  rw [Wnd_act_five]
  exact zstep_p710_4 (zstep_p710_3 (zstep_p710_2 (zstep_p710_1 (zstep_p710_0 hv))))

lemma zone_up_p710 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    UpCone ((-1:ℚ) * ((Wnd ((7/10:ℚ) - 3) 5).act v).1, (-1:ℚ) * ((Wnd ((7/10:ℚ) - 3) 5).act v).2) :=
  cone_to_up (-1:ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (zone_run_p710 hv)

lemma zone_run_p1720 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    ConeAt ((99391:ℚ), (11019:ℚ)) ((5231:ℚ), (581:ℚ)) ((Wnd ((17/20:ℚ) - 3) 5).act v) := by
  rw [Wnd_act_five]
  exact zstep_p1720_4 (zstep_p1720_3 (zstep_p1720_2 (zstep_p1720_1 (zstep_p1720_0 hv))))

lemma zone_up_p1720 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    UpCone ((1:ℚ) * ((Wnd ((17/20:ℚ) - 3) 5).act v).1, (1:ℚ) * ((Wnd ((17/20:ℚ) - 3) 5).act v).2) :=
  cone_to_up (1:ℚ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (zone_run_p1720 hv)

lemma ee1_p320 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    0 < (1:ℚ) * ((Wnd ((3/20:ℚ) - 3) 3).act v).1 := by
  rw [Wnd_act_three]
  exact cone_fst_sign (1:ℚ) (by norm_num) (by norm_num)
    (zstep_p320_2 (zstep_p320_1 (zstep_p320_0 hv)))

lemma ee1_p310 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    0 < (-1:ℚ) * ((Wnd ((3/10:ℚ) - 3) 3).act v).1 := by
  rw [Wnd_act_three]
  exact cone_fst_sign (-1:ℚ) (by norm_num) (by norm_num)
    (zstep_p310_2 (zstep_p310_1 (zstep_p310_0 hv)))

lemma ee1_p710 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    0 < (1:ℚ) * ((Wnd ((7/10:ℚ) - 3) 3).act v).1 := by
  rw [Wnd_act_three]
  exact cone_fst_sign (1:ℚ) (by norm_num) (by norm_num)
    (zstep_p710_2 (zstep_p710_1 (zstep_p710_0 hv)))

lemma ee0_p310 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    0 < (-1:ℚ) * ((Wnd ((3/10:ℚ) - 3) 4).act v).1 := by
  rw [Wnd_act_four]
  exact cone_fst_sign (-1:ℚ) (by norm_num) (by norm_num)
    (zstep_p310_3 (zstep_p310_2 (zstep_p310_1 (zstep_p310_0 hv))))

lemma ee0_p12 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    0 < (1:ℚ) * ((Wnd ((1/2:ℚ) - 3) 4).act v).1 := by
  rw [Wnd_act_four]
  exact cone_fst_sign (1:ℚ) (by norm_num) (by norm_num)
    (zstep_p12_3 (zstep_p12_2 (zstep_p12_1 (zstep_p12_0 hv))))

lemma ee0_p710 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    0 < (-1:ℚ) * ((Wnd ((7/10:ℚ) - 3) 4).act v).1 := by
  rw [Wnd_act_four]
  exact cone_fst_sign (-1:ℚ) (by norm_num) (by norm_num)
    (zstep_p710_3 (zstep_p710_2 (zstep_p710_1 (zstep_p710_0 hv))))

lemma ee0_p1720 {v : ℚ × ℚ} (hv : ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v) :
    0 < (1:ℚ) * ((Wnd ((17/20:ℚ) - 3) 4).act v).1 := by
  rw [Wnd_act_four]
  exact cone_fst_sign (1:ℚ) (by norm_num) (by norm_num)
    (zstep_p1720_3 (zstep_p1720_2 (zstep_p1720_1 (zstep_p1720_0 hv))))

lemma sl_p310_m3 :
    UpCone ((-1:ℚ) * ((Wnd ((3/10:ℚ) + (-3)) 5).act (1,0)).1,
            (-1:ℚ) * ((Wnd ((3/10:ℚ) + (-3)) 5).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p310_m2 :
    UpCone ((-1:ℚ) * ((Wnd ((3/10:ℚ) + (-2)) 4).act (1,0)).1,
            (-1:ℚ) * ((Wnd ((3/10:ℚ) + (-2)) 4).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p310_m1 :
    UpCone ((-1:ℚ) * ((Wnd ((3/10:ℚ) + (-1)) 3).act (1,0)).1,
            (-1:ℚ) * ((Wnd ((3/10:ℚ) + (-1)) 3).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p12_m3 :
    UpCone ((1:ℚ) * ((Wnd ((1/2:ℚ) + (-3)) 5).act (1,0)).1,
            (1:ℚ) * ((Wnd ((1/2:ℚ) + (-3)) 5).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p12_m2 :
    UpCone ((1:ℚ) * ((Wnd ((1/2:ℚ) + (-2)) 4).act (1,0)).1,
            (1:ℚ) * ((Wnd ((1/2:ℚ) + (-2)) 4).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p12_m1 :
    UpCone ((1:ℚ) * ((Wnd ((1/2:ℚ) + (-1)) 3).act (1,0)).1,
            (1:ℚ) * ((Wnd ((1/2:ℚ) + (-1)) 3).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p12_0 :
    UpCone ((-1:ℚ) * ((Wnd ((1/2:ℚ) + 0) 2).act (1,0)).1,
            (-1:ℚ) * ((Wnd ((1/2:ℚ) + 0) 2).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p710_m3 :
    UpCone ((-1:ℚ) * ((Wnd ((7/10:ℚ) + (-3)) 5).act (1,0)).1,
            (-1:ℚ) * ((Wnd ((7/10:ℚ) + (-3)) 5).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p710_m2 :
    UpCone ((-1:ℚ) * ((Wnd ((7/10:ℚ) + (-2)) 4).act (1,0)).1,
            (-1:ℚ) * ((Wnd ((7/10:ℚ) + (-2)) 4).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p710_m1 :
    UpCone ((-1:ℚ) * ((Wnd ((7/10:ℚ) + (-1)) 3).act (1,0)).1,
            (-1:ℚ) * ((Wnd ((7/10:ℚ) + (-1)) 3).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p1720_m3 :
    UpCone ((1:ℚ) * ((Wnd ((17/20:ℚ) + (-3)) 5).act (1,0)).1,
            (1:ℚ) * ((Wnd ((17/20:ℚ) + (-3)) 5).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p1720_m2 :
    UpCone ((1:ℚ) * ((Wnd ((17/20:ℚ) + (-2)) 4).act (1,0)).1,
            (1:ℚ) * ((Wnd ((17/20:ℚ) + (-2)) 4).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p1720_m1 :
    UpCone ((1:ℚ) * ((Wnd ((17/20:ℚ) + (-1)) 3).act (1,0)).1,
            (1:ℚ) * ((Wnd ((17/20:ℚ) + (-1)) 3).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

lemma sl_p1720_0 :
    UpCone ((1:ℚ) * ((Wnd ((17/20:ℚ) + 0) 2).act (1,0)).1,
            (1:ℚ) * ((Wnd ((17/20:ℚ) + 0) 2).act (1,0)).2) := by
  unfold UpCone
  decide +kernel

/-! ## Generic journey lemmas -/

lemma journey_sl' (b : ℚ) (σ : ℚ) (k : ℕ)
    (hsl : UpCone (σ * ((Wnd b k).act (1,0)).1, σ * ((Wnd b k).act (1,0)).2))
    (hup : 11/10 ≤ b + k)
    (len : ℕ) (hlen : k ≤ len) :
    0 < σ * (Wnd b len).a := by
  obtain ⟨u, rfl⟩ : ∃ u, len = k + u := ⟨len - k, by omega⟩
  rw [a_eq_act, Wnd_split b k u, M2.act_mul]
  have h4 := up_run (b + (k:ℚ)) hup u _ hsl
  rw [act_smul] at h4
  exact UpCone_pos_fst _ h4

lemma journey_gen' (b c σ : ℚ) (d : ℕ) (hd1 : 1 ≤ d) (hdown : b + d - 1 ≤ -3)
    (hc : c = b + d)
    (hzone : ∀ v : ℚ × ℚ, ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v →
      UpCone (σ * ((Wnd c 5).act v).1, σ * ((Wnd c 5).act v).2))
    (hup : 11/10 ≤ c + 5)
    (len : ℕ) (hlen : d + 5 ≤ len) :
    0 < σ * (Wnd b len).a := by
  obtain ⟨u, rfl⟩ : ∃ u, len = (d + 5) + u := ⟨len - (d+5), by omega⟩
  rw [a_eq_act, Wnd_split b (d+5) u, M2.act_mul, Wnd_split b d 5, M2.act_mul]
  have h1 : DownState ((Wnd b d).act (1, 0)) := down_run b d hd1 hdown
  have h2 := down_to_cone _ h1
  rw [← hc]
  have h3 := hzone _ h2
  have hcast : b + ((d + 5 : ℕ) : ℚ) = c + 5 := by
    push_cast
    push_cast at hc
    linarith
  rw [hcast]
  have h4 := up_run (c+5) hup u _ h3
  rw [act_smul] at h4
  exact UpCone_pos_fst _ h4

lemma journey_ee' (b c ε : ℚ) (d : ℕ) (hd1 : 1 ≤ d) (hdown : b + d - 1 ≤ -3)
    (hc : c = b + d) (z : ℕ)
    (hee : ∀ v : ℚ × ℚ, ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v →
      0 < ε * ((Wnd c z).act v).1)
    (len : ℕ) (hlen : len = d + z) :
    0 < ε * (Wnd b len).a := by
  subst hlen
  rw [a_eq_act, Wnd_split b d z, M2.act_mul]
  have h1 : DownState ((Wnd b d).act (1, 0)) := down_run b d hd1 hdown
  have h2 := down_to_cone _ h1
  rw [← hc]
  exact hee _ h2

end Bala

-- ===== Dev.Alt =====
/-!
# Alternation of the window numerators at the test points (m arbitrary, len ≥ 5)
-/

namespace Bala

open Polynomial

lemma eval_Wnd_a (b : ℚ[X]) (len : ℕ) (t : ℚ) :
    (Wnd b len).a.eval t = (Wnd (b.eval t) len).a := by
  rw [← emap_eval_Wnd]
  rfl

/-! ## The test points -/

/-- Phase for offset `r` inside a block. -/
noncomputable def phaseOf (r : ℕ) : ℚ :=
  if r = 0 then 3/10 else if r = 1 then 1/2 else if r = 2 then 7/10 else 17/20

/-- The phase of test point `i`. -/
noncomputable def altd (len i : ℕ) : ℚ :=
  if i = 0 then 3/20
  else if i = 1 then 3/10
  else if i = 2 then 7/10
  else if i = 4*len - 1 then 1/2
  else if i = 4*len then 17/20
  else phaseOf ((i-3) % 4)

/-- The block (unit) of test point `i`, relative to the lowest block. -/
def altu (len i : ℕ) : ℕ :=
  if i ≤ 2 then 0
  else if 4*len - 1 ≤ i then len
  else 1 + (i-3)/4

/-- Test point `i` for the window of length `len`. -/
noncomputable def altpt (m len i : ℕ) : ℚ :=
  (((m:ℚ) - 1 - (len:ℚ)) + (altu len i : ℚ) + altd len i) / m

lemma altu_head (len i : ℕ) (h : i ≤ 2) : altu len i = 0 := by
  unfold altu
  rw [if_pos h]

lemma altu_tail (len i : ℕ) (h : 4*len - 1 ≤ i) (hl : 1 ≤ len) : altu len i = len := by
  unfold altu
  rw [if_neg (by omega), if_pos h]

lemma altu_mid (len i : ℕ) (h3 : 3 ≤ i) (h4 : i ≤ 4*len - 2) (hl : 5 ≤ len) :
    altu len i = 1 + (i-3)/4 := by
  unfold altu
  rw [if_neg (by omega), if_neg (by omega)]

lemma altd_0 (len : ℕ) : altd len 0 = 3/20 := by
  unfold altd
  rw [if_pos rfl]

lemma altd_1 (len : ℕ) (hl : 5 ≤ len) : altd len 1 = 3/10 := by
  unfold altd
  rw [if_neg (by omega), if_pos rfl]

lemma altd_2 (len : ℕ) (hl : 5 ≤ len) : altd len 2 = 7/10 := by
  unfold altd
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

lemma altd_tail1 (len : ℕ) (hl : 1 ≤ len) : altd len (4*len-1) = 1/2 := by
  unfold altd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

lemma altd_tail0 (len : ℕ) (hl : 1 ≤ len) : altd len (4*len) = 17/20 := by
  unfold altd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]

lemma altd_mid (len i : ℕ) (h3 : 3 ≤ i) (h4 : i ≤ 4*len - 2) (hl : 5 ≤ len) :
    altd len i = phaseOf ((i-3) % 4) := by
  unfold altd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-! ## Helpers for the `i = 3 + 4q + r` decomposition -/

lemma sub3_mod4 (q r : ℕ) (hr : r < 4) : (3 + 4*q + r - 3) % 4 = r := by omega

lemma sub3_div4 (q r : ℕ) (hr : r < 4) : (3 + 4*q + r - 3) / 4 = q := by omega

lemma altu_mid4 (len q r : ℕ) (hr : r < 4) (h4 : 3+4*q+r ≤ 4*len - 2) (hl : 5 ≤ len) :
    altu len (3+4*q+r) = 1 + q := by
  rw [altu_mid len _ (by omega) h4 hl, sub3_div4 q r hr]

lemma altd_mid4 (len q r : ℕ) (hr : r < 4) (h4 : 3+4*q+r ≤ 4*len - 2) (hl : 5 ≤ len) :
    altd len (3+4*q+r) = phaseOf r := by
  rw [altd_mid len _ (by omega) h4 hl, sub3_mod4 q r hr]

lemma phaseOf_0 : phaseOf 0 = 3/10 := by norm_num [phaseOf]
lemma phaseOf_1 : phaseOf 1 = 1/2 := by norm_num [phaseOf]
lemma phaseOf_2 : phaseOf 2 = 7/10 := by norm_num [phaseOf]
lemma phaseOf_3 : phaseOf 3 = 17/20 := by norm_num [phaseOf]

/-- The affine change of variables sending test points to block coordinates. -/
lemma altpt_base (m len i : ℕ) (hm0 : (m:ℚ) ≠ 0) :
    (m:ℚ) * altpt m len i + ((1-(m:ℤ):ℤ):ℚ) =
      (altu len i : ℚ) + altd len i - (len:ℚ) := by
  unfold altpt
  rw [mul_comm, div_mul_cancel₀ _ hm0]
  push_cast
  ring

/-! ## Monotonicity of the test points -/

theorem altpt_mono (m len : ℕ) (hm : 1 ≤ m) (hl : 5 ≤ len) (i : ℕ)
    (hi : i + 1 ≤ 4*len) : altpt m len i < altpt m len (i+1) := by
  have hm' : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  unfold altpt
  rw [div_lt_div_iff_of_pos_right hm']
  have key : (altu len i : ℚ) + altd len i < (altu len (i+1) : ℚ) + altd len (i+1) := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ (3 ≤ i ∧ i + 1 ≤ 4*len - 2) ∨
        i = 4*len - 2 ∨ i = 4*len - 1) with h | h | h | ⟨h3, h4⟩ | h | h
    · subst h
      rw [altu_head len 0 (by omega), altu_head len 1 (by omega), altd_0,
        altd_1 len hl]
      norm_num
    · subst h
      rw [altu_head len 1 (by omega), altu_head len 2 (by omega), altd_1 len hl,
        altd_2 len hl]
      norm_num
    · subst h
      rw [altu_head len 2 (by omega), altd_2 len hl,
        (by norm_num : (2+1 : ℕ) = 3+4*0+0), altu_mid4 len 0 0 (by norm_num) (by omega) hl,
        altd_mid4 len 0 0 (by norm_num) (by omega) hl, phaseOf_0]
      norm_num
    · obtain ⟨q, r, hr4, rfl⟩ : ∃ q r, r < 4 ∧ i = 3 + 4*q + r :=
        ⟨(i-3)/4, (i-3)%4, Nat.mod_lt _ (by norm_num), by omega⟩
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with hr | hr | hr | hr <;> subst hr
      · rw [altu_mid4 len q 0 (by norm_num) (Nat.le_of_succ_le h4) hl,
          altd_mid4 len q 0 (by norm_num) (Nat.le_of_succ_le h4) hl,
          (by ring : 3+4*q+0+1 = 3+4*q+1), altu_mid4 len q 1 (by norm_num) h4 hl,
          altd_mid4 len q 1 (by norm_num) h4 hl, phaseOf_0, phaseOf_1]
        exact add_lt_add_right (show (3:ℚ)/10 < 1/2 by norm_num) _
      · rw [altu_mid4 len q 1 (by norm_num) (Nat.le_of_succ_le h4) hl,
          altd_mid4 len q 1 (by norm_num) (Nat.le_of_succ_le h4) hl,
          (by ring : 3+4*q+1+1 = 3+4*q+2), altu_mid4 len q 2 (by norm_num) h4 hl,
          altd_mid4 len q 2 (by norm_num) h4 hl, phaseOf_1, phaseOf_2]
        exact add_lt_add_right (show (1:ℚ)/2 < 7/10 by norm_num) _
      · rw [altu_mid4 len q 2 (by norm_num) (Nat.le_of_succ_le h4) hl,
          altd_mid4 len q 2 (by norm_num) (Nat.le_of_succ_le h4) hl,
          (by ring : 3+4*q+2+1 = 3+4*q+3), altu_mid4 len q 3 (by norm_num) h4 hl,
          altd_mid4 len q 3 (by norm_num) h4 hl, phaseOf_2, phaseOf_3]
        exact add_lt_add_right (show (7:ℚ)/10 < 17/20 by norm_num) _
      · rw [altu_mid4 len q 3 (by norm_num) (Nat.le_of_succ_le h4) hl,
          altd_mid4 len q 3 (by norm_num) (Nat.le_of_succ_le h4) hl,
          (by ring : 3+4*q+3+1 = 3+4*(q+1)+0),
          altu_mid4 len (q+1) 0 (by norm_num) h4 hl,
          altd_mid4 len (q+1) 0 (by norm_num) h4 hl, phaseOf_3, phaseOf_0]
        push_cast
        linarith
    · subst h
      rw [(by omega : 4*len-2 = 3+4*(len-2)+3),
        altu_mid4 len (len-2) 3 (by norm_num) (by omega) hl,
        altd_mid4 len (len-2) 3 (by norm_num) (by omega) hl, phaseOf_3,
        (by omega : 3+4*(len-2)+3+1 = 4*len-1),
        altu_tail len (4*len-1) (by omega) (by omega), altd_tail1 len (by omega)]
      push_cast [Nat.cast_sub (by omega : 2 ≤ len)]
      linarith
    · subst h
      rw [altu_tail len (4*len-1) (by omega) (by omega), (by omega : 4*len-1+1 = 4*len),
        altu_tail len (4*len) (by omega) (by omega), altd_tail1 len (by omega),
        altd_tail0 len (by omega)]
      exact add_lt_add_right (show (1:ℚ)/2 < 17/20 by norm_num) _
  linarith only [key]

/-! ## Per-phase journeys for negative block offsets -/

lemma journeyP_gen (δ σ : ℚ) (hδl : -9/10 ≤ δ) (hδu : δ ≤ 1)
    (hee : ∀ v : ℚ × ℚ, ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v →
      0 < σ * ((Wnd (δ - 3) 4).act v).1)
    (hzone : ∀ v : ℚ × ℚ, ConeAt ((109:ℚ), (10:ℚ)) ((14:ℚ), (1:ℚ)) v →
      UpCone (σ * ((Wnd (δ - 3) 5).act v).1, σ * ((Wnd (δ - 3) 5).act v).2))
    (hsl3 : UpCone (σ * ((Wnd (δ + (-3)) 5).act (1,0)).1,
                    σ * ((Wnd (δ + (-3)) 5).act (1,0)).2))
    (hsl2 : UpCone (σ * ((Wnd (δ + (-2)) 4).act (1,0)).1,
                    σ * ((Wnd (δ + (-2)) 4).act (1,0)).2))
    (hsl1 : UpCone (σ * ((Wnd (δ + (-1)) 3).act (1,0)).1,
                    σ * ((Wnd (δ + (-1)) 3).act (1,0)).2))
    (len : ℕ) (hl : 5 ≤ len) (i_b : ℤ)
    (hib1 : 1-(len:ℤ) ≤ i_b) (hib2 : i_b ≤ -1) (b : ℚ) (hb : b = δ + (i_b:ℚ)) :
    0 < σ * (Wnd b len).a := by
  rcases (by omega : i_b = 1-(len:ℤ) ∨ (2-(len:ℤ) ≤ i_b ∧ i_b ≤ -4) ∨ i_b = -3 ∨
      i_b = -2 ∨ i_b = -1) with h | ⟨h1, h2⟩ | h | h | h
  · subst h
    have hcast : ((len-4:ℕ):ℚ) = (len:ℚ) - 4 := by
      push_cast [Nat.cast_sub (by omega : 4 ≤ len)]
      ring
    refine journey_ee' b (δ - 3) σ (len-4) (by omega) ?_ ?_ 4
      (fun v hv => hee v hv) len (by omega)
    · rw [hb, hcast]
      push_cast
      linarith
    · rw [hb, hcast]
      push_cast
      ring
  · set d : ℕ := (-3 - i_b).toNat with hd
    have hdz : (d:ℤ) = -3 - i_b := by omega
    have hdq : (d:ℚ) = -3 - (i_b:ℚ) := by exact_mod_cast hdz
    refine journey_gen' b (δ - 3) σ d (by omega) ?_ ?_
      (fun v hv => hzone v hv) (by linarith) len (by omega)
    · rw [hb, hdq]
      push_cast
      linarith
    · rw [hb, hdq]
      push_cast
      ring
  · subst h
    have hb' : b = δ + (-3) := by rw [hb]; norm_num
    subst hb'
    exact journey_sl' (δ + (-3)) σ 5 hsl3 (by push_cast; linarith) len (by omega)
  · subst h
    have hb' : b = δ + (-2) := by rw [hb]; norm_num
    subst hb'
    exact journey_sl' (δ + (-2)) σ 4 hsl2 (by push_cast; linarith) len (by omega)
  · subst h
    have hb' : b = δ + (-1) := by rw [hb]; norm_num
    subst hb'
    exact journey_sl' (δ + (-1)) σ 3 hsl1 (by push_cast; linarith) len (by omega)

lemma journeyP_p310 (len : ℕ) (hl : 5 ≤ len) (i_b : ℤ)
    (hib1 : 1-(len:ℤ) ≤ i_b) (hib2 : i_b ≤ -1) (b : ℚ) (hb : b = (3/10:ℚ) + (i_b:ℚ)) :
    0 < (-1:ℚ) * (Wnd b len).a :=
  journeyP_gen (3/10) (-1) (by norm_num) (by norm_num)
    (fun v hv => ee0_p310 hv) (fun v hv => zone_up_p310 hv)
    sl_p310_m3 sl_p310_m2 sl_p310_m1 len hl i_b hib1 hib2 b hb

lemma journeyP_p12 (len : ℕ) (hl : 5 ≤ len) (i_b : ℤ)
    (hib1 : 1-(len:ℤ) ≤ i_b) (hib2 : i_b ≤ -1) (b : ℚ) (hb : b = (1/2:ℚ) + (i_b:ℚ)) :
    0 < (1:ℚ) * (Wnd b len).a :=
  journeyP_gen (1/2) 1 (by norm_num) (by norm_num)
    (fun v hv => ee0_p12 hv) (fun v hv => zone_up_p12 hv)
    sl_p12_m3 sl_p12_m2 sl_p12_m1 len hl i_b hib1 hib2 b hb

lemma journeyP_p710 (len : ℕ) (hl : 5 ≤ len) (i_b : ℤ)
    (hib1 : 1-(len:ℤ) ≤ i_b) (hib2 : i_b ≤ -1) (b : ℚ) (hb : b = (7/10:ℚ) + (i_b:ℚ)) :
    0 < (-1:ℚ) * (Wnd b len).a :=
  journeyP_gen (7/10) (-1) (by norm_num) (by norm_num)
    (fun v hv => ee0_p710 hv) (fun v hv => zone_up_p710 hv)
    sl_p710_m3 sl_p710_m2 sl_p710_m1 len hl i_b hib1 hib2 b hb

lemma journeyP_p1720 (len : ℕ) (hl : 5 ≤ len) (i_b : ℤ)
    (hib1 : 1-(len:ℤ) ≤ i_b) (hib2 : i_b ≤ -1) (b : ℚ) (hb : b = (17/20:ℚ) + (i_b:ℚ)) :
    0 < (1:ℚ) * (Wnd b len).a :=
  journeyP_gen (17/20) 1 (by norm_num) (by norm_num)
    (fun v hv => ee0_p1720 hv) (fun v hv => zone_up_p1720 hv)
    sl_p1720_m3 sl_p1720_m2 sl_p1720_m1 len hl i_b hib1 hib2 b hb

/-! ## The master alternation theorem -/

theorem theta_alt (m len : ℕ) (hm : 1 ≤ m) (hl : 5 ≤ len) (i : ℕ) (hi : i ≤ 4*len) :
    0 < (-1:ℚ)^i * ((Wnd (pa m (1-(m:ℤ))) len).a).eval (altpt m len i) := by
  have hm' : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hm0 : (m:ℚ) ≠ 0 := ne_of_gt hm'
  have hc3 : ((len-3:ℕ):ℚ) = (len:ℚ) - 3 := by
    push_cast [Nat.cast_sub (show 3 ≤ len by omega)]
    ring
  rw [eval_Wnd_a, pa_eval, altpt_base m len i hm0]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ (3 ≤ i ∧ i ≤ 4*len - 2) ∨ i = 4*len - 1 ∨
      i = 4*len) with h | h | h | ⟨h3, h4⟩ | h | h
  · -- head, δ = 3/20, ee(-1), sign +
    subst h
    rw [altu_head len 0 (by omega), altd_0, pow_zero]
    refine journey_ee' _ ((3/20:ℚ) - 3) 1 (len-3) (by omega) ?_ ?_ 3
      (fun v hv => ee1_p320 hv) len (by omega)
    · rw [hc3]; push_cast; linarith
    · rw [hc3]; push_cast; ring
  · -- head, δ = 3/10, ee(-1), sign -
    subst h
    rw [altu_head len 1 (by omega), altd_1 len hl, pow_one]
    refine journey_ee' _ ((3/10:ℚ) - 3) (-1) (len-3) (by omega) ?_ ?_ 3
      (fun v hv => ee1_p310 hv) len (by omega)
    · rw [hc3]; push_cast; linarith
    · rw [hc3]; push_cast; ring
  · -- head, δ = 7/10, ee(-1), sign +
    subst h
    rw [altu_head len 2 (by omega), altd_2 len hl, neg_one_sq]
    refine journey_ee' _ ((7/10:ℚ) - 3) 1 (len-3) (by omega) ?_ ?_ 3
      (fun v hv => ee1_p710 hv) len (by omega)
    · rw [hc3]; push_cast; linarith
    · rw [hc3]; push_cast; ring
  · -- middle blocks
    obtain ⟨q, r, hr4, rfl⟩ : ∃ q r, r < 4 ∧ i = 3 + 4*q + r :=
      ⟨(i-3)/4, (i-3)%4, Nat.mod_lt _ (by norm_num), by omega⟩
    rw [altu_mid4 len q r hr4 h4 hl, altd_mid4 len q r hr4 h4 hl]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with hr | hr | hr | hr <;> subst hr
    · -- δ = 3/10, sign -
      have hodd : Odd (3+4*q+0) := ⟨1 + 2*q, by ring⟩
      rw [hodd.neg_one_pow, phaseOf_0]
      exact journeyP_p310 len hl ((q:ℤ)+1-(len:ℤ)) (by omega) (by omega) _
        (by push_cast; ring)
    · -- δ = 1/2, sign +
      have heven : Even (3+4*q+1) := ⟨2 + 2*q, by ring⟩
      rw [heven.neg_one_pow, phaseOf_1]
      exact journeyP_p12 len hl ((q:ℤ)+1-(len:ℤ)) (by omega) (by omega) _
        (by push_cast; ring)
    · -- δ = 7/10, sign -
      have hodd : Odd (3+4*q+2) := ⟨2 + 2*q, by ring⟩
      rw [hodd.neg_one_pow, phaseOf_2]
      exact journeyP_p710 len hl ((q:ℤ)+1-(len:ℤ)) (by omega) (by omega) _
        (by push_cast; ring)
    · -- δ = 17/20, sign +
      have heven : Even (3+4*q+3) := ⟨3 + 2*q, by ring⟩
      rw [heven.neg_one_pow, phaseOf_3]
      exact journeyP_p1720 len hl ((q:ℤ)+1-(len:ℤ)) (by omega) (by omega) _
        (by push_cast; ring)
  · -- tail, δ = 1/2, SL at i_b = 0, sign -
    subst h
    have hodd : Odd (4*len-1) := ⟨2*len-1, by omega⟩
    rw [altu_tail len (4*len-1) (by omega) (by omega), altd_tail1 len (by omega),
      hodd.neg_one_pow, (by ring : ((len:ℚ) + 1/2 - (len:ℚ)) = 1/2 + 0)]
    exact journey_sl' ((1/2:ℚ) + 0) (-1) 2 sl_p12_0 (by norm_num) len (by omega)
  · -- tail, δ = 17/20, SL at i_b = 0, sign +
    subst h
    have heven : Even (4*len) := ⟨2*len, by omega⟩
    rw [altu_tail len (4*len) (by omega) (by omega), altd_tail0 len (by omega),
      heven.neg_one_pow, (by ring : ((len:ℚ) + 17/20 - (len:ℚ)) = 17/20 + 0)]
    exact journey_sl' ((17/20:ℚ) + 0) 1 2 sl_p1720_0 (by norm_num) len (by omega)

end Bala

-- ===== Dev.AltSmall =====
/-!
# Alternation for the small windows (`len ≤ 4`), by direct evaluation
-/

namespace Bala

open Polynomial

section SmallSign

/-- Generic small-case sign lemma via kernel computation. -/
private lemma theta_alt_small (m len : ℕ) (i : ℕ) (hi : i ≤ 4*len)
    (H : ∀ j : ℕ, j ≤ 4*len →
      0 < (-1:ℚ)^j * (Wnd ((m:ℚ) * altpt m len j + ((1-(m:ℤ) : ℤ) : ℚ)) len).a) :
    0 < (-1:ℚ)^i * ((Wnd (pa m (1-(m:ℤ))) len).a).eval (altpt m len i) := by
  rw [eval_Wnd_a, pa_eval]
  exact H i hi

theorem theta_alt_s21 (i : ℕ) (hi : i ≤ 4*1) :
    0 < (-1:ℚ)^i * ((Wnd (pa 2 (1-(2:ℤ))) 1).a).eval (altpt 2 1 i) :=
  theta_alt_small 2 1 i hi (by decide +kernel)

theorem theta_alt_s32 (i : ℕ) (hi : i ≤ 4*2) :
    0 < (-1:ℚ)^i * ((Wnd (pa 3 (1-(3:ℤ))) 2).a).eval (altpt 3 2 i) :=
  theta_alt_small 3 2 i hi (by decide +kernel)

theorem theta_alt_s43 (i : ℕ) (hi : i ≤ 4*3) :
    0 < (-1:ℚ)^i * ((Wnd (pa 4 (1-(4:ℤ))) 3).a).eval (altpt 4 3 i) :=
  theta_alt_small 4 3 i hi (by decide +kernel)

theorem theta_alt_s54 (i : ℕ) (hi : i ≤ 4*4) :
    0 < (-1:ℚ)^i * ((Wnd (pa 5 (1-(5:ℤ))) 4).a).eval (altpt 5 4 i) :=
  theta_alt_small 5 4 i hi (by decide +kernel)

theorem theta_alt_s11 (i : ℕ) (hi : i ≤ 4*1) :
    0 < (-1:ℚ)^i * ((Wnd (pa 1 (1-(1:ℤ))) 1).a).eval (altpt 1 1 i) :=
  theta_alt_small 1 1 i hi (by decide +kernel)

theorem theta_alt_s23 (i : ℕ) (hi : i ≤ 4*3) :
    0 < (-1:ℚ)^i * ((Wnd (pa 2 (1-(2:ℤ))) 3).a).eval (altpt 2 3 i) :=
  theta_alt_small 2 3 i hi (by decide +kernel)

theorem altpt_mono_s (m len : ℕ) (hm : 1 ≤ m) (hml : len ≤ 4) (hl : 1 ≤ len)
    (i : ℕ) (hi : i + 1 ≤ 4*len) : altpt m len i < altpt m len (i+1) := by
  have hm' : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  unfold altpt
  rw [div_lt_div_iff_of_pos_right hm']
  have key : ∀ len : ℕ, len ≤ 4 → ∀ i : ℕ, i < 4*len →
      (altu len i : ℚ) + altd len i < (altu len (i+1) : ℚ) + altd len (i+1) := by
    decide +kernel
  have := key len hml i (by omega)
  linarith

end SmallSign

/-! ## Uniform dispatch -/

theorem theta_alt_all (m len : ℕ) (hm : 1 ≤ m)
    (hlen : (len = m-1 ∧ 2 ≤ m) ∨ len = 2*m-1) :
    (∀ i, i ≤ 4*len →
      0 < (-1:ℚ)^i * ((Wnd (pa m (1-(m:ℤ))) len).a).eval (altpt m len i)) ∧
    (∀ i, i + 1 ≤ 4*len → altpt m len i < altpt m len (i+1)) := by
  by_cases h5 : 5 ≤ len
  · exact ⟨fun i hi => theta_alt m len hm h5 i hi,
      fun i hi => altpt_mono m len hm h5 i hi⟩
  · rcases hlen with ⟨hl, hm2⟩ | hl
    · have hm5 : m ≤ 5 := by omega
      subst hl
      interval_cases m
      · exact ⟨fun i hi => theta_alt_s21 i hi,
          fun i hi => altpt_mono_s 2 1 (by omega) (by omega) (by omega) i hi⟩
      · exact ⟨fun i hi => theta_alt_s32 i hi,
          fun i hi => altpt_mono_s 3 2 (by omega) (by omega) (by omega) i hi⟩
      · exact ⟨fun i hi => theta_alt_s43 i hi,
          fun i hi => altpt_mono_s 4 3 (by omega) (by omega) (by omega) i hi⟩
      · exact ⟨fun i hi => theta_alt_s54 i hi,
          fun i hi => altpt_mono_s 5 4 (by omega) (by omega) (by omega) i hi⟩
    · have hm2 : m ≤ 2 := by omega
      subst hl
      interval_cases m
      · exact ⟨fun i hi => theta_alt_s11 i hi,
          fun i hi => altpt_mono_s 1 1 (by omega) (by omega) (by omega) i hi⟩
      · exact ⟨fun i hi => theta_alt_s23 i hi,
          fun i hi => altpt_mono_s 2 3 (by omega) (by omega) (by omega) i hi⟩

/-! ## Endpoint values -/

lemma altpt_first (m len : ℕ) : altpt m len 0 = ((m:ℚ)-1-len+3/20)/m := by
  unfold altpt
  rw [altu_head len 0 (by omega), altd_0]
  norm_num

lemma altpt_last (m len : ℕ) (hl : 1 ≤ len) :
    altpt m len (4*len) = ((m:ℚ)-1+17/20)/m := by
  unfold altpt
  rw [altu_tail len (4*len) (by omega) hl, altd_tail0 len hl]
  ring_nf

end Bala

-- ===== Dev.RootsFinal =====
/-!
# Root localisation for `P(2m,·)` and `Q(2m,·)`
-/

namespace Bala

open Polynomial

/-- The master localisation: all complex roots of the window numerator are
real, strictly between the first and last test point. -/
lemma theta_complex_roots (m len : ℕ) (hm : 1 ≤ m)
    (hlen : (len = m-1 ∧ 2 ≤ m) ∨ len = 2*m-1) (hl1 : 1 ≤ len) :
    ∀ z : ℂ,
      ((((Wnd (pa m (1-(m:ℤ))) len).a.map (algebraMap ℚ ℝ)).map
        (algebraMap ℝ ℂ)).eval z = 0) →
      z.im = 0 ∧ ((altpt m len 0 : ℚ):ℝ) < z.re ∧
        z.re < ((altpt m len (4*len) : ℚ):ℝ) := by
  obtain ⟨hsign, hmono⟩ := theta_alt_all m len hm hlen
  have hc : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hdeg := Wnd_deg (pa m (1-(m:ℤ))) (pa_natDegree_le m _) m hc (pa_coeff_one m _) len
  have hndeg : (Wnd (pa m (1-(m:ℤ))) len).a.natDegree = 4*len :=
    natDegree_eq_of_le_of_coeff_ne_zero hdeg.1 (ne_of_gt hdeg.2.1)
  set f : ℝ[X] := (Wnd (pa m (1-(m:ℤ))) len).a.map (algebraMap ℚ ℝ) with hf
  have hfdeg : f.natDegree = 4*len := by
    rw [hf, natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective, hndeg]
  exact complex_roots_of_alternation f (4*len) hfdeg (by omega)
    (fun i => ((altpt m len i : ℚ):ℝ))
    (fun i hi => by
      show ((altpt m len i : ℚ):ℝ) < ((altpt m len (i+1) : ℚ):ℝ)
      exact_mod_cast hmono i hi)
    (fun i hi => by
      show 0 < (-1:ℝ)^i * f.eval ((altpt m len i : ℚ):ℝ)
      have h := hsign i hi
      have heq : ((((-1:ℚ))^i * ((Wnd (pa m (1-(m:ℤ))) len).a).eval (altpt m len i) : ℚ):ℝ)
          = (-1:ℝ)^i * f.eval ((altpt m len i : ℚ):ℝ) := by
        rw [hf, map_eval_rat]
        push_cast
        ring
      rw [← heq]
      exact_mod_cast h)

/-- All complex roots of `P` lie in `[0,1]` (in fact in `(0,1)`), `m ≥ 2`. -/
theorem P_roots (m : ℕ) (hm : 2 ≤ m) :
    ∀ z : ℂ, ((PR m).map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (0:ℝ) 1 := by
  intro z hz
  have hm1 : 1 ≤ m := by omega
  have hm' : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  -- z is a root of the full window numerator
  have htheta : ((((ThetaLow m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).eval z) = 0 := by
    have hspec := Pq_spec m
    have : ((ThetaLow m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)
        = (((contL m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ))
          * ((PR m).map (algebraMap ℝ ℂ)) := by
      rw [hspec, Polynomial.map_mul, Polynomial.map_mul, PR]
    rw [this, eval_mul, hz, mul_zero]
  have hcore := theta_complex_roots m (m-1) hm1 (Or.inl ⟨rfl, hm⟩) (by omega) z
    (by exact htheta)
  refine ⟨hcore.1, ?_, ?_⟩
  · -- 0 ≤ z.re
    have h0 : (0:ℝ) ≤ ((altpt m (m-1) 0 : ℚ):ℝ) := by
      have : (0:ℚ) ≤ altpt m (m-1) 0 := by
        rw [altpt_first]
        have hcast : ((m-1:ℕ):ℚ) = (m:ℚ) - 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
          ring
        rw [hcast]
        have hnum : (m:ℚ)-1-((m:ℚ)-1)+3/20 = 3/20 := by ring
        rw [hnum]
        positivity
      exact_mod_cast this
    linarith [hcore.2.1]
  · -- z.re ≤ 1
    have h1 : ((altpt m (m-1) (4*(m-1)) : ℚ):ℝ) ≤ 1 := by
      have : altpt m (m-1) (4*(m-1)) ≤ 1 := by
        rw [altpt_last m (m-1) (by omega)]
        rw [div_le_one hm']
        linarith
      exact_mod_cast this
    linarith [hcore.2.2]

/-- All complex roots of `Q(·²)` lie in `[-1,1]`, `m ≥ 1`. -/
theorem Q_roots (m : ℕ) (hm : 1 ≤ m) :
    ∀ z : ℂ, ((QR m).map (algebraMap ℝ ℂ)).eval (z^2) = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (-1:ℝ) 1 := by
  intro z hz
  have hm' : (0:ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  -- z is a root of Qhat over ℂ
  have hQhat : ((((Qhat m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).eval z) = 0 := by
    have hcomp := Qsmall_comp m hm
    have : ((Qhat m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)
        = ((QR m).map (algebraMap ℝ ℂ)).comp (X^2) := by
      rw [← hcomp, Polynomial.map_comp, Polynomial.map_comp, QR]
      simp
    rw [this, eval_comp]
    simpa using hz
  have htheta : ((((ThetaHat m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).eval z) = 0 := by
    have hspec := Qhat_spec m
    have : ((ThetaHat m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)
        = (((contH m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ))
          * (((Qhat m).map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)) := by
      rw [hspec, Polynomial.map_mul, Polynomial.map_mul]
    rw [this, eval_mul, hQhat, mul_zero]
  have hcore := theta_complex_roots m (2*m-1) hm (Or.inr rfl) (by omega) z
    (by exact htheta)
  refine ⟨hcore.1, ?_, ?_⟩
  · -- -1 ≤ z.re
    have h0 : (-1:ℝ) ≤ ((altpt m (2*m-1) 0 : ℚ):ℝ) := by
      have : (-1:ℚ) ≤ altpt m (2*m-1) 0 := by
        rw [altpt_first]
        have hcast : ((2*m-1:ℕ):ℚ) = 2*(m:ℚ) - 1 := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ 2*m)]
          ring
        rw [hcast]
        rw [le_div_iff₀ hm']
        linarith
      exact_mod_cast this
    linarith [hcore.2.1]
  · have h1 : ((altpt m (2*m-1) (4*(2*m-1)) : ℚ):ℝ) ≤ 1 := by
      have : altpt m (2*m-1) (4*(2*m-1)) ≤ 1 := by
        rw [altpt_last m (2*m-1) (by omega)]
        rw [div_le_one hm']
        linarith
      exact_mod_cast this
    linarith [hcore.2.2]

end Bala

-- ===== Dev.Final =====
/-!
# Final ingredients: degrees, symmetry, and the case `m = 1`
-/

namespace Bala

open Polynomial

/-! ## Degrees and symmetry over `ℝ` -/

lemma PR_ne_zero (m : ℕ) (hm : 1 ≤ m) : PR m ≠ 0 := by
  rw [PR]
  intro h
  exact Pq_ne_zero m hm (Polynomial.map_injective _ (algebraMap ℚ ℝ).injective
    (by rwa [Polynomial.map_zero]))

lemma QR_ne_zero (m : ℕ) (hm : 1 ≤ m) : QR m ≠ 0 := by
  rw [QR]
  intro h
  exact Qsmall_ne_zero m hm (Polynomial.map_injective _ (algebraMap ℚ ℝ).injective
    (by rwa [Polynomial.map_zero]))

theorem PR_degree (m : ℕ) (hm : 2 ≤ m) : (PR m).degree = (2*m : ℕ) := by
  rw [degree_eq_natDegree (PR_ne_zero m (by omega)), PR,
    natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective, Pq_natDegree m hm]

theorem QR_degree (m : ℕ) (hm : 1 ≤ m) : (QR m).degree = (2*m : ℕ) := by
  rw [degree_eq_natDegree (QR_ne_zero m hm), QR,
    natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective, Qsmall_natDegree m hm]

theorem PR_symm (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (PR m).eval x = (PR m).eval (1 - x) := by
  have h := Pq_comp_reflect m hm
  have hmap := congrArg (Polynomial.map (algebraMap ℚ ℝ)) h
  rw [Polynomial.map_comp] at hmap
  have h1 : (1 - X : ℚ[X]).map (algebraMap ℚ ℝ) = 1 - X := by
    simp
  rw [h1] at hmap
  have := congrArg (Polynomial.eval x) hmap
  rw [eval_comp] at this
  simp only [eval_sub, eval_one, eval_X] at this
  rw [PR]
  exact this.symm

/-! ## The case `m = 1` -/

/-- `P(2,·)` over `ℝ`. -/
noncomputable def P1R : ℝ[X] := p1 (X : ℝ[X])

lemma P1R_natDegree : P1R.natDegree = 2 := by
  have h : P1R = C 5 * X^2 + C (-5) * X + C 1 := by
    simp only [P1R, p1, Polynomial.C_neg, map_ofNat, Polynomial.C_1]
    ring
  rw [h, Polynomial.natDegree_quadratic (by norm_num)]

lemma P1R_ne_zero : P1R ≠ 0 := by
  intro h
  have := P1R_natDegree
  rw [h] at this
  simp at this

theorem P1R_degree : P1R.degree = (2 : ℕ) := by
  rw [degree_eq_natDegree P1R_ne_zero, P1R_natDegree]

theorem P1R_symm (x : ℝ) : P1R.eval x = P1R.eval (1 - x) := by
  simp only [P1R, eval_p1, eval_X]
  rw [p1_one_sub]

theorem P1R_roots :
    ∀ z : ℂ, (P1R.map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (0:ℝ) 1 := by
  intro z hz
  have hx := complex_roots_of_alternation P1R 2 P1R_natDegree (by omega)
    (fun i : ℕ => if i = 0 then (0:ℝ) else if i = 1 then 1/2 else 1)
    (fun i hi => by
      have h2 : i ≤ 1 := by omega
      interval_cases i <;> norm_num)
    (fun i hi => by
      have h2 : i ≤ 2 := hi
      interval_cases i <;> norm_num [P1R, p1])
    z hz
  obtain ⟨h1, h2, h3⟩ := hx
  norm_num at h2 h3
  rw [Set.mem_Icc]
  exact ⟨h1, le_of_lt h2, le_of_lt h3⟩

lemma contH_one : contH 1 = 1 := by
  unfold contH
  norm_num

lemma Qhat_one : Qhat 1 = ThetaHat 1 := by
  have h := Qhat_spec 1
  rw [contH_one, one_mul] at h
  exact h.symm

lemma Qhat_one_eval (t : ℚ) : (Qhat 1).eval t = -(c0 t) := by
  rw [Qhat_one]
  unfold ThetaHat
  rw [show (2*1-1 : ℕ) = 1 from rfl, Wnd_one, Mstep_a]
  simp only [eval_neg, eval_c0, pa_eval]
  congr 2
  push_cast
  ring

/-- The scalar recurrence for `m = 1` over `ℚ`. -/
lemma scalar_rec_m1 (n : ℕ) (hn : 1 ≤ n) :
    ((2*(n:ℚ)+1)*(2*(n:ℚ)+2)) * (p1 (n:ℚ)) * aq (n+1)
      + (-1) * (((2*(n:ℚ)-1)*(2*(n:ℚ)-2)) * (p1 (-(n:ℚ)))) * aq (n-1)
      = (Qhat 1).eval (n:ℚ) * aq n := by
  have h := base_rec n hn
  rw [Qhat_one_eval]
  simp only [cP, c0, cM, p1] at *
  linear_combination h

/-- The real recurrence for `m = 1`. -/
theorem real_rec_m1 (n : ℕ) (hn : 1 ≤ n) :
    ((∏ k ∈ Finset.Ioc (0:ℕ) (2*1), ((2*(1:ℝ)*(n:ℝ)) + (k:ℝ))) * P1R.eval ((n:ℝ)))
        * (A103885 (1*(n+1)) : ℝ)
      + ((-1:ℝ)^1 * (∏ k ∈ Finset.Ioc (0:ℕ) (2*1), ((2*(1:ℝ)*(n:ℝ)) - (k:ℝ)))
          * P1R.eval (-(n:ℝ))) * (A103885 (1*(n-1)) : ℝ)
      = (QR 1).eval ((n:ℝ)^2) * (A103885 (1*n) : ℝ) := by
  have hs := scalar_rec_m1 n hn
  have hcast := congrArg (fun x : ℚ => (x : ℝ)) hs
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_neg, Rat.cast_one] at hcast
  have haq : ∀ k : ℕ, ((aq k : ℚ) : ℝ) = (A103885 k : ℝ) := by
    intro k
    simp [aq]
  rw [haq, haq, haq] at hcast
  have hQ : (((Qhat 1).eval (n:ℚ) : ℚ) : ℝ) = (QR 1).eval ((n:ℝ)^2) := by
    rw [← Qsmall_comp 1 (by omega), eval_comp, eval_pow, eval_X,
      show ((n:ℝ)^2) = ((((n:ℚ)^2):ℚ):ℝ) from by push_cast; ring, QR, map_eval_rat]
  rw [hQ] at hcast
  have hp1 : ∀ t : ℚ, ((p1 t : ℚ) : ℝ) = P1R.eval ((t:ℚ):ℝ) := by
    intro t
    rw [P1R, show ((t:ℚ):ℝ) = algebraMap ℚ ℝ t from by simp]
    simp only [p1]
    push_cast
    simp [eval_p1]
  have hP1 : ((p1 ((n:ℚ)) : ℚ) : ℝ) = P1R.eval ((n:ℝ)) := by
    rw [hp1]
    norm_num
  have hP2 : ((p1 (-(n:ℚ)) : ℚ) : ℝ) = P1R.eval (-(n:ℝ)) := by
    rw [hp1]
    norm_num
  rw [hP1, hP2] at hcast
  have hIoc : Finset.Ioc (0:ℕ) (2*1) = {1, 2} := by decide
  rw [hIoc, Finset.prod_insert (by norm_num), Finset.prod_singleton,
    Finset.prod_insert (by norm_num), Finset.prod_singleton]
  simp only [Nat.one_mul, pow_one]
  push_cast at hcast ⊢
  linear_combination hcast

end Bala

/--
The recurrence given below can be rewritten in the form
(2*n+1)*(2*n+2)*P(2,n)*a(n+1) - (2*n-1)*(2*n-2)*P(2,-n)*a(n-1) = Q(2,n^2)*a(n), where the polynomial Q(2,n) = 4*(55*n^2 - 34*n + 3) and the polynomial P(2,n) = 5*n^2 - 5*n + 1 satisfies the symmetry condition P(2,n) = P(2,1-n) and has real zeros.
More generally, for fixed m = 1,2,3,..., we conjecture that the sequence b(n) := a(m*n) satisfies a recurrence of the form ( Product_{k = 1..2*m} (2*m*n + k) ) * P(2*m,n)*b(n+1) + (-1)^m*( Product_{k = 1..2*m} (2*m*n - k) ) * P(2*m,-n)*b(n-1) = Q(2*m,n^2)*b(n), where the polynomials P(2*m,n) and Q(2*m,n) have degree 2*m. Conjecturally, the polynomial P(2*m,n) = P(2*m,1-n) and has real zeros in the interval [0, 1]. The 4*m zeros of the polynomial Q(2*m,n^2) seem to belong to the interval [-1, 1] and 4*m - 2 of these zeros appear to be approximated by the rational numbers +- k/(3*m), where 1 <= k <= 3*m - 2, k not a multiple of 3.
-/
theorem oeis_a103885_conjecture_0 (m : ℕ) (hm : 1 ≤ m) :
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
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) :=
    by
  have hAB : ∀ k : ℕ, ((Bala.A103885 k : ℕ) : ℝ) = ((A103885 k : ℕ) : ℝ) := fun _ => rfl
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · -- m = 1
    have hm1 : m = 1 := by omega
    subst hm1
    refine ⟨Bala.P1R, Bala.QR 1, by simpa using Bala.P1R_degree,
      by simpa using Bala.QR_degree 1 (by omega), ?_, fun x => Bala.P1R_symm x,
      Bala.P1R_roots, Bala.Q_roots 1 (by omega)⟩
    intro n hn
    have h := Bala.real_rec_m1 n hn
    simp only [hAB] at h
    simp only [prod_factor_plus, prod_factor_minus, product_indices,
      A103885_subsequence_real]
    push_cast at h ⊢
    linear_combination h
  · -- m ≥ 2
    refine ⟨Bala.PR m, Bala.QR m, Bala.PR_degree m hm2, Bala.QR_degree m (by omega),
      ?_, fun x => Bala.PR_symm m (by omega) x, Bala.P_roots m hm2,
      Bala.Q_roots m (by omega)⟩
    intro n hn
    have h := Bala.real_rec m n hm2 hn
    simp only [hAB] at h
    simp only [prod_factor_plus, prod_factor_minus, product_indices,
      A103885_subsequence_real]
    push_cast at h ⊢
    linear_combination h

