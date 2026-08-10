import FormalConjectures.Util.ProblemImports

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det




/- Helpers from DetCrit.lean -/

open Matrix Finset
open scoped Matrix

namespace DetCrit

variable {K : Type*} [Field K]

/-- The row-indexed matrix from the Legendre determinant criterion, in positive size. -/
def D (n : ℕ) (z : Fin (n + 1) → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => if i = 0 then 1 + z j ^ (n + 1) else z j ^ (i : ℕ)

/-- The transpose of `D` is a Vandermonde matrix with column `0` replaced by
`1 + z^(n+1)`. -/
lemma D_transpose_eq_updateCol (n : ℕ) (z : Fin (n + 1) → K) :
    (D n z)ᵀ = (Matrix.vandermonde z).updateCol 0 (fun j => 1 + z j ^ (n + 1)) := by
  ext i j
  by_cases hj : j = 0
  · subst hj
    simp [D, Matrix.vandermonde]
  · simp [D, Matrix.vandermonde, hj]

/-- The determinant contribution obtained by replacing the constant Vandermonde
column by `z^(n+1)`. -/
lemma det_updateCol_zero_pow (n : ℕ) (z : Fin (n + 1) → K) :
    ((Matrix.vandermonde z).updateCol 0 (fun j => z j ^ (n + 1))).det =
      (-1 : K) ^ n * (∏ j, z j) * (Matrix.vandermonde z).det := by
  let V : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.vandermonde z
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    Matrix.of fun i j => z i * V i ((finRotate (n + 1)).symm j)
  have h_update : V.updateCol 0 (fun j => z j ^ (n + 1)) = B := by
    ext i j
    by_cases hj : j = 0
    · subst hj
      simp [V, B, Matrix.vandermonde, _root_.pow_succ']
    · have hjpos : 0 < (j : ℕ) := Fin.pos_iff_ne_zero.mpr hj
      simp [V, B, Matrix.vandermonde, hj]
      rw [← Nat.succ_pred_eq_of_pos hjpos, _root_.pow_succ']
      rw [Nat.pred_eq_sub_one]
      rw [Fin.val_sub_one_of_ne_zero hj]


  calc
    (V.updateCol 0 (fun j => z j ^ (n + 1))).det = B.det := by rw [h_update]
    _ = (∏ j, z j) * (V.submatrix id (finRotate (n + 1)).symm).det := by
      rw [show B = Matrix.of (fun i j => z i * (V.submatrix id (finRotate (n + 1)).symm) i j) by
        ext i j
        rfl]
      rw [Matrix.det_mul_column]
    _ = (∏ j, z j) * ((Equiv.Perm.sign (finRotate (n + 1)).symm : K) * V.det) := by
      rw [Matrix.det_permute']
    _ = (-1 : K) ^ n * (∏ j, z j) * V.det := by
      rw [Equiv.Perm.sign_symm, sign_finRotate]
      norm_num
      ring

/-- Determinant formula for `D`: transpose, update column additivity, and the
cyclic column permutation of the high-power column. -/
theorem det_D (n : ℕ) (z : Fin (n + 1) → K) :
    (D n z).det =
      (1 - (-1 : K) ^ (n + 1) * (∏ j, z j)) * (Matrix.vandermonde z).det := by
  let V : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.vandermonde z
  have hcol : (fun j : Fin (n + 1) => 1 + z j ^ (n + 1)) =
      (fun j => V j 0) + fun j => z j ^ (n + 1) := by
    ext j
    simp [V, Matrix.vandermonde]
  calc
    (D n z).det = ((D n z)ᵀ).det := by rw [Matrix.det_transpose]
    _ = (V.updateCol 0 (fun j => 1 + z j ^ (n + 1))).det := by
      rw [D_transpose_eq_updateCol]
    _ = (V.updateCol 0 ((fun j => V j 0) + fun j => z j ^ (n + 1))).det := by
      rw [← hcol]
    _ = (V.updateCol 0 (fun j => V j 0)).det +
          (V.updateCol 0 (fun j => z j ^ (n + 1))).det := by
      rw [Matrix.det_updateCol_add]
    _ = V.det + (-1 : K) ^ n * (∏ j, z j) * V.det := by
      rw [Matrix.updateCol_eq_self, det_updateCol_zero_pow]
    _ = (1 - (-1 : K) ^ (n + 1) * (∏ j, z j)) * V.det := by
      ring

/-- Nonvanishing corollary under injectivity and nonvanishing of the explicit
extra factor. -/
theorem det_D_ne_zero (n : ℕ) {z : Fin (n + 1) → K}
    (hz : Function.Injective z)
    (hfac : 1 - (-1 : K) ^ (n + 1) * (∏ j, z j) ≠ 0) :
    (D n z).det ≠ 0 := by
  rw [det_D]
  exact mul_ne_zero hfac ((Matrix.det_vandermonde_ne_zero_iff).2 hz)

/-- Same matrix, indexed by a positive size `n`. The zero-size version of the
closed formula is false, so the `[NeZero n]` hypothesis is necessary. -/
def Dpos (n : ℕ) [NeZero n] (z : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = 0 then 1 + z j ^ n else z j ^ (i : ℕ)

/-- Positive-size version stated with `Fin n`. -/
theorem det_Dpos (n : ℕ) [NeZero n] (z : Fin n → K) :
    (Dpos n z).det =
      (1 - (-1 : K) ^ n * (∏ j, z j)) * (Matrix.vandermonde z).det := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact det_D m z

/-- Positive-size nonvanishing version stated with `Fin n`. -/
theorem det_Dpos_ne_zero (n : ℕ) [NeZero n] {z : Fin n → K}
    (hz : Function.Injective z)
    (hfac : 1 - (-1 : K) ^ n * (∏ j, z j) ≠ 0) :
    (Dpos n z).det ≠ 0 := by
  rw [det_Dpos]
  exact mul_ne_zero hfac ((Matrix.det_vandermonde_ne_zero_iff).2 hz)



end DetCrit


/- Helpers from BinomScalar.lean -/

open Finset
open BigOperators

namespace BinomScalar

variable {K : Type*} [Field K]

/-- A scalar binomial identity factoring out a nonzero scalar.  The final
summand in the binomial expansion is folded into the `k = 0` summand, using
`x ^ m = 1`. -/
theorem binomScalar {m : ℕ} (hm : 0 < m) {x y : K} (hy : y ≠ 0) (hx : x ^ m = 1) :
    (x + y) ^ m =
      (∑ k : Fin m,
        if (k : ℕ) = 0 then 1 + y⁻¹ ^ m
        else x ^ (k : ℕ) * (m.choose (k : ℕ) : K) * y⁻¹ ^ (k : ℕ)) * y ^ m := by
  have hxy : x + y = (x * y⁻¹ + 1) * y := by
    field_simp [hy]
  calc
    (x + y) ^ m = ((x * y⁻¹ + 1) * y) ^ m := by rw [hxy]
    _ = (x * y⁻¹ + 1) ^ m * y ^ m := by rw [mul_pow]
    _ = (∑ k ∈ range (m + 1), (x * y⁻¹) ^ k * 1 ^ (m - k) * (m.choose k : K)) * y ^ m := by
      rw [add_pow]
    _ = (∑ k ∈ range (m + 1), x ^ k * (m.choose k : K) * y⁻¹ ^ k) * y ^ m := by
      congr 1
      apply sum_congr rfl
      intro k hk
      rw [one_pow, mul_one, mul_pow]
      ring
    _ = (∑ k : Fin m,
        if (k : ℕ) = 0 then 1 + y⁻¹ ^ m
        else x ^ (k : ℕ) * (m.choose (k : ℕ) : K) * y⁻¹ ^ (k : ℕ)) * y ^ m := by
      congr 1
      rcases m with _ | n
      · cases hm
      · rw [Fin.sum_univ_eq_sum_range
            (fun k : ℕ =>
              if k = 0 then 1 + y⁻¹ ^ (n + 1)
              else x ^ k * ((n + 1).choose k : K) * y⁻¹ ^ k) (n + 1)]
        rw [sum_range_succ]
        rw [sum_range_succ']
        rw [sum_range_succ'
          (fun k : ℕ =>
            if k = 0 then 1 + y⁻¹ ^ (n + 1)
            else x ^ k * ((n + 1).choose k : K) * y⁻¹ ^ k) n]

        simp [hx, pow_succ, mul_assoc]
        ac_rfl


end BinomScalar


/- Helpers from TmpDet.lean -/

open Matrix Finset
open scoped Matrix BigOperators

namespace TmpDet

lemma zmod_natCast_choose_ne_zero {p m k : ℕ} (hp : p.Prime) (hm : m < p) (hk : k ≤ m) :
    ((m.choose k : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact (hp.coprime_iff_not_dvd.mp (hp.coprime_choose_of_lt hm hk))

lemma inv_neg_injective_of_injective {K : Type*} [Field K] {n : ℕ} {b : Fin n → K}
    (hb : Function.Injective b) : Function.Injective (fun j => (-b j)⁻¹) := by
  intro i j h
  apply hb
  apply neg_injective
  exact inv_injective h

lemma prod_inv_neg_eq {K : Type*} [Field K] {n : ℕ} (b : Fin n → K) :
    (∏ j, (-b j)⁻¹) = ((-1 : K) ^ n * ∏ j, b j)⁻¹ := by
  calc
    (∏ j, (-b j)⁻¹) = (∏ j, (-b j))⁻¹ := by
      simpa using (Finset.prod_inv_distrib (s := (Finset.univ : Finset (Fin n))) (fun j => -b j))
    _ = ((-1 : K) ^ n * ∏ j, b j)⁻¹ := by
      congr 1
      rw [show (fun j : Fin n => -b j) = (fun j => (-1 : K) * b j) by
        ext j
        exact neg_eq_neg_one_mul (b j)]
      rw [Finset.prod_mul_distrib]
      simp

lemma det_Dpos_factor_ne_zero_from_prod {K : Type*} [Field K] {n : ℕ} [NeZero n] {b : Fin n → K}
    (hb0 : ∀ j, b j ≠ 0) (hprod : ∏ j, b j ≠ 1) :
    1 - (-1 : K) ^ n * (∏ j, (-b j)⁻¹) ≠ 0 := by
  rw [prod_inv_neg_eq]
  have hpb : (∏ j, b j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact hb0 j
  intro h
  let a : K := (-1 : K) ^ n
  let P : K := ∏ j, b j
  have ha : a ≠ 0 := by
    dsimp [a]
    exact pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)
  have hap : a * P ≠ 0 := mul_ne_zero ha hpb
  have hm : a * (a * P)⁻¹ = 1 := by
    change 1 - a * (a * P)⁻¹ = 0 at h
    rw [sub_eq_zero] at h
    exact h.symm
  have heq : a = a * P := by
    calc
      a = a * 1 := by rw [mul_one]
      _ = a * ((a * P)⁻¹ * (a * P)) := by rw [inv_mul_cancel₀ hap]
      _ = (a * (a * P)⁻¹) * (a * P) := by ring
      _ = 1 * (a * P) := by rw [hm]
      _ = a * P := by rw [one_mul]
  have hP : P = 1 := by
    exact (mul_left_cancel₀ ha (by simpa [mul_one] using heq)).symm
  exact hprod (by simpa [P] using hP)

lemma det_Dpos_inv_neg_b_ne_zero {K : Type*} [Field K] {n : ℕ} [NeZero n] {b : Fin n → K}
    (hb0 : ∀ j, b j ≠ 0) (hbinj : Function.Injective b) (hprod : ∏ j, b j ≠ 1) :
    (DetCrit.Dpos n (fun j : Fin n => (-b j)⁻¹)).det ≠ 0 := by
  exact DetCrit.det_Dpos_ne_zero n
    (z := fun j : Fin n => (-b j)⁻¹)
    (inv_neg_injective_of_injective hbinj)
    (det_Dpos_factor_ne_zero_from_prod hb0 hprod)


lemma det_factorized_matrix_ne_zero {p m : ℕ} [Fact p.Prime] [NeZero m]
    (hm : m < p) {b x : Fin m → ZMod p}
    (hb0 : ∀ j, b j ≠ 0) (hbinj : Function.Injective b)
    (hxinj : Function.Injective x) (hprod : ∏ j, b j ≠ 1) :
    ((Matrix.vandermonde x) *
        (Matrix.diagonal (fun k : Fin m => if k = (0 : Fin m) then (1 : ZMod p) else (m.choose (k : ℕ) : ZMod p))) *
        (DetCrit.Dpos m (fun j : Fin m => (-b j)⁻¹)) *
        (Matrix.diagonal (fun j : Fin m => (-b j) ^ m))).det ≠ 0 := by
  let coeff : Fin m → ZMod p := fun k => if k = 0 then (1 : ZMod p) else (m.choose (k : ℕ) : ZMod p)
  let z : Fin m → ZMod p := fun j => (-b j)⁻¹
  let col : Fin m → ZMod p := fun j => (-b j) ^ m
  have hp : p.Prime := Fact.out
  have hV : (Matrix.vandermonde x).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff).2 hxinj
  have hC : (Matrix.diagonal coeff).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k hkmem
    by_cases hk0 : k = 0
    · simp [coeff, hk0]
    · have hk_le : (k : ℕ) ≤ m := le_of_lt k.isLt
      simp [coeff, hk0, zmod_natCast_choose_ne_zero hp hm hk_le]
  have hD : (DetCrit.Dpos m z).det ≠ 0 := by
    exact DetCrit.det_Dpos_ne_zero m (z := z)
      (inv_neg_injective_of_injective hbinj)
      (by
        dsimp [z]
        exact det_Dpos_factor_ne_zero_from_prod hb0 hprod)
  have hCol : (Matrix.diagonal col).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro j hjmem
    exact pow_ne_zero m (neg_ne_zero.mpr (hb0 j))
  dsimp [coeff, z, col] at hC hD hCol ⊢
  repeat rw [Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hV hC) hD) hCol

end TmpDet

namespace TmpDet

lemma half_pred_lt_of_prime {p : ℕ} (hp : p.Prime) : (p - 1) / 2 < p := by
  have hp0 : 0 < p := hp.pos
  have hle : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  have hlt : p - 1 < p := Nat.sub_lt hp0 zero_lt_one
  exact lt_of_le_of_lt hle hlt

lemma det_factorized_matrix_ne_zero_half {p : ℕ} [Fact p.Prime] [NeZero ((p - 1) / 2)]
    {b x : Fin ((p - 1) / 2) → ZMod p}
    (hb0 : ∀ j, b j ≠ 0) (hbinj : Function.Injective b)
    (hxinj : Function.Injective x) (hprod : ∏ j, b j ≠ 1) :
    ((Matrix.vandermonde x) *
        (Matrix.diagonal (fun k : Fin ((p - 1) / 2) =>
          if k = 0 then (1 : ZMod p) else (((p - 1) / 2).choose (k : ℕ) : ZMod p))) *
        (DetCrit.Dpos ((p - 1) / 2) (fun j : Fin ((p - 1) / 2) => (-b j)⁻¹)) *
        (Matrix.diagonal (fun j : Fin ((p - 1) / 2) => (-b j) ^ ((p - 1) / 2)))).det ≠ 0 := by
  exact det_factorized_matrix_ne_zero (p := p) (m := (p - 1) / 2)
    (half_pred_lt_of_prime (Fact.out : p.Prime)) hb0 hbinj hxinj hprod

end TmpDet

namespace TmpDet

def legendreMatrix (p m : ℕ) (b x : Fin m → ZMod p) : Matrix (Fin m) (Fin m) (ZMod p) :=
  fun i j => (x i - b j) ^ m

def factorMatrix (p m : ℕ) [Fact p.Prime] [NeZero m] (b x : Fin m → ZMod p) : Matrix (Fin m) (Fin m) (ZMod p) :=
  ((Matrix.vandermonde x) *
    (Matrix.diagonal (fun k : Fin m => if k = (0 : Fin m) then (1 : ZMod p) else (m.choose (k : ℕ) : ZMod p))) *
    (DetCrit.Dpos m (fun j : Fin m => (-b j)⁻¹))) *
    (Matrix.diagonal (fun j : Fin m => (-b j) ^ m))

lemma matrix_mul_diagonal_apply {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    (M : Matrix n n R) (d : n → R) (i j : n) :
    (M * Matrix.diagonal d) i j = M i j * d j := by
  classical
  rw [Matrix.mul_apply]
  simp [Matrix.diagonal]

lemma factorMatrix_apply {p m : ℕ} [Fact p.Prime] [NeZero m]
    (b x : Fin m → ZMod p) (i j : Fin m) :
    factorMatrix p m b x i j =
      (∑ k : Fin m,
        if (k : ℕ) = 0 then 1 + ((-b j)⁻¹) ^ m
        else x i ^ (k : ℕ) * (m.choose (k : ℕ) : ZMod p) * ((-b j)⁻¹) ^ (k : ℕ)) *
        (-b j) ^ m := by
  classical
  unfold factorMatrix
  rw [matrix_mul_diagonal_apply]
  rw [Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [matrix_mul_diagonal_apply]
  by_cases hk0 : k = (0 : Fin m)
  · subst hk0
    simp [Matrix.vandermonde, DetCrit.Dpos]
  · have hknat : (k : ℕ) ≠ 0 := by
      intro h
      exact hk0 (Fin.ext h)
    simp [Matrix.vandermonde, DetCrit.Dpos, hk0, hknat, mul_assoc]


lemma legendre_det_ne_zero_of_factorization {p m : ℕ} [Fact p.Prime] [NeZero m]
    (hm : m < p) {b x : Fin m → ZMod p}
    (hb0 : ∀ j, b j ≠ 0) (hbinj : Function.Injective b)
    (hxinj : Function.Injective x) (hprod : ∏ j, b j ≠ 1)
    (hfactor : legendreMatrix p m b x = factorMatrix p m b x) :
    (legendreMatrix p m b x).det ≠ 0 := by
  rw [hfactor]
  dsimp [factorMatrix]
  exact det_factorized_matrix_ne_zero (p := p) (m := m) hm hb0 hbinj hxinj hprod

end TmpDet

namespace TmpDet

lemma factorization_of_pow_eq_one {p m : ℕ} [Fact p.Prime] [NeZero m]
    {b x : Fin m → ZMod p} (hb0 : ∀ j, b j ≠ 0) (hxpow : ∀ i, x i ^ m = 1) :
    legendreMatrix p m b x = factorMatrix p m b x := by
  ext i j
  have hy : -b j ≠ 0 := neg_ne_zero.mpr (hb0 j)
  have h := BinomScalar.binomScalar (K := ZMod p) (m := m) (NeZero.pos m)
    (x := x i) (y := -b j) hy (hxpow i)
  simpa [legendreMatrix, factorMatrix_apply, sub_eq_add_neg] using h


end TmpDet


/- Helpers from HalfWilson.lean -/

open scoped Nat BigOperators
open Finset

namespace HalfWilson

/-- In `ZMod p`, the reflected term in the upper half of `1, ..., 2*m`
is the negative of the corresponding lower-half term, when `p = 2*m + 1`. -/
lemma cast_reflected_add_one_eq_neg (p m j : ℕ) (hp : p = 2 * m + 1) (hj : j < m) :
    ((m + (m - 1 - j) + 1 : ℕ) : ZMod p) = -((j + 1 : ℕ) : ZMod p) := by
  rw [eq_neg_iff_add_eq_zero]
  rw [← Nat.cast_add]
  have hsum : m + (m - 1 - j) + 1 + (j + 1) = p := by
    omega
  rw [hsum]
  exact ZMod.natCast_self p

/-- Split `(p-1)!` into lower-half and reflected upper-half factors. -/
lemma factorial_eq_neg_pow_mul_sq (p m : ℕ) (hp : p = 2 * m + 1) :
    (((p - 1).factorial : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ m * (((m.factorial : ℕ) : ZMod p) ^ 2) := by
  have hp1 : p - 1 = 2 * m := by omega
  calc
    (((p - 1).factorial : ℕ) : ZMod p)
        = (((2 * m).factorial : ℕ) : ZMod p) := by rw [hp1]
    _ = ∏ i ∈ range (2 * m), ((i + 1 : ℕ) : ZMod p) := by
      rw [← Finset.prod_range_add_one_eq_factorial]
      exact Nat.cast_prod _ _
    _ = (∏ i ∈ range m, ((i + 1 : ℕ) : ZMod p)) *
          (∏ i ∈ range m, ((m + i + 1 : ℕ) : ZMod p)) := by
      rw [← Finset.prod_range_add (fun i : ℕ => ((i + 1 : ℕ) : ZMod p)) m m]
      ring_nf
    _ = (∏ i ∈ range m, ((i + 1 : ℕ) : ZMod p)) *
          (∏ i ∈ range m, ((m + (m - 1 - i) + 1 : ℕ) : ZMod p)) := by
      rw [Finset.prod_range_reflect (fun i : ℕ => ((m + i + 1 : ℕ) : ZMod p)) m]
    _ = (∏ i ∈ range m, ((i + 1 : ℕ) : ZMod p)) *
          (∏ i ∈ range m, -((i + 1 : ℕ) : ZMod p)) := by
      congr 1
      refine Finset.prod_congr rfl ?_
      intro i hi
      exact cast_reflected_add_one_eq_neg p m i hp (Finset.mem_range.mp hi)
    _ = (∏ i ∈ range m, ((i + 1 : ℕ) : ZMod p)) *
          ((-1 : ZMod p) ^ m * ∏ i ∈ range m, ((i + 1 : ℕ) : ZMod p)) := by
      congr 1
      rw [show (∏ i ∈ range m, -((i + 1 : ℕ) : ZMod p)) =
          ∏ i ∈ range m, ((-1 : ZMod p) * ((i + 1 : ℕ) : ZMod p)) by simp]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    _ = (-1 : ZMod p) ^ m * (((m.factorial : ℕ) : ZMod p) ^ 2) := by
      have hprod : (∏ i ∈ range m, ((i + 1 : ℕ) : ZMod p)) =
          (((m.factorial : ℕ) : ZMod p)) := by
        rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
      rw [hprod]
      ring

/-- Half-Wilson: for an odd prime `p = 2*m + 1`, the square of `m!` modulo
`p` is `(-1)^(m+1)`.  The hypothesis `hm` records `m = (p-1)/2`; the proof
uses the equivalent displayed form `p = 2*m+1`. -/
theorem halfWilson (p m : ℕ) [Fact p.Prime] (hodd : Odd p) (hm : m = (p - 1) / 2)
    (hp : p = 2 * m + 1) :
    let C : ZMod p := (m.factorial : ZMod p)
    C ^ 2 = (-1 : ZMod p) ^ (m + 1) := by
  intro C
  have _hodd_used : Odd p := hodd
  have _hm_used : m = (p - 1) / 2 := hm

  have hfac := factorial_eq_neg_pow_mul_sq p m hp
  have hw : (((p - 1).factorial : ℕ) : ZMod p) = -1 := ZMod.wilsons_lemma p
  rw [hw] at hfac
  have hmul : (-1 : ZMod p) ^ m * C ^ 2 = -1 := by
    simpa [C] using hfac.symm
  have hnegpow_mul : (-1 : ZMod p) ^ m * ((-1 : ZMod p) ^ m) = 1 := by
    rw [← pow_add]
    have : (-1 : ZMod p) ^ (m + m) = ((-1 : ZMod p) ^ 2) ^ m := by
      rw [← pow_mul]
      congr 1
      ring
    rw [this]
    simp
  calc
    C ^ 2 = 1 * C ^ 2 := by ring
    _ = (((-1 : ZMod p) ^ m * (-1 : ZMod p) ^ m) * C ^ 2) := by rw [hnegpow_mul]
    _ = (-1 : ZMod p) ^ m * ((-1 : ZMod p) ^ m * C ^ 2) := by ring
    _ = (-1 : ZMod p) ^ m * (-1 : ZMod p) := by rw [hmul]
    _ = (-1 : ZMod p) ^ (m + 1) := by rw [pow_succ]

end HalfWilson


/- Helpers from Work.lean -/

open Finset

lemma quadChar_jacobi_self {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) :
    jacobiSum (quadraticChar F) (quadraticChar F) = - quadraticChar F (-1) := by
  simpa [(quadraticChar_isQuadratic F).inv] using
    (jacobiSum_nontrivial_inv (χ := quadraticChar F) (quadraticChar_ne_one hF))

lemma quadChar_sum_shift {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {a b : F} (hab : a + b ≠ 0) :
    (∑ t : F, quadraticChar F (a - t) * quadraticChar F (b + t)) =
      - quadraticChar F (-1) := by
  let χ : MulChar F ℤ := quadraticChar F
  let s : F := a + b
  have hs : s ≠ 0 := hab
  rw [← quadChar_jacobi_self hF]
  change (∑ t : F, χ (a - t) * χ (b + t)) = jacobiSum χ χ
  rw [jacobiSum]
  let f : F ≃ F := (Equiv.mulRight₀ s hs).trans (Equiv.subLeft a).symm
  rw [← Equiv.sum_comp f (fun t => χ (a - t) * χ (b + t))]
  apply sum_congr rfl
  intro x hx
  have h1 : a - f x = s * x := by
    simp [f, s]
    ring
  have h2 : b + f x = s * (1 - x) := by
    simp [f, s]
    ring
  rw [h1, h2, map_mul, map_mul]
  have hsq : χ s * χ s = 1 := by
    have hnonzero : χ s ≠ 0 := by
      change quadraticChar F s ≠ 0
      rw [quadraticChar_apply]
      exact mt quadraticCharFun_eq_zero_iff.mp hs
    have hq := quadraticChar_isQuadratic F s
    rcases hq with hzero | hpm
    · exact (hnonzero hzero).elim
    · rcases hpm with hpos | hneg
      · simp [χ, hpos]
      · simp [χ, hneg]
  rw [show χ s * χ x * (χ s * χ (1 - x)) = (χ s * χ s) * (χ x * χ (1 - x)) by ring]
  rw [hsq, one_mul]


open Matrix

lemma det_zero_of_mul_transpose_skew {K : Type*} [Field K] [CharZero K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) (hodd : Odd (Fintype.card n)) (hB : B.det ≠ 0)
    (hskew : A * Bᵀ + B * Aᵀ = 0) : A.det = 0 := by
  have hAB : A * Bᵀ = - (B * Aᵀ) := by
    rw [← add_eq_zero_iff_eq_neg]
    exact hskew
  have hdet := congrArg Matrix.det hAB
  rw [det_mul, det_transpose, det_neg, det_mul, det_transpose] at hdet
  have hneg : ((-1 : K) ^ Fintype.card n) = -1 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    simp [pow_succ, pow_mul]
  rw [hneg] at hdet
  have hdet' : A.det * B.det = - (A.det * B.det) := by
    calc
      A.det * B.det = -1 * (B.det * A.det) := hdet
      _ = - (A.det * B.det) := by ring
  have hsum : A.det * B.det + A.det * B.det = 0 := by
    exact add_eq_zero_iff_eq_neg.mpr hdet'
  have hprod : A.det * B.det = 0 := by
    have htwo : (2 : K) * (A.det * B.det) = 0 := by simpa [two_mul] using hsum
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact (mul_eq_zero.mp hprod).resolve_right hB


/- Helpers from PrimeLegendre.lean -/

open Matrix Finset
open scoped Matrix BigOperators

namespace PrimeLegendre

abbrev mOf (p : ℕ) : ℕ := (p - 1) / 2

abbrev C (p : ℕ) : ZMod p := ((mOf p).factorial : ZMod p)

abbrev x (p : ℕ) : Fin (mOf p) → ZMod p :=
  fun i => (((i : ℕ) + 1 : ℕ) : ZMod p) ^ 2

abbrev bD (p : ℕ) (D : ZMod p) : Fin (mOf p) → ZMod p :=
  fun j => D * (((j : ℕ) + 1 : ℕ) : ZMod p)

lemma m_pos_of_three_le {p : ℕ} (hp3 : 3 ≤ p) : 0 < mOf p := by
  dsimp [mOf]
  omega

lemma m_lt_of_prime {p : ℕ} (hp : p.Prime) : mOf p < p := by
  exact TmpDet.half_pred_lt_of_prime hp

lemma prime_odd_of_three_le {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : Odd p := by
  exact hp.odd_of_ne_two (by omega)

lemma p_eq_two_mul_m_add_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    p = 2 * mOf p + 1 := by
  rcases prime_odd_of_three_le hp hp3 with ⟨k, hk⟩
  dsimp [mOf]
  omega

lemma one_le_fin_add_one {m : ℕ} (i : Fin m) : 1 ≤ (i : ℕ) + 1 := by omega

lemma fin_add_one_le {m : ℕ} (i : Fin m) : (i : ℕ) + 1 ≤ m := by
  exact Nat.succ_le_of_lt i.isLt

lemma fin_add_one_lt_p {p : ℕ} (i : Fin (mOf p)) (hm : mOf p < p) :
    (i : ℕ) + 1 < p := by
  exact lt_of_le_of_lt (fin_add_one_le i) hm

lemma natCast_fin_add_one_ne_zero {p : ℕ} (hp : p.Prime) (i : Fin (mOf p)) :
    (((i : ℕ) + 1 : ℕ) : ZMod p) ≠ 0 := by
  have hlt : (i : ℕ) + 1 < p := fin_add_one_lt_p i (m_lt_of_prime hp)
  have hpos : 0 < (i : ℕ) + 1 := by omega
  intro h
  have hdvd : p ∣ (i : ℕ) + 1 := (ZMod.natCast_eq_zero_iff ((i : ℕ) + 1) p).mp h
  exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd

lemma natCast_fin_add_one_injective {p : ℕ} (hp : p.Prime) :
    Function.Injective (fun i : Fin (mOf p) => (((i : ℕ) + 1 : ℕ) : ZMod p)) := by
  intro i j hij
  have hlt_i : (i : ℕ) + 1 < p := fin_add_one_lt_p i (m_lt_of_prime hp)
  have hlt_j : (j : ℕ) + 1 < p := fin_add_one_lt_p j (m_lt_of_prime hp)
  have hmod : (i : ℕ) + 1 ≡ (j : ℕ) + 1 [MOD p] :=
    (ZMod.natCast_eq_natCast_iff ((i : ℕ) + 1) ((j : ℕ) + 1) p).mp hij
  have hnat : (i : ℕ) + 1 = (j : ℕ) + 1 := hmod.eq_of_lt_of_lt hlt_i hlt_j
  apply Fin.ext
  omega

lemma x_injective {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : Function.Injective (x p) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro i j hij
  let a : ℕ := (i : ℕ) + 1
  let b : ℕ := (j : ℕ) + 1
  let az : ZMod p := (a : ZMod p)
  let bz : ZMod p := (b : ZMod p)
  have hmul : (az - bz) * (az + bz) = 0 := by
    have hsub : az ^ 2 - bz ^ 2 = 0 := sub_eq_zero.mpr (by simpa [x, a, b, az, bz] using hij)
    calc
      (az - bz) * (az + bz) = az ^ 2 - bz ^ 2 := by ring
      _ = 0 := hsub
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hdiff | hsum
  · have hcast : (a : ZMod p) = (b : ZMod p) := by
      exact sub_eq_zero.mp (by simpa [az, bz] using hdiff)
    have hlt_a : a < p := by
      dsimp [a]
      exact fin_add_one_lt_p i (m_lt_of_prime hp)
    have hlt_b : b < p := by
      dsimp [b]
      exact fin_add_one_lt_p j (m_lt_of_prime hp)
    have hmod : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp hcast
    have hab : a = b := hmod.eq_of_lt_of_lt hlt_a hlt_b
    apply Fin.ext
    dsimp [a, b] at hab
    omega
  · have hzero : (((a + b : ℕ) : ZMod p) = 0) := by
      simpa [az, bz, Nat.cast_add] using hsum
    have hdvd : p ∣ a + b := (ZMod.natCast_eq_zero_iff (a + b) p).mp hzero
    have hpos : 0 < a + b := by
      dsimp [a, b]
      omega
    have hle_a : a ≤ mOf p := by dsimp [a]; exact fin_add_one_le i
    have hle_b : b ≤ mOf p := by dsimp [b]; exact fin_add_one_le j
    have hp_eq : p = 2 * mOf p + 1 := p_eq_two_mul_m_add_one hp hp3
    have hlt_sum : a + b < p := by omega
    exfalso
    exact (Nat.not_dvd_of_pos_of_lt hpos hlt_sum) hdvd

lemma bD_ne_zero {p : ℕ} (hp : p.Prime) {D : ZMod p} (hD0 : D ≠ 0) :
    ∀ j, bD p D j ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro j
  exact mul_ne_zero hD0 (natCast_fin_add_one_ne_zero hp j)

lemma bD_injective {p : ℕ} (hp : p.Prime) {D : ZMod p} (hD0 : D ≠ 0) :
    Function.Injective (bD p D) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro i j hij
  apply natCast_fin_add_one_injective hp
  exact mul_left_cancel₀ hD0 (by simpa [bD] using hij)

lemma prod_fin_add_one_eq_factorial (p : ℕ) :
    (∏ j : Fin (mOf p), (((j : ℕ) + 1 : ℕ) : ZMod p)) = C p := by
  calc
    (∏ j : Fin (mOf p), (((j : ℕ) + 1 : ℕ) : ZMod p))
        = (∏ j ∈ Finset.range (mOf p), (((j : ℕ) + 1 : ℕ) : ZMod p)) := by
          simpa using (Fin.prod_univ_eq_prod_range (fun j : ℕ => (((j : ℕ) + 1 : ℕ) : ZMod p)) (mOf p))
    _ = C p := by
      dsimp [C]
      rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

lemma prod_bD_eq (p : ℕ) (D : ZMod p) :
    (∏ j : Fin (mOf p), bD p D j) = D ^ (mOf p) * C p := by
  calc
    (∏ j : Fin (mOf p), bD p D j)
        = (∏ j : Fin (mOf p), D * (((j : ℕ) + 1 : ℕ) : ZMod p)) := rfl
    _ = (∏ _j : Fin (mOf p), D) * ∏ j : Fin (mOf p), (((j : ℕ) + 1 : ℕ) : ZMod p) := by
      rw [Finset.prod_mul_distrib]
    _ = D ^ (mOf p) * C p := by
      rw [Finset.prod_const, prod_fin_add_one_eq_factorial]
      simp

lemma x_pow_m_eq_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∀ i : Fin (mOf p), x p i ^ (mOf p) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro i
  let a : ZMod p := (((i : ℕ) + 1 : ℕ) : ZMod p)
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact natCast_fin_add_one_ne_zero hp i
  have hp_eq : p = 2 * mOf p + 1 := p_eq_two_mul_m_add_one hp hp3
  calc
    x p i ^ (mOf p) = (a ^ 2) ^ (mOf p) := by rfl
    _ = a ^ (2 * mOf p) := by rw [pow_mul]
    _ = a ^ (p - 1) := by
      congr 1
      omega
    _ = 1 := ZMod.pow_card_sub_one_eq_one ha0

lemma det_ne_zero_of_D_pow_mul_C_ne_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (D : ZMod p) (hD0 : D ≠ 0) (hprod : D ^ (mOf p) * C p ≠ 1) :
    (TmpDet.legendreMatrix p (mOf p) (bD p D) (x p)).det ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (mOf p) := ⟨Nat.ne_of_gt (m_pos_of_three_le hp3)⟩
  refine TmpDet.legendre_det_ne_zero_of_factorization (p := p) (m := mOf p)
    (TmpDet.half_pred_lt_of_prime hp) (b := bD p D) (x := x p)
    (bD_ne_zero hp hD0) (bD_injective hp hD0) (x_injective hp hp3) ?_ ?_
  · simpa [prod_bD_eq] using hprod
  · exact TmpDet.factorization_of_pow_eq_one (p := p) (m := mOf p)
      (b := bD p D) (x := x p) (bD_ne_zero hp hD0) (x_pow_m_eq_one hp hp3)

lemma det_matrix_ne_zero_of_D_pow_mul_C_ne_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (D : ZMod p) (hD0 : D ≠ 0) (hprod : D ^ (mOf p) * C p ≠ 1) :
    (Matrix.of fun i j : Fin (mOf p) => (x p i - bD p D j) ^ (mOf p)).det ≠ 0 := by
  simpa [TmpDet.legendreMatrix] using det_ne_zero_of_D_pow_mul_C_ne_one hp hp3 D hD0 hprod

lemma C_ne_zero {p : ℕ} (hp : p.Prime) : C p ≠ 0 := by
  dsimp [C]
  intro h
  have hdvd : p ∣ (mOf p).factorial := (ZMod.natCast_eq_zero_iff ((mOf p).factorial) p).mp h
  have hle : p ≤ mOf p := (hp.dvd_factorial).mp hdvd
  exact (not_le_of_gt (m_lt_of_prime hp)) hle

lemma neg_one_ne_one_zmod {p : ℕ} (hp3 : 3 ≤ p) : (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have h' : (1 : ZMod p) + 1 = 0 := by
      have h'' : (-1 : ZMod p) + 1 = (1 : ZMod p) + 1 := by rw [h]
      exact h''.symm.trans (by simp)
    norm_num at h' ⊢
    exact h'
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hp3) hdvd

lemma halfWilson_C_sq {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    C p ^ 2 = (-1 : ZMod p) ^ (mOf p + 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact HalfWilson.halfWilson p (mOf p) (prime_odd_of_three_le hp hp3) rfl (p_eq_two_mul_m_add_one hp hp3)

lemma even_m_of_mod_four_eq_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hp4 : p % 4 = 1) :
    Even (mOf p) := by
  rcases p_eq_two_mul_m_add_one hp hp3 with hp_eq
  rw [hp_eq] at hp4
  use (mOf p) / 2
  have : (2 * mOf p + 1) % 4 = 1 := hp4
  omega

lemma odd_m_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hp4 : p % 4 = 3) :
    Odd (mOf p) := by
  rcases p_eq_two_mul_m_add_one hp hp3 with hp_eq
  rw [hp_eq] at hp4
  rw [Nat.odd_iff]
  omega

lemma C_pow_m_add_one_ne_one_of_mod_four_eq_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 1) : C p ^ (mOf p + 1) ≠ 1 := by
  have hC2 := halfWilson_C_sq hp hp3
  have hm_even : Even (mOf p) := even_m_of_mod_four_eq_one hp hp3 hp4
  have hm1_odd : Odd (mOf p + 1) := by
    rcases hm_even with ⟨k, hk⟩
    use k
    omega
  intro h
  have hsquare : (C p ^ (mOf p + 1)) ^ 2 = (1 : ZMod p) := by rw [h, one_pow]
  have hneg : (C p ^ (mOf p + 1)) ^ 2 = (-1 : ZMod p) := by
    calc
      (C p ^ (mOf p + 1)) ^ 2 = (C p ^ 2) ^ (mOf p + 1) := by ring
      _ = ((-1 : ZMod p) ^ (mOf p + 1)) ^ (mOf p + 1) := by rw [hC2]
      _ = (-1 : ZMod p) := by
        rw [← pow_mul]
        exact Odd.neg_one_pow (hm1_odd.mul hm1_odd)
  exact neg_one_ne_one_zmod hp3 (by rw [← hneg, hsquare])

lemma negC_pow_m_mul_C_ne_one_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) : (-C p) ^ (mOf p) * C p ≠ 1 := by
  have hC2 := halfWilson_C_sq hp hp3
  have hm_odd : Odd (mOf p) := odd_m_of_mod_four_eq_three hp hp3 hp4
  have hm1_even : Even (mOf p + 1) := by
    rcases hm_odd with ⟨k, hk⟩
    use k + 1
    omega
  have hC2_one : C p ^ 2 = (1 : ZMod p) := by
    rw [hC2]
    exact Even.neg_one_pow hm1_even
  have hCp : C p ^ (mOf p + 1) = (1 : ZMod p) := by
    rcases hm1_even with ⟨k, hk⟩
    have hk2 : mOf p + 1 = 2 * k := by omega
    rw [hk2]
    calc
      C p ^ (2 * k) = (C p ^ 2) ^ k := by rw [pow_mul]
      _ = 1 := by rw [hC2_one, one_pow]
  have hval : (-C p) ^ (mOf p) * C p = (-1 : ZMod p) := by
    calc
      (-C p) ^ (mOf p) * C p = ((-1 : ZMod p) ^ (mOf p) * C p ^ (mOf p)) * C p := by
        rw [neg_eq_neg_one_mul, mul_pow]
      _ = (-1 : ZMod p) ^ (mOf p) * (C p ^ (mOf p) * C p) := by ring
      _ = (-1 : ZMod p) ^ (mOf p) * C p ^ (mOf p + 1) := by rw [pow_succ]
      _ = (-1 : ZMod p) * 1 := by rw [Odd.neg_one_pow hm_odd, hCp]
      _ = (-1 : ZMod p) := by ring
  intro h
  exact neg_one_ne_one_zmod hp3 (by rw [← hval, h])

theorem det_ne_zero_D_eq_C_of_mod_four_eq_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 1) :
    (Matrix.of fun i j : Fin (mOf p) => (x p i - bD p (C p) j) ^ (mOf p)).det ≠ 0 := by
  refine det_matrix_ne_zero_of_D_pow_mul_C_ne_one hp hp3 (C p) (C_ne_zero hp) ?_
  simpa [pow_succ] using C_pow_m_add_one_ne_one_of_mod_four_eq_one hp hp3 hp4

theorem det_ne_zero_D_eq_negC_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) :
    (Matrix.of fun i j : Fin (mOf p) => (x p i - bD p (-C p) j) ^ (mOf p)).det ≠ 0 := by
  refine det_matrix_ne_zero_of_D_pow_mul_C_ne_one hp hp3 (-C p) (neg_ne_zero.mpr (C_ne_zero hp)) ?_
  exact negC_pow_m_mul_C_ne_one_of_mod_four_eq_three hp hp3 hp4

end PrimeLegendre


/- Helpers from FinalDev.lean -/

open Matrix Finset
open scoped Matrix BigOperators

namespace FinalDev

/-- The integer matrix from the original specification, with an arbitrary integer
coefficient `D` in place of `((p-1)/2)!`. -/
noncomputable def originalMatrix (p : ℕ) (D : ℤ) :
    Matrix (Fin (PrimeLegendre.mOf p)) (Fin (PrimeLegendre.mOf p)) ℤ :=
  fun i j =>
    jacobiSym ((((i : ℕ) + 1 : ℕ) : ℤ) ^ 2 - D * (((j : ℕ) + 1 : ℕ) : ℤ)) p

/-- The concrete original matrix from the specification. -/
noncomputable abbrev originalCMatrix (p : ℕ) :
    Matrix (Fin (PrimeLegendre.mOf p)) (Fin (PrimeLegendre.mOf p)) ℤ :=
  originalMatrix p (((PrimeLegendre.mOf p).factorial : ℕ) : ℤ)

/-- The same construction with the negative factorial coefficient.  This is the
auxiliary matrix naturally paired with the `D = -C` finite-field matrix. -/
noncomputable abbrev originalNegCMatrix (p : ℕ) :
    Matrix (Fin (PrimeLegendre.mOf p)) (Fin (PrimeLegendre.mOf p)) ℤ :=
  originalMatrix p (-(((PrimeLegendre.mOf p).factorial : ℕ) : ℤ))

lemma nat_div_two_eq_mOf {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    p / 2 = PrimeLegendre.mOf p := by
  have hodd : Odd p := PrimeLegendre.prime_odd_of_three_le hp hp3
  rcases hodd with ⟨k, hk⟩
  dsimp [PrimeLegendre.mOf]
  omega

/-- Entrywise bridge: after reducing modulo the prime `p`, the integer Jacobi
symbol entry is exactly the Euler-power entry used in the finite-field matrix. -/
lemma original_entry_cast_eq_finite {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (D : ℤ)
    (i j : Fin (PrimeLegendre.mOf p)) :
    ((originalMatrix p D i j : ℤ) : ZMod p) =
      (PrimeLegendre.x p i - PrimeLegendre.bD p (D : ZMod p) j) ^ (PrimeLegendre.mOf p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdiv : p / 2 = PrimeLegendre.mOf p := nat_div_two_eq_mOf hp hp3
  let a : ℤ := ((((i : ℕ) + 1 : ℕ) : ℤ) ^ 2 - D * (((j : ℕ) + 1 : ℕ) : ℤ))
  calc
    ((originalMatrix p D i j : ℤ) : ZMod p)
        = ((legendreSym p a : ℤ) : ZMod p) := by
          simpa [originalMatrix, a] using
            congrArg (fun z : ℤ => (z : ZMod p))
              (jacobiSym.legendreSym.to_jacobiSym p a).symm
    _ = (a : ZMod p) ^ (p / 2) := by
          exact legendreSym.eq_pow p a
    _ = (a : ZMod p) ^ (PrimeLegendre.mOf p) := by rw [hdiv]
    _ = (PrimeLegendre.x p i - PrimeLegendre.bD p (D : ZMod p) j) ^ (PrimeLegendre.mOf p) := by
          congr 1
          dsimp [a, PrimeLegendre.x, PrimeLegendre.bD]
          norm_num [Int.cast_sub, Int.cast_mul, Int.cast_pow]

/-- Determinant bridge for any integer coefficient `D`: reducing the determinant
of the original Jacobi-symbol matrix modulo `p` gives the finite-field
determinant with `D` cast to `ZMod p`. -/
theorem original_det_cast_eq_finite {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (D : ℤ) :
    ((originalMatrix p D).det : ZMod p) =
      (Matrix.of fun i j : Fin (PrimeLegendre.mOf p) =>
        (PrimeLegendre.x p i - PrimeLegendre.bD p (D : ZMod p) j) ^
          (PrimeLegendre.mOf p)).det := by
  rw [Int.cast_det]
  apply congrArg Matrix.det
  ext i j
  exact original_entry_cast_eq_finite hp hp3 D i j

/-- Specialization of the determinant bridge to `D = ((p-1)/2)!`, the matrix in
the original specification. -/
theorem original_C_det_cast_eq_finite {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ((originalCMatrix p).det : ZMod p) =
      (Matrix.of fun i j : Fin (PrimeLegendre.mOf p) =>
        (PrimeLegendre.x p i - PrimeLegendre.bD p (PrimeLegendre.C p) j) ^
          (PrimeLegendre.mOf p)).det := by
  simpa [originalCMatrix, PrimeLegendre.C] using
    (original_det_cast_eq_finite hp hp3 (((PrimeLegendre.mOf p).factorial : ℕ) : ℤ))

/-- Therefore, when `p ≡ 1 (mod 4)`, the original integer determinant is
nonzero.  This is the main nonzero half of the requested bridge to the existing
finite-field theorem in `PrimeLegendre`. -/
theorem original_C_det_ne_zero_of_mod_four_eq_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 1) :
    (originalCMatrix p).det ≠ 0 := by
  intro hzero
  have hcast := original_C_det_cast_eq_finite hp hp3
  have hfinite_ne := PrimeLegendre.det_ne_zero_D_eq_C_of_mod_four_eq_one hp hp3 hp4
  have hcast_zero : ((originalCMatrix p).det : ZMod p) = 0 := by simp [hzero]
  exact hfinite_ne (by simpa [hcast_zero] using hcast.symm)

/-- Specialization of the determinant bridge to the auxiliary coefficient
`D = -((p-1)/2)!`. -/
theorem original_negC_det_cast_eq_finite {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ((originalNegCMatrix p).det : ZMod p) =
      (Matrix.of fun i j : Fin (PrimeLegendre.mOf p) =>
        (PrimeLegendre.x p i - PrimeLegendre.bD p (-PrimeLegendre.C p) j) ^
          (PrimeLegendre.mOf p)).det := by
  simpa [originalNegCMatrix, PrimeLegendre.C] using
    (original_det_cast_eq_finite hp hp3 (-(((PrimeLegendre.mOf p).factorial : ℕ) : ℤ)))

/-- For `p ≡ 3 (mod 4)`, the auxiliary `D=-C` integer determinant is nonzero.
This is the compiled partial result available from the finite-field theorem. -/
theorem original_negC_det_ne_zero_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) :
    (originalNegCMatrix p).det ≠ 0 := by
  intro hzero
  have hcast := original_negC_det_cast_eq_finite hp hp3
  have hfinite_ne := PrimeLegendre.det_ne_zero_D_eq_negC_of_mod_four_eq_three hp hp3 hp4
  have hcast_zero : ((originalNegCMatrix p).det : ZMod p) = 0 := by simp [hzero]
  exact hfinite_ne (by simpa [hcast_zero] using hcast.symm)

/-- Equivalently, the reduction of the auxiliary integer determinant modulo `p`
is already nonzero. -/
theorem original_negC_det_cast_ne_zero_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) :
    ((originalNegCMatrix p).det : ZMod p) ≠ 0 := by
  rw [original_negC_det_cast_eq_finite hp hp3]
  exact PrimeLegendre.det_ne_zero_D_eq_negC_of_mod_four_eq_three hp hp3 hp4

/-- The two finite-field determinants whose product appears in the `p ≡ 3 (mod
4)` approach are both certified nonzero on the auxiliary side. -/
theorem finite_negC_det_mul_ne_zero_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) :
    (Matrix.of fun i j : Fin (PrimeLegendre.mOf p) =>
        (PrimeLegendre.x p i - PrimeLegendre.bD p (-PrimeLegendre.C p) j) ^
          (PrimeLegendre.mOf p)).det * PrimeLegendre.C p ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact mul_ne_zero (PrimeLegendre.det_ne_zero_D_eq_negC_of_mod_four_eq_three hp hp3 hp4)
    (PrimeLegendre.C_ne_zero hp)

end FinalDev


/- Helpers from P3Zero.lean -/

open Matrix Finset
open scoped Matrix BigOperators

namespace PrimeLegendre

/-- In the `p ≡ 3 (mod 4)` case, the Wilson half-factorial coefficient squares to `1`
in `ZMod p`.  This is one of the structural inputs for the intended partition of the
nonzero field elements into the two signed half-intervals. -/
lemma C_sq_one_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) : C p ^ 2 = (1 : ZMod p) := by
  have hC2 := halfWilson_C_sq hp hp3
  have hm_odd : Odd (mOf p) := odd_m_of_mod_four_eq_three hp hp3 hp4
  have hm1_even : Even (mOf p + 1) := by
    rcases hm_odd with ⟨k, hk⟩
    use k + 1
    omega
  rw [hC2]
  exact Even.neg_one_pow hm1_even

/-- Consequently the same coefficient is one of the two square roots of `1`. -/
lemma C_eq_one_or_eq_neg_one_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) : C p = (1 : ZMod p) ∨ C p = (-1 : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsq : C p ^ 2 = (1 : ZMod p) := C_sq_one_of_mod_four_eq_three hp hp3 hp4
  have hmul : (C p - 1) * (C p + 1) = (0 : ZMod p) := by
    calc
      (C p - 1) * (C p + 1) = C p ^ 2 - 1 := by ring
      _ = 0 := by rw [hsq]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hminus | hplus
  · left
    exact sub_eq_zero.mp hminus
  · right
    exact add_eq_zero_iff_eq_neg.mp hplus

/-- The characteristic of `ZMod p` is not two under the standing hypotheses. -/
lemma zmod_ringChar_ne_two {p : ℕ} (hp3 : 3 ≤ p) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n p]
  omega

/-- For `p ≡ 3 (mod 4)`, the quadratic character of `-1` over `ZMod p` is `-1`. -/
lemma quadraticChar_neg_one_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) : quadraticChar (ZMod p) (-1) = -1 := by
  rw [quadraticChar_neg_one (zmod_ringChar_ne_two (p := p) hp3), ZMod.card]
  exact ZMod.χ₄_nat_three_mod_four hp4

/-- The two square entries `x_i` and `x_j` never sum to zero when `p ≡ 3 (mod 4)`.
Equivalently, `-1` is not a square in `ZMod p`. -/
lemma x_add_x_ne_zero_of_mod_four_eq_three {p : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 3) (i j : Fin (mOf p)) : x p i + x p j ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hsum
  let a : ZMod p := (((i : ℕ) + 1 : ℕ) : ZMod p)
  let b : ZMod p := (((j : ℕ) + 1 : ℕ) : ZMod p)
  have hb0 : b ≠ 0 := by
    dsimp [b]
    exact natCast_fin_add_one_ne_zero hp j
  have hsquares : a ^ 2 + b ^ 2 = 0 := by
    simpa [x, a, b] using hsum
  have hsq_neg : (a * b⁻¹) ^ 2 = (-1 : ZMod p) := by
    have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb0
    have hmul : (a ^ 2 + b ^ 2) * (b ^ 2)⁻¹ = 0 := by
      rw [hsquares, zero_mul]
    have hmul' : a ^ 2 * (b ^ 2)⁻¹ + 1 = 0 := by
      simpa [add_mul, hb2] using hmul
    have haeq : a ^ 2 * (b ^ 2)⁻¹ = (-1 : ZMod p) := add_eq_zero_iff_eq_neg.mp hmul'
    calc
      (a * b⁻¹) ^ 2 = a ^ 2 * (b⁻¹) ^ 2 := by ring
      _ = a ^ 2 * (b ^ 2)⁻¹ := by rw [inv_pow]
      _ = (-1 : ZMod p) := haeq
  have hsq_neg' : (-1 : ZMod p) = (a * b⁻¹) * (a * b⁻¹) := by
    rw [← hsq_neg]
    ring
  exact (ZMod.exists_sq_eq_neg_one_iff.mp ⟨a * b⁻¹, hsq_neg'⟩) hp4

/-- A direct specialization of `quadChar_sum_shift` to the entries `x_i,x_j` in the
`p ≡ 3 (mod 4)` case.  This is the full-field character-sum identity underlying the
entrywise matrix skew relation; the remaining work is to replace the full-field sum by
the two signed half-interval sums coming from `C = ±1`. -/
lemma quadChar_sum_shift_x_eq_one_of_mod_four_eq_three {p : ℕ} [Fact p.Prime] (hp : p.Prime)
    (hp3 : 3 ≤ p) (hp4 : p % 4 = 3) (i j : Fin (mOf p)) :
    (∑ t : ZMod p, quadraticChar (ZMod p) (x p i - t) *
        quadraticChar (ZMod p) (x p j + t)) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hshift := quadChar_sum_shift (F := ZMod p) (zmod_ringChar_ne_two (p := p) hp3)
    (a := x p i) (b := x p j) (x_add_x_ne_zero_of_mod_four_eq_three hp hp4 i j)
  rw [quadraticChar_neg_one_of_mod_four_eq_three hp3 hp4] at hshift
  simpa using hshift

end PrimeLegendre


/- Helpers from Partition.lean -/

open Finset
open scoped BigOperators

namespace PrimeLegendre

/-- Under the standard equivalence `Fin p ≃ ZMod p`, the element indexed by `i`
is just the natural-number cast of `i.val`. -/
lemma finEquiv_apply_eq_natCast (p : ℕ) [NeZero p] (i : Fin p) :
    (ZMod.finEquiv p i : ZMod p) = (((i : ℕ) : ℕ) : ZMod p) := by
  rw [← ZMod.natCast_zmod_val (ZMod.finEquiv p i)]
  congr
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ _ => rfl

/-- Reindex a sum over `ZMod p` by the least nonnegative representatives `0, ..., p-1`. -/
lemma sum_zmod_eq_sum_range {A : Type*} [AddCommMonoid A] (p : ℕ) [NeZero p]
    (f : ZMod p → A) :
    (∑ t : ZMod p, f t) = ∑ i ∈ Finset.range p, f (((i : ℕ) : ℕ) : ZMod p) := by
  calc
    (∑ t : ZMod p, f t) = ∑ i : Fin p, f (ZMod.finEquiv p i : ZMod p) := by
      refine (Fintype.sum_equiv (ZMod.finEquiv p).toEquiv
        (fun i : Fin p => f (ZMod.finEquiv p i : ZMod p)) f ?_).symm
      intro i
      rfl
    _ = ∑ i : Fin p, f (((i : ℕ) : ℕ) : ZMod p) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [finEquiv_apply_eq_natCast]
    _ = ∑ i ∈ Finset.range p, f (((i : ℕ) : ℕ) : ZMod p) := by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => f (((i : ℕ) : ℕ) : ZMod p)) p)

/-- The first half of a range, with the zero term split off. -/
lemma sum_range_succ_eq_zero_add_fin {A : Type*} [AddCommMonoid A] (m : ℕ)
    (g : ℕ → A) :
    (∑ i ∈ Finset.range (m + 1), g i) = g 0 + ∑ i : Fin m, g ((i : ℕ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1)) m]
  rw [show m + 1 = Nat.succ m by omega]
  rw [Finset.sum_range_succ']
  rw [add_comm]

/-- A purely finite-sum partition of the range `0, ..., 2*m`.  The last sum is
written in the reflected order which will become the negative representatives in
`ZMod (2*m+1)`. -/
lemma sum_range_two_mul_add_one_partition {A : Type*} [AddCommMonoid A] (m : ℕ)
    (g : ℕ → A) :
    (∑ i ∈ Finset.range (2 * m + 1), g i) =
      g 0 + ∑ j : Fin m, g ((j : ℕ) + 1) + ∑ j : Fin m, g (2 * m - (j : ℕ)) := by
  calc
    (∑ i ∈ Finset.range (2 * m + 1), g i)
        = ∑ i ∈ Finset.range ((m + 1) + m), g i := by
          congr 1
          ring_nf
    _ = (∑ i ∈ Finset.range (m + 1), g i) +
          ∑ i ∈ Finset.range m, g ((m + 1) + i) := by
          rw [Finset.sum_range_add]
    _ = (g 0 + ∑ j : Fin m, g ((j : ℕ) + 1)) +
          ∑ i ∈ Finset.range m, g ((m + 1) + i) := by
          rw [sum_range_succ_eq_zero_add_fin]
    _ = (g 0 + ∑ j : Fin m, g ((j : ℕ) + 1)) +
          ∑ j ∈ Finset.range m, g (2 * m - j) := by
          congr 1
          calc
            (∑ i ∈ Finset.range m, g ((m + 1) + i))
                = ∑ j ∈ Finset.range m, g ((m + 1) + (m - 1 - j)) := by
                  exact (Finset.sum_range_reflect (fun k => g ((m + 1) + k)) m).symm
            _ = ∑ j ∈ Finset.range m, g (2 * m - j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hjlt : j < m := Finset.mem_range.mp hj
                  congr 1
                  omega
    _ = g 0 + ∑ j : Fin m, g ((j : ℕ) + 1) + ∑ j : Fin m, g (2 * m - (j : ℕ)) := by
          rw [Fin.sum_univ_eq_sum_range (fun j => g (2 * m - j)) m]

/-- In `ZMod (2*m+1)`, the upper-half representative `2*m - j` is the negative
of the lower-half representative `j+1`. -/
lemma natCast_two_mul_sub_eq_neg (m : ℕ) (j : Fin m) :
    ((((2 * m - (j : ℕ)) : ℕ) : ZMod (2 * m + 1)) =
      - ((((j : ℕ) + 1 : ℕ) : ZMod (2 * m + 1)))) := by
  apply eq_neg_of_add_eq_zero_left
  have hsum_nat : (2 * m - (j : ℕ)) + ((j : ℕ) + 1) = 2 * m + 1 := by
    have hj : (j : ℕ) ≤ 2 * m := by omega
    omega
  have hcast : ((((2 * m - (j : ℕ)) + ((j : ℕ) + 1) : ℕ) : ZMod (2 * m + 1)) = 0) := by
    rw [hsum_nat]
    exact CharP.cast_eq_zero (ZMod (2 * m + 1)) (2 * m + 1)
  simpa [Nat.cast_add] using hcast

/-- Partition a full `ZMod p` sum into the zero residue, the lower half
`1, ..., m`, and the negatives of the lower half, assuming `p = 2*m+1`.
This is the reusable additive-commutative-monoid form. -/
lemma sum_zmod_partition_of_eq {A : Type*} [AddCommMonoid A] {p m : ℕ} [NeZero p]
    (hp_eq : p = 2 * m + 1) (f : ZMod p → A) :
    (∑ t : ZMod p, f t) =
      f 0 + ∑ j : Fin m, f (((((j : ℕ) + 1 : ℕ) : ZMod p))) +
        ∑ j : Fin m, f (-(((((j : ℕ) + 1 : ℕ) : ZMod p)))) := by
  calc
    (∑ t : ZMod p, f t) = ∑ i ∈ Finset.range p, f (((i : ℕ) : ℕ) : ZMod p) := by
      rw [sum_zmod_eq_sum_range]
    _ = ∑ i ∈ Finset.range (2 * m + 1), f (((i : ℕ) : ℕ) : ZMod p) := by
      rw [show Finset.range p = Finset.range (2 * m + 1) from congrArg Finset.range hp_eq]
    _ = f 0 + ∑ j : Fin m, f (((((j : ℕ) + 1 : ℕ) : ZMod p))) +
          ∑ j : Fin m, f (((((2 * m - (j : ℕ)) : ℕ) : ZMod p))) := by
      simpa using sum_range_two_mul_add_one_partition (m := m)
        (g := fun i : ℕ => f (((i : ℕ) : ℕ) : ZMod p))
    _ = f 0 + ∑ j : Fin m, f (((((j : ℕ) + 1 : ℕ) : ZMod p))) +
          ∑ j : Fin m, f (-(((((j : ℕ) + 1 : ℕ) : ZMod p)))) := by
      subst p
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [natCast_two_mul_sub_eq_neg]


/-- Prime-specialized version with an explicit primality hypothesis.  The `[NeZero p]`
instance is the standard finite-`ZMod` instance needed to state the full sum. -/
lemma sum_zmod_partition_of_prime {A : Type*} [AddCommMonoid A] {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp3 : 3 ≤ p) (f : ZMod p → A) :
    (∑ t : ZMod p, f t) =
      f 0 + ∑ j : Fin (mOf p), f (((((j : ℕ) + 1 : ℕ) : ZMod p))) +
        ∑ j : Fin (mOf p), f (-(((((j : ℕ) + 1 : ℕ) : ZMod p)))) := by
  exact sum_zmod_partition_of_eq (p := p) (m := mOf p) (p_eq_two_mul_m_add_one hp hp3) f

/-- Prime-specialized version with `m = PrimeLegendre.mOf p`. -/
lemma sum_zmod_partition {A : Type*} [AddCommMonoid A] {p : ℕ} [Fact p.Prime]
    (hp3 : 3 ≤ p) (f : ZMod p → A) :
    (∑ t : ZMod p, f t) =
      f 0 + ∑ j : Fin (mOf p), f (((((j : ℕ) + 1 : ℕ) : ZMod p))) +
        ∑ j : Fin (mOf p), f (-(((((j : ℕ) + 1 : ℕ) : ZMod p)))) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact sum_zmod_partition_of_eq (p := p) (m := mOf p) (p_eq_two_mul_m_add_one hp hp3) f

end PrimeLegendre


/- Helpers from P3Final.lean -/

open Matrix Finset
open scoped Matrix BigOperators
set_option maxHeartbeats 800000


namespace PrimeLegendre

lemma quadChar_x_eq_one {p : ℕ} [Fact p.Prime] (hp : p.Prime) (i : Fin (mOf p)) :
    quadraticChar (ZMod p) (x p i) = 1 := by
  simpa [x] using
    (quadraticChar_sq_one' (F := ZMod p)
      (a := ((((i : ℕ) + 1 : ℕ) : ZMod p))) (natCast_fin_add_one_ne_zero hp i))

lemma lower_add_upper_quadChar_sum_eq_zero_of_mod_four_eq_three {p : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hp3 : 3 ≤ p) (hp4 : p % 4 = 3) (i j : Fin (mOf p)) :
    (∑ k : Fin (mOf p),
        quadraticChar (ZMod p) (x p i - (((k : ℕ) + 1 : ℕ) : ZMod p)) *
          quadraticChar (ZMod p) (x p j + (((k : ℕ) + 1 : ℕ) : ZMod p))) +
      (∑ k : Fin (mOf p),
        quadraticChar (ZMod p) (x p i + (((k : ℕ) + 1 : ℕ) : ZMod p)) *
          quadraticChar (ZMod p) (x p j - (((k : ℕ) + 1 : ℕ) : ZMod p))) = 0 := by
  let f : ZMod p → ℤ := fun t =>
    quadraticChar (ZMod p) (x p i - t) * quadraticChar (ZMod p) (x p j + t)
  have hfull := quadChar_sum_shift_x_eq_one_of_mod_four_eq_three (p := p) hp hp3 hp4 i j
  have hpart := sum_zmod_partition (p := p) (A := ℤ) hp3 f
  have hf0 : f 0 = 1 := by
    change quadraticChar (ZMod p) (x p i - 0) * quadraticChar (ZMod p) (x p j + 0) = 1
    rw [sub_zero, add_zero, quadChar_x_eq_one hp i, quadChar_x_eq_one hp j]
    norm_num
  have hpart' : (1 : ℤ) = f 0 +
      (∑ k : Fin (mOf p), f (((((k : ℕ) + 1 : ℕ) : ZMod p)))) +
        ∑ k : Fin (mOf p), f (-(((((k : ℕ) + 1 : ℕ) : ZMod p)))) := by
    simpa [f] using hfull.symm.trans hpart
  rw [hf0] at hpart'
  have hzero :
      (∑ k : Fin (mOf p), f (((((k : ℕ) + 1 : ℕ) : ZMod p)))) +
        ∑ k : Fin (mOf p), f (-(((((k : ℕ) + 1 : ℕ) : ZMod p)))) = 0 := by
    omega
  rw [← hzero]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  dsimp [f]
  congr 2 <;> ring_nf

end PrimeLegendre

namespace FinalDev

noncomputable abbrev originalCQ (p : ℕ) :
    Matrix (Fin (PrimeLegendre.mOf p)) (Fin (PrimeLegendre.mOf p)) ℚ :=
  (originalCMatrix p).map (Int.castRingHom ℚ)

noncomputable abbrev originalNegCQ (p : ℕ) :
    Matrix (Fin (PrimeLegendre.mOf p)) (Fin (PrimeLegendre.mOf p)) ℚ :=
  (originalNegCMatrix p).map (Int.castRingHom ℚ)

lemma originalMatrix_entry_cast_rat_eq_quadraticChar {p : ℕ} [Fact p.Prime]
    (D : ℤ) (i j : Fin (PrimeLegendre.mOf p)) :
    ((originalMatrix p D i j : ℤ) : ℚ) =
      (quadraticChar (ZMod p)
        (((((i : ℕ) + 1 : ℕ) : ℤ) ^ 2 - D * (((j : ℕ) + 1 : ℕ) : ℤ) : ℤ) : ZMod p) : ℚ) := by
  let a : ℤ := (((i : ℕ) + 1 : ℕ) : ℤ) ^ 2 - D * (((j : ℕ) + 1 : ℕ) : ℤ)
  calc
    ((originalMatrix p D i j : ℤ) : ℚ) = (legendreSym p a : ℚ) := by
      simpa [originalMatrix, a] using
        congrArg (fun z : ℤ => (z : ℚ))
          (jacobiSym.legendreSym.to_jacobiSym p a).symm
    _ = (quadraticChar (ZMod p) (a : ZMod p) : ℚ) := by
      rfl

lemma originalC_entry_cast_rat_eq_quadChar_sub_C {p : ℕ} [Fact p.Prime]
    (i j : Fin (PrimeLegendre.mOf p)) :
    ((originalCMatrix p i j : ℤ) : ℚ) =
      (quadraticChar (ZMod p) (PrimeLegendre.x p i - PrimeLegendre.C p *
        (((j : ℕ) + 1 : ℕ) : ZMod p)) : ℚ) := by
  simpa [originalCMatrix, PrimeLegendre.x, PrimeLegendre.C, sub_eq_add_neg, Int.cast_sub,
    Int.cast_mul, Int.cast_pow, PrimeLegendre.bD] using
    (originalMatrix_entry_cast_rat_eq_quadraticChar (p := p)
      (((PrimeLegendre.mOf p).factorial : ℕ) : ℤ) i j)

lemma originalNegC_entry_cast_rat_eq_quadChar_add_C {p : ℕ} [Fact p.Prime]
    (i j : Fin (PrimeLegendre.mOf p)) :
    ((originalNegCMatrix p i j : ℤ) : ℚ) =
      (quadraticChar (ZMod p) (PrimeLegendre.x p i + PrimeLegendre.C p *
        (((j : ℕ) + 1 : ℕ) : ZMod p)) : ℚ) := by
  simpa [originalNegCMatrix, originalCMatrix, PrimeLegendre.x, PrimeLegendre.C, sub_eq_add_neg,
    Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_pow, PrimeLegendre.bD] using
    (originalMatrix_entry_cast_rat_eq_quadraticChar (p := p)
      (-(((PrimeLegendre.mOf p).factorial : ℕ) : ℤ)) i j)

lemma originalCQ_entry_eq_quadChar_sub_C {p : ℕ} [Fact p.Prime]
    (i j : Fin (PrimeLegendre.mOf p)) :
    originalCQ p i j =
      (quadraticChar (ZMod p) (PrimeLegendre.x p i - PrimeLegendre.C p *
        (((j : ℕ) + 1 : ℕ) : ZMod p)) : ℚ) := by
  simpa [originalCQ] using originalC_entry_cast_rat_eq_quadChar_sub_C (p := p) i j

lemma originalNegCQ_entry_eq_quadChar_add_C {p : ℕ} [Fact p.Prime]
    (i j : Fin (PrimeLegendre.mOf p)) :
    originalNegCQ p i j =
      (quadraticChar (ZMod p) (PrimeLegendre.x p i + PrimeLegendre.C p *
        (((j : ℕ) + 1 : ℕ) : ZMod p)) : ℚ) := by
  simpa [originalNegCQ] using originalNegC_entry_cast_rat_eq_quadChar_add_C (p := p) i j

/-- Fallback/product relation: over `ℚ`, the original `C` and auxiliary `-C`
matrices satisfy the skew product relation used by the determinant lemma. -/
theorem originalCQ_mul_transpose_skew_of_mod_four_eq_three {p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hp4 : p % 4 = 3) :
    originalCQ p * (originalNegCQ p)ᵀ + originalNegCQ p * (originalCQ p)ᵀ = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hCcases := PrimeLegendre.C_eq_one_or_eq_neg_one_of_mod_four_eq_three hp hp3 hp4
  ext i j
  rcases hCcases with hC | hC
  · have hsum := PrimeLegendre.lower_add_upper_quadChar_sum_eq_zero_of_mod_four_eq_three
      (p := p) hp hp3 hp4 i j
    calc
      (originalCQ p * (originalNegCQ p)ᵀ + originalNegCQ p * (originalCQ p)ᵀ) i j
          = ((∑ k : Fin (PrimeLegendre.mOf p),
              quadraticChar (ZMod p) (PrimeLegendre.x p i - (((k : ℕ) + 1 : ℕ) : ZMod p)) *
                quadraticChar (ZMod p) (PrimeLegendre.x p j + (((k : ℕ) + 1 : ℕ) : ZMod p))) +
            (∑ k : Fin (PrimeLegendre.mOf p),
              quadraticChar (ZMod p) (PrimeLegendre.x p i + (((k : ℕ) + 1 : ℕ) : ZMod p)) *
                quadraticChar (ZMod p) (PrimeLegendre.x p j - (((k : ℕ) + 1 : ℕ) : ZMod p))) : ℚ) := by
              simp [Matrix.mul_apply, originalCQ, originalNegCQ, Matrix.map_apply,
                originalC_entry_cast_rat_eq_quadChar_sub_C,
                originalNegC_entry_cast_rat_eq_quadChar_add_C, hC]
      _ = 0 := by exact_mod_cast hsum
  · have hsum := PrimeLegendre.lower_add_upper_quadChar_sum_eq_zero_of_mod_four_eq_three
      (p := p) hp hp3 hp4 i j
    have hsum' :
        (∑ k : Fin (PrimeLegendre.mOf p),
            quadraticChar (ZMod p) (PrimeLegendre.x p i + (((k : ℕ) + 1 : ℕ) : ZMod p)) *
              quadraticChar (ZMod p) (PrimeLegendre.x p j - (((k : ℕ) + 1 : ℕ) : ZMod p))) +
          (∑ k : Fin (PrimeLegendre.mOf p),
            quadraticChar (ZMod p) (PrimeLegendre.x p i - (((k : ℕ) + 1 : ℕ) : ZMod p)) *
              quadraticChar (ZMod p) (PrimeLegendre.x p j + (((k : ℕ) + 1 : ℕ) : ZMod p))) = 0 := by
      simpa [add_comm] using hsum
    calc
      (originalCQ p * (originalNegCQ p)ᵀ + originalNegCQ p * (originalCQ p)ᵀ) i j
          = ((∑ k : Fin (PrimeLegendre.mOf p),
              quadraticChar (ZMod p) (PrimeLegendre.x p i + (((k : ℕ) + 1 : ℕ) : ZMod p)) *
                quadraticChar (ZMod p) (PrimeLegendre.x p j - (((k : ℕ) + 1 : ℕ) : ZMod p))) +
            (∑ k : Fin (PrimeLegendre.mOf p),
              quadraticChar (ZMod p) (PrimeLegendre.x p i - (((k : ℕ) + 1 : ℕ) : ZMod p)) *
                quadraticChar (ZMod p) (PrimeLegendre.x p j + (((k : ℕ) + 1 : ℕ) : ZMod p))) : ℚ) := by
              simp [Matrix.mul_apply, originalCQ, originalNegCQ, Matrix.map_apply,
                originalC_entry_cast_rat_eq_quadChar_sub_C,
                originalNegC_entry_cast_rat_eq_quadChar_add_C, hC]
              congr 1
              · apply Finset.sum_congr rfl
                intro k _
                congr 2 <;> ring_nf
              · apply Finset.sum_congr rfl
                intro k _
                congr 2 <;> ring_nf
      _ = 0 := by exact_mod_cast hsum'

/-- Main result: for primes `p ≡ 3 (mod 4)`, the original integer determinant vanishes. -/
theorem original_C_det_eq_zero_of_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp4 : p % 4 = 3) :
    (originalCMatrix p).det = 0 := by
  let A := originalCQ p
  let B := originalNegCQ p
  have hskew : A * Bᵀ + B * Aᵀ = 0 := by
    simpa [A, B] using originalCQ_mul_transpose_skew_of_mod_four_eq_three hp hp3 hp4
  have hB_int : (originalNegCMatrix p).det ≠ 0 :=
    original_negC_det_ne_zero_of_mod_four_eq_three hp hp3 hp4
  have hB : B.det ≠ 0 := by
    intro h
    have hmap := (Int.castRingHom ℚ).map_det (originalNegCMatrix p)
    have hcast : (((originalNegCMatrix p).det : ℤ) : ℚ) = 0 := by
      change (Int.castRingHom ℚ) (originalNegCMatrix p).det = 0
      rw [hmap]
      exact h
    exact hB_int (Int.cast_injective hcast)
  have hodd : Odd (Fintype.card (Fin (PrimeLegendre.mOf p))) := by
    simpa using PrimeLegendre.odd_m_of_mod_four_eq_three hp hp3 hp4
  have hAdet : A.det = 0 :=
    det_zero_of_mul_transpose_skew A B hodd hB hskew
  have hcastA : (((originalCMatrix p).det : ℤ) : ℚ) = 0 := by
    have hmap := (Int.castRingHom ℚ).map_det (originalCMatrix p)
    change (Int.castRingHom ℚ) (originalCMatrix p).det = 0
    rw [hmap]
    exact hAdet
  exact Int.cast_injective hcastA

end FinalDev

/- Final bridge lemmas from FullDev.lean -/
lemma A226163_eq_originalCMatrix_det {n : ℕ} (h_n : 2 ≤ n) :
    A226163 n = (FinalDev.originalCMatrix (Nat.nth Nat.Prime (n - 1))).det := by
  have hnot : ¬ n < 2 := by omega
  unfold A226163
  simp [hnot]
  unfold FinalDev.originalCMatrix FinalDev.originalMatrix PrimeLegendre.mOf
  apply congrArg Matrix.det
  ext i j
  simp [pow_two]


lemma prime_mod_four_eq_one_or_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  omega

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  have hp : p.Prime := by
    dsimp [p]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
  have hp3 : 3 ≤ p := by
    have hidx : 1 ≤ n - 1 := by omega
    have hmono := (Nat.nth_le_nth Nat.infinite_setOf_prime).2 hidx
    dsimp [p]
    simpa [Nat.nth_prime_one_eq_three] using hmono
  have hA : A226163 n = (FinalDev.originalCMatrix p).det := by
    dsimp [p]
    exact A226163_eq_originalCMatrix_det h_n
  constructor
  · intro hzero
    rcases prime_mod_four_eq_one_or_three hp hp3 with hp4 | hp4
    · have hne := FinalDev.original_C_det_ne_zero_of_mod_four_eq_one hp hp3 hp4
      exfalso
      exact hne (by simpa [hA] using hzero)
    · exact hp4
  · intro hp4
    have hz := FinalDev.original_C_det_eq_zero_of_mod_four_eq_three hp hp3 hp4
    simpa [hA] using hz

