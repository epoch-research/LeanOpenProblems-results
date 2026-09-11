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

open Matrix Nat Int Polynomial
open scoped BigOperators
namespace A226163Proof

-- Interpolation at distinct points, followed by a nonvanishing criterion
-- for the matrix of powers of differences.
lemma polynomial_factor {K : Type*} [Field K] {m : ℕ} (y : Fin m → K)
    (hy : Function.Injective y) (f : K[X]) (hd : f.natDegree ≤ m)
    (hr : ∀ j, f.eval (y j) = 0) :
    f = C f.leadingCoeff * ∏ j, (X - C (y j)) := by
  apply eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le
    (monic_prod_X_sub_C y Finset.univ)
  · apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact pairwise_coprime_X_sub_C hy hij
    · intro j _
      exact (dvd_iff_isRoot).mpr (hr j)
  · simpa using hd

lemma det_pow_sub_ne_zero {K : Type*} [Field K] {m : ℕ}
    (x y : Fin m → K) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxm : ∀ i, x i ^ m = 1) (hprod : ∏ i, y i ≠ 1)
    (hchoose : ∀ k ≤ m, (m.choose k : K) ≠ 0) :
    (Matrix.of fun i j => (x i - y j) ^ m).det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.vecMul_injective_iff_isUnit]
  suffices hker : ∀ v : Fin m → K,
      v ᵥ* (Matrix.of fun i j => (x i - y j) ^ m) = 0 → v = 0 by
    intro u v huv
    dsimp only at huv
    have := hker (u - v) (by rw [Matrix.sub_vecMul, huv, sub_self])
    exact sub_eq_zero.mp this
  intro v hv
  let f : K[X] := ∑ i, C (v i) * (X + C (x i)) ^ m
  have hcoeff (k : ℕ) : f.coeff k = (∑ i, v i * x i ^ (m-k)) * (m.choose k : K) := by
    simp [f, finset_sum_coeff, coeff_X_add_C_pow, Finset.sum_mul, mul_assoc]
  have hd : f.natDegree ≤ m := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have hr (j : Fin m) : f.eval (-y j) = 0 := by
    have := congr_fun hv j
    simpa [f, eval_finset_sum, Matrix.vecMul, dotProduct, sub_eq_add_neg, add_comm] using this
  have hf := polynomial_factor (fun j => -y j) (neg_injective.comp hy) f hd hr
  have hlead : f.coeff m = f.leadingCoeff := by
    conv_lhs => rw [hf]
    rw [coeff_C_mul]
    have hh := (monic_prod_X_sub_C (fun j => -y j) Finset.univ).coeff_natDegree
    simp only [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin] at hh
    rw [hh, mul_one]
  have hc : f.coeff m = ∑ i, v i := by simp [hcoeff]
  have hconst : f.eval 0 = ∑ i, v i := by simp [f, eval_finset_sum, hxm]
  have hz : f.leadingCoeff = 0 := by
    have he := congr_arg (Polynomial.eval 0) hf
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X, zero_sub, neg_neg] at he
    rw [hconst, ← hc, hlead] at he
    have he' : f.leadingCoeff * (∏ i, y i - 1) = 0 := by linear_combination -he
    exact (mul_eq_zero.mp he').resolve_right (sub_ne_zero.mpr hprod)
  have hf0 : f = 0 := leadingCoeff_eq_zero.mp hz
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hx
  intro k
  have hh := hcoeff (m - k.val)
  have hk : k.val ≤ m := Nat.le_of_lt k.isLt
  rw [hf0, coeff_zero, Nat.sub_sub_self hk] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_right (hchoose _ (Nat.sub_le _ _))


-- Arithmetic of the representatives 1, ..., (p-1)/2, including Wilson's theorem.
section Half
variable {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)

def half (p m : ℕ) (i : Fin m) : ZMod p := (i.val + 1 : ℕ)

include hp

lemma half_lt (i : Fin m) : i.val + 1 < p := by omega

lemma half_ne_zero (i : Fin m) : half p m i ≠ 0 := by
  intro h
  have hh := congr_arg ZMod.val h
  simp only [half, ZMod.val_natCast_of_lt (half_lt hp i), ZMod.val_zero] at hh
  omega

lemma half_injective : Function.Injective (half p m) := by
  intro i j h
  have hh := congr_arg ZMod.val h
  simp only [half, ZMod.val_natCast_of_lt (half_lt hp i),
    ZMod.val_natCast_of_lt (half_lt hp j)] at hh
  exact Fin.ext (by omega)

lemma half_ne_neg (i j : Fin m) : half p m i ≠ -half p m j := by
  intro h
  have hh : ((i.val+1 + (j.val+1) : ℕ) : ZMod p) = 0 := by
    simpa only [Nat.cast_add, half, add_neg_cancel] using
      (show half p m i + half p m j = 0 by rw [h, neg_add_cancel])
  have hv := congr_arg ZMod.val hh
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
  omega

lemma half_sq_injective : Function.Injective (fun i : Fin m => half p m i ^ 2) := by
  intro i j h
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp h with h | h
  · exact half_injective hp h
  · exact (half_ne_neg hp i j h).elim

lemma half_sq_pow (i : Fin m) : (half p m i ^ 2) ^ m = 1 := by
  rw [← pow_mul, ← show p - 1 = 2*m by omega]
  exact ZMod.pow_card_sub_one_eq_one (half_ne_zero hp i)

omit hp in
lemma prod_half : ∏ i : Fin m, half p m i = (m.factorial : ZMod p) := by
  simp only [half]
  rw [← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => i+1),
    Finset.prod_range_add_one_eq_factorial]

lemma half_factorial_identity : (-1 : ZMod p)^m * (m.factorial : ZMod p)^2 = -1 := by
  have hh := congr_arg (fun n : ℕ => (n : ZMod p))
    (Nat.factorial_mul_descFactorial (n := p-1) (k := m) (by omega))
  have he : p-1-m = m := by omega
  dsimp only at hh
  rw [he, Nat.cast_mul, ZMod.cast_descFactorial (by omega), ZMod.wilsons_lemma] at hh
  linear_combination hh

lemma half_factorial_ne_zero : (m.factorial : ZMod p) ≠ 0 := by
  intro h
  have hh := half_factorial_identity hp
  simp [h] at hh

lemma choose_ne_zero (k : ℕ) (hk : k ≤ m) : (m.choose k : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp
    ((Fact.out : p.Prime).coprime_choose_of_lt (by omega) hk)

lemma char_cast_pow (a : ZMod p) : (quadraticChar (ZMod p) a : ZMod p) = a^m := by
  have hp2 : p ≠ 2 := by omega
  simpa only [ZMod.card, show p/2 = m by omega] using
    quadraticChar_eq_pow_of_char_ne_two' (by simpa only [ZMod.ringChar_zmod_n] using hp2) a

lemma det_char_ne_zero (x y : Fin m → ZMod p)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxm : ∀ i, x i ^ m = 1) (hprod : ∏ i, y i ≠ 1) :
    (Matrix.of fun i j => quadraticChar (ZMod p) (x i - y j)).det ≠ 0 := by
  intro h
  have hh := congr_arg (Int.castRingHom (ZMod p)) h
  rw [RingHom.map_det, map_zero] at hh
  change (Matrix.of fun i j => (quadraticChar (ZMod p) (x i-y j) : ZMod p)).det = 0 at hh
  simp only [char_cast_pow hp] at hh
  exact det_pow_sub_ne_zero x y hx hy hxm hprod (choose_ne_zero hp) hh

lemma det_char_rat_ne_zero (x y : Fin m → ZMod p)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxm : ∀ i, x i ^ m = 1) (hprod : ∏ i, y i ≠ 1) :
    (Matrix.of fun i j => (quadraticChar (ZMod p) (x i - y j) : ℚ)).det ≠ 0 := by
  have hh := det_char_ne_zero hp x y hx hy hxm hprod
  have he := (Int.castRingHom ℚ).map_det (Matrix.of fun i j => quadraticChar (ZMod p) (x i-y j))
  change ((Matrix.of fun i j => quadraticChar (ZMod p) (x i-y j)).det : ℚ) =
    (Matrix.of fun i j => (quadraticChar (ZMod p) (x i-y j) : ℚ)).det at he
  intro hz
  rw [← he] at hz
  exact hh (Int.cast_eq_zero.mp hz)

lemma det_half_add_ne_zero :
    (Matrix.of fun i j : Fin m =>
      (quadraticChar (ZMod p) (half p m i ^ 2 + half p m j ^ 2) : ℚ)).det ≠ 0 := by
  suffices hh : ∏ i : Fin m, -(half p m i ^ 2) ≠ (1 : ZMod p) by
    simpa only [sub_neg_eq_add] using det_char_rat_ne_zero hp
      (fun i => half p m i ^ 2) (fun j => -(half p m j ^ 2))
      (half_sq_injective hp) (neg_injective.comp (half_sq_injective hp)) (half_sq_pow hp) hh
  have hh : ∏ i : Fin m, -(half p m i ^ 2) = (-1 : ZMod p) := by
    simp only [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, Finset.prod_pow, prod_half]
    exact half_factorial_identity hp
  rw [hh]
  intro he
  have hp2 : p ∣ 2 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).mp
    have : (2 : ZMod p) = 0 := by linear_combination -he
    exact this
  have := Nat.le_of_dvd (by decide : 0 < 2) hp2
  have := (Fact.out : p.Prime).two_le
  omega

end Half
-- Selecting columns from commuting skew-symmetric and symmetric matrices.
-- An odd number of skew-symmetric columns makes the determinant vanish.
lemma mixed_det_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℚ) (hA : Aᵀ = -A) (hB : Bᵀ = B)
    (hAB : A*B = B*A) (hdet : B.det ≠ 0)
    (s : ι → Prop) [DecidablePred s]
    (hs : ∏ j, (if s j then (-1 : ℚ) else 1) = -1) :
    (Matrix.of fun i j => if s j then A i j else B i j).det = 0 := by
  let K := B⁻¹ * A
  let P : Matrix ι ι ℚ := diagonal fun j => if s j then 1 else 0
  let D : Matrix ι ι ℚ := diagonal fun j => if s j then -1 else 1
  let N := K * P + (1-P)
  have hBu : IsUnit B.det := hdet.isUnit
  have hcomm : B⁻¹*A = A*B⁻¹ := by
    calc
      B⁻¹*A = B⁻¹*(A*B)*B⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hBu]
      _ = B⁻¹*(B*A)*B⁻¹ := by rw [hAB]
      _ = A*B⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hBu]
  have hK : Kᵀ = -K := by
    simp only [K, transpose_mul, transpose_nonsing_inv, hA, hB, Matrix.neg_mul, Matrix.mul_neg, hcomm]
  have hP : Pᵀ = P := diagonal_transpose _
  have hPD : P*D = -P := by
    ext i j
    by_cases hij : i=j <;> by_cases hj : s j <;>
      simp [P, D, mul_diagonal, diagonal_apply, hij, hj]
  have hQD : (1-P)*D = 1-P := by
    ext i j
    by_cases hij : i=j <;> by_cases hj : s j <;>
      simp [P, D, mul_diagonal, diagonal_apply, Matrix.one_apply, hij, hj]
  have hNt : Nᵀ = 1 + P * (-K-1) := by
    simp only [N, transpose_add, transpose_mul, transpose_sub, transpose_one, hK, hP]
    noncomm_ring
  have hND : N*D = 1 + (-K-1)*P := by
    dsimp only [N]
    rw [Matrix.add_mul, Matrix.mul_assoc, hPD, hQD]
    noncomm_ring
  have hN : N.det = 0 := by
    have he : N.det = N.det * (-1) := by
      calc
        N.det = Nᵀ.det := (det_transpose _).symm
        _ = (1 + P * (-K-1)).det := by rw [hNt]
        _ = (1 + (-K-1)*P).det := det_one_add_mul_comm _ _
        _ = (N*D).det := by rw [hND]
        _ = N.det * (-1) := by rw [det_mul, show D.det = -1 from (det_diagonal).trans hs]
    linarith
  have hM : (Matrix.of fun i j => if s j then A i j else B i j) = B*N := by
    dsimp only [N, K]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hBu]
    ext i j
    simp only [Matrix.add_apply, P, mul_diagonal, Matrix.mul_sub, Matrix.mul_one,
      Matrix.sub_apply, Matrix.of_apply]
    split_ifs <;> ring
  rw [hM, det_mul, hN, mul_zero]

-- Convolution matrices on a finite abelian group commute.
lemma circulant_commute {G R : Type*} [CommGroup G] [Fintype G] [CommRing R]
    (f g : G → R) :
    (Matrix.of fun i j => f (j/i)) * (Matrix.of fun i j => g (j/i)) =
    (Matrix.of fun i j => g (j/i)) * (Matrix.of fun i j => f (j/i)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft (i*j))
  calc
    ∑ k, f (k/i) * g (j/k) = ∑ k, g (e k/i) * f (j/e k) := by
      apply Finset.sum_congr rfl
      intro k _
      have h₁ : e k/i = j/k := by
        calc
          e k/i = (i*i⁻¹)*(j*k⁻¹) := by dsimp [e]; simp only [div_eq_mul_inv]; ac_rfl
          _ = j/k := by simp [div_eq_mul_inv]
      have h₂ : j/e k = k/i := by
        calc
          j/e k = (j*j⁻¹)*(k*i⁻¹) := by
            dsimp [e]; simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]; ac_rfl
          _ = k/i := by simp [div_eq_mul_inv]
      rw [h₁, h₂, mul_comm]
    _ = ∑ k, g (k/i) * f (j/k) := e.sum_comp (fun k => g (k/i) * f (j/k))

lemma det_submatrix_zero_iff {ι κ K : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Field K] (e f : ι ≃ κ) (M : Matrix κ κ K) :
    (M.submatrix e f).det = 0 ↔ M.det = 0 := by
  have hh := Matrix.isUnit_submatrix_equiv (A := M) e f
  simp only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hh
  exact not_iff_not.mp hh

def rootVal {p m : ℕ} (q : rootsOfUnity m (ZMod p)) : ZMod p := q.val.val

-- The nonzero quadratic residues form the group of m-th roots of unity.
-- This realizes the character matrices as convolution matrices.
section Roots
variable {p m : ℕ} [Fact p.Prime] [NeZero m] (hp : p = 2*m+1)

include hp

noncomputable def halfRoot (i : Fin m) : rootsOfUnity m (ZMod p) :=
  rootsOfUnity.mkOfPowEq (half p m i ^ 2) (half_sq_pow hp i)

lemma halfRoot_bijective : Function.Bijective (halfRoot hp) := by
  have hi : Function.Injective (halfRoot hp) := by
    intro i j h
    apply half_sq_injective hp
    exact congr_arg (fun q : rootsOfUnity m (ZMod p) => rootVal q) h
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨hi, le_antisymm (Fintype.card_le_of_injective _ hi) ?_⟩
  simpa using card_rootsOfUnity (ZMod p) m

noncomputable def halfEquiv : Fin m ≃ rootsOfUnity m (ZMod p) :=
  Equiv.ofBijective (halfRoot hp) (halfRoot_bijective hp)

@[simp] lemma halfEquiv_val (i : Fin m) : rootVal (halfEquiv hp i) = half p m i ^ 2 := rfl

lemma root_char (q : rootsOfUnity m (ZMod p)) : quadraticChar (ZMod p) (rootVal q) = 1 := by
  apply (quadraticChar_one_iff_isSquare (Units.ne_zero q.val)).mpr
  apply (ZMod.euler_criterion p (Units.ne_zero q.val)).mpr
  simpa only [show p/2 = m by omega] using (mem_rootsOfUnity' m q.val).mp q.prop

lemma neg_one_ne_one : (-1 : ZMod p) ≠ 1 := by
  intro he
  have hp2 : p ∣ 2 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).mp
    linear_combination -he
  have := Nat.le_of_dvd (by decide : 0 < 2) hp2
  have := (Fact.out : p.Prime).two_le
  omega

lemma char_neg_one (hm : Odd m) : quadraticChar (ZMod p) (-1) = -1 := by
  rw [quadraticChar_eq_pow_of_char_ne_two
    (by rw [ZMod.ringChar_zmod_n]; omega) (neg_ne_zero.mpr one_ne_zero)]
  simp only [ZMod.card, show p/2 = m by omega, hm.neg_one_pow, if_neg (neg_one_ne_one hp)]

lemma root_char_sub_circulant (i j : rootsOfUnity m (ZMod p)) :
    quadraticChar (ZMod p) (rootVal i - rootVal j) =
    quadraticChar (ZMod p) (1 - rootVal (j/i)) := by
  have he : rootVal i - rootVal j =
      rootVal i * (1 - rootVal (j/i)) := by
    simp only [rootVal, Subgroup.coe_div, Units.val_div_eq_div_val]
    field_simp
  rw [he, map_mul, root_char hp, one_mul]

lemma root_char_add_circulant (i j : rootsOfUnity m (ZMod p)) :
    quadraticChar (ZMod p) (rootVal i + rootVal j) =
    quadraticChar (ZMod p) (1 + rootVal (j/i)) := by
  have he : rootVal i + rootVal j =
      rootVal i * (1 + rootVal (j/i)) := by
    simp only [rootVal, Subgroup.coe_div, Units.val_div_eq_div_val]
    field_simp
  rw [he, map_mul, root_char hp, one_mul]

lemma signed_pow (hm : Odd m) (a : ZMod p) (ha : a ≠ 0) :
    (if quadraticChar (ZMod p) a = 1 then a else -a)^m = 1 := by
  rcases quadraticChar_dichotomy ha with hc | hc
  · rw [if_pos hc, ← char_cast_pow hp, hc, Int.cast_one]
  · rw [if_neg (by omega), neg_pow, hm.neg_one_pow, ← char_cast_pow hp, hc]
    norm_num

noncomputable def signedRoot (hm : Odd m) (a : ZMod p) (ha : a ≠ 0) :
    rootsOfUnity m (ZMod p) :=
  rootsOfUnity.mkOfPowEq _ (signed_pow hp hm a ha)

@[simp] lemma signedRoot_val (hm : Odd m) (a : ZMod p) (ha : a ≠ 0) :
    rootVal (signedRoot hp hm a ha) = if quadraticChar (ZMod p) a = 1 then a else -a := rfl

-- Replace each column parameter by its signed quadratic-residue representative.
-- The character product controls the parity of the selected columns.
lemma det_char_zero_of_odd (hm : Odd m) (y : Fin m → ZMod p)
    (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (hneg : ∀ i j, y i ≠ -y j) (hprod : ∏ j, quadraticChar (ZMod p) (y j) = 1) :
    (Matrix.of fun i j : Fin m =>
      (quadraticChar (ZMod p) (half p m i ^ 2 - y j) : ℚ)).det = 0 := by
  classical
  let Q := rootsOfUnity m (ZMod p)
  let A : Matrix Q Q ℚ := Matrix.of fun i j =>
    (quadraticChar (ZMod p) (rootVal i - rootVal j) : ℚ)
  let B : Matrix Q Q ℚ := Matrix.of fun i j =>
    (quadraticChar (ZMod p) (rootVal i + rootVal j) : ℚ)
  have hA : Aᵀ = -A := by
    ext i j
    change (quadraticChar (ZMod p) (rootVal j-rootVal i) : ℚ) =
      -(quadraticChar (ZMod p) (rootVal i-rootVal j) : ℚ)
    have he : rootVal j-rootVal i = (-1 : ZMod p)*(rootVal i-rootVal j) := by ring
    rw [he, map_mul, char_neg_one hp hm]
    push_cast
    ring
  have hB : Bᵀ = B := by ext i j; simp [B, add_comm]
  have hAB : A*B = B*A := by
    have hAc : A = Matrix.of (fun i j : Q =>
        (quadraticChar (ZMod p) (1-rootVal (j/i)) : ℚ)) := by
      ext i j; exact congr_arg (fun z : ℤ => (z : ℚ)) (root_char_sub_circulant hp i j)
    have hBc : B = Matrix.of (fun i j : Q =>
        (quadraticChar (ZMod p) (1+rootVal (j/i)) : ℚ)) := by
      ext i j; exact congr_arg (fun z : ℤ => (z : ℚ)) (root_char_add_circulant hp i j)
    rw [hAc, hBc]
    exact circulant_commute (G := Q) (R := ℚ)
      (fun j => (quadraticChar (ZMod p) (1-rootVal j) : ℚ))
      (fun j => (quadraticChar (ZMod p) (1+rootVal j) : ℚ))
  have hdet : B.det ≠ 0 := by
    rw [← Matrix.det_submatrix_equiv_self (halfEquiv hp) B]
    simpa only [B, Matrix.submatrix, Matrix.of_apply, halfEquiv_val] using det_half_add_ne_zero hp
  let q : Fin m → Q := fun j => signedRoot hp hm (y j) (hy0 j)
  have hq : Function.Injective q := by
    intro i j he
    have hv := congr_arg rootVal he
    change (if quadraticChar (ZMod p) (y i) = 1 then y i else -y i) =
      (if quadraticChar (ZMod p) (y j) = 1 then y j else -y j) at hv
    split_ifs at hv with hi hj hj
    · exact hy hv
    · exact (hneg i j hv).elim
    · exact (hneg j i hv.symm).elim
    · exact hy (neg_injective hv)
  let e : Fin m ≃ Q := Equiv.ofBijective q
    ((Fintype.bijective_iff_injective_and_card q).mpr ⟨hq, (Fintype.card_congr (halfEquiv hp))⟩)
  let s : Q → Prop := fun j => quadraticChar (ZMod p) (y (e.symm j)) = 1
  have hs : ∏ j : Q, (if s j then (-1 : ℚ) else 1) = -1 := by
    rw [← e.prod_comp (fun j => if s j then (-1 : ℚ) else 1)]
    have he (j : Fin m) : (if s (e j) then (-1 : ℚ) else 1) =
        -(quadraticChar (ZMod p) (y j) : ℚ) := by
      simp only [s, Equiv.symm_apply_apply]
      rcases quadraticChar_dichotomy (hy0 j) with hj | hj <;> simp [hj]
    simp only [he, Finset.prod_neg, Finset.card_univ, Fintype.card_fin, hm.neg_one_pow,
      ← Int.cast_prod, hprod, Int.cast_one, mul_one]
  let N : Matrix Q Q ℚ := Matrix.of fun i j => if s j then A i j else B i j
  have hN : N.det = 0 := mixed_det_zero A B hA hB hAB hdet s hs
  have hM : (Matrix.of fun i j : Fin m =>
      (quadraticChar (ZMod p) (half p m i ^ 2 - y j) : ℚ)) =
      N.submatrix (halfEquiv hp) e := by
    ext i j
    have he : rootVal (e j) = if quadraticChar (ZMod p) (y j) = 1 then y j else -y j := rfl
    simp only [Matrix.of_apply, Matrix.submatrix_apply, N, s, Equiv.symm_apply_apply,
      A, B, halfEquiv_val, he]
    split_ifs <;> simp [sub_eq_add_neg]
  rw [hM]
  exact (det_submatrix_zero_iff (halfEquiv hp) e N).mpr hN

end Roots

noncomputable def halfMatrix (p m : ℕ) [Fact p.Prime] : Matrix (Fin m) (Fin m) ℤ :=
  Matrix.of fun i j => quadraticChar (ZMod p)
    (half p m i ^ 2 - (m.factorial : ZMod p) * half p m j)

-- Specialization to the factorial-scaled column parameters.
section FinalAlgebra
variable {p m : ℕ} [Fact p.Prime] [NeZero m] (hp : p = 2*m+1)
include hp

lemma scaled_half_injective :
    Function.Injective (fun i : Fin m => (m.factorial : ZMod p) * half p m i) := by
  intro i j h
  exact half_injective hp ((mul_left_cancel₀ (half_factorial_ne_zero hp)) h)

lemma scaled_half_ne_neg (i j : Fin m) :
    (m.factorial : ZMod p) * half p m i ≠ -((m.factorial : ZMod p) * half p m j) := by
  intro h
  rw [← mul_neg] at h
  exact half_ne_neg hp i j ((mul_left_cancel₀ (half_factorial_ne_zero hp)) h)

lemma prod_scaled_half :
    ∏ i : Fin m, (m.factorial : ZMod p) * half p m i = (m.factorial : ZMod p)^(m+1) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    prod_half, pow_succ]

lemma halfMatrix_det_ne_zero (hm : Even m) : (halfMatrix p m).det ≠ 0 := by
  apply det_char_ne_zero hp (fun i => half p m i ^ 2)
    (fun i => (m.factorial : ZMod p) * half p m i)
    (half_sq_injective hp) (scaled_half_injective hp) (half_sq_pow hp)
  rw [prod_scaled_half hp]
  intro he
  have hC : (m.factorial : ZMod p)^2 = -1 := by
    simpa only [hm.neg_one_pow, one_mul] using half_factorial_identity hp
  have hh := congr_arg (fun a : ZMod p => a^2) he
  dsimp only at hh
  rw [← pow_mul, Nat.mul_comm (m+1) 2, pow_mul, hC, hm.add_one.neg_one_pow, one_pow] at hh
  exact neg_one_ne_one hp hh

lemma halfMatrix_det_zero (hm : Odd m) : (halfMatrix p m).det = 0 := by
  have hC : (m.factorial : ZMod p)^2 = 1 := by
    have hh := half_factorial_identity hp
    rw [hm.neg_one_pow] at hh
    linear_combination -hh
  have hpow : (m.factorial : ZMod p)^(m+1) = 1 := by
    obtain ⟨k, hk⟩ := hm
    rw [show m+1 = 2*(k+1) by omega, pow_mul, hC, one_pow]
  have hprod : ∏ j : Fin m, quadraticChar (ZMod p) ((m.factorial : ZMod p)*half p m j) = 1 := by
    rw [← map_prod, prod_scaled_half hp, hpow, map_one]
  have hh := det_char_zero_of_odd hp hm
    (fun j => (m.factorial : ZMod p)*half p m j)
    (scaled_half_injective hp)
    (fun j => mul_ne_zero (half_factorial_ne_zero hp) (half_ne_zero hp j))
    (scaled_half_ne_neg hp) hprod
  have he := (Int.castRingHom ℚ).map_det (halfMatrix p m)
  change ((halfMatrix p m).det : ℚ) =
    (Matrix.of fun i j => (quadraticChar (ZMod p)
      (half p m i ^ 2 - (m.factorial : ZMod p)*half p m j) : ℚ)).det at he
  exact Int.cast_eq_zero.mp (he.trans hh)

lemma halfMatrix_det_iff : (halfMatrix p m).det = 0 ↔ Odd m := by
  constructor
  · intro h
    rcases Nat.even_or_odd m with hm | hm
    · exact (halfMatrix_det_ne_zero hp hm h).elim
    · exact hm
  · exact halfMatrix_det_zero hp

end FinalAlgebra
end A226163Proof

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  let p := Nat.nth Nat.Prime (n-1)
  have hprime : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _
  letI : Fact p.Prime := ⟨hprime⟩
  have hp3 : 3 ≤ p := by
    have hh := Nat.nth_monotone Nat.infinite_setOf_prime (show 1 ≤ n-1 by omega)
    simpa only [Nat.nth_prime_one_eq_three] using hh
  have hodd : p % 2 = 1 := (hprime.eq_two_or_odd).resolve_left (by omega)
  let m := (p-1)/2
  have hp : p = 2*m+1 := by dsimp [m]; omega
  have hm : m ≠ 0 := by omega
  letI : NeZero m := ⟨hm⟩
  have he : A226163 n = (A226163Proof.halfMatrix p m).det := by
    unfold A226163
    rw [dif_neg (by omega)]
    change (Matrix.of fun i j : Fin m => jacobiSym
      (((i.val+1 : ℕ) : ℤ)*((i.val+1 : ℕ) : ℤ) -
        (m.factorial : ℤ)*((j.val+1 : ℕ) : ℤ)) p).det = _
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [legendreSym, A226163Proof.halfMatrix, A226163Proof.half, pow_two]
  rw [he, A226163Proof.halfMatrix_det_iff hp, Nat.odd_iff]
  change m % 2 = 1 ↔ p % 4 = 3
  omega

theorem oeis_226163_conjecture_0.disproof : ¬ (type_of% @oeis_226163_conjecture_0) := sorry
