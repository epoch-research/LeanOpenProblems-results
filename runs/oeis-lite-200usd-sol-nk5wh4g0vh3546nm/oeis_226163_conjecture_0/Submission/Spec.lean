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


lemma det_eq_zero_of_skew_of_odd
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [NoZeroDivisors R] [Nontrivial R]
    (M : Matrix ι ι R) (hM : M.transpose = -M)
    (htwo : (2 : R) ≠ 0) (hodd : Odd (Fintype.card ι)) : M.det = 0 := by
  have hdet : M.det = (-1 : R) ^ Fintype.card ι * M.det := by
    rw [← Matrix.det_neg, ← hM, Matrix.det_transpose]
  rw [hodd.neg_one_pow] at hdet
  rw [neg_one_mul] at hdet
  have hx : (2 : R) * M.det = 0 := by rw [two_mul, add_eq_zero_iff_eq_neg]; exact hdet
  exact (mul_eq_zero.mp hx).resolve_left htwo

lemma det_select_cols_eq_principal
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (K : Matrix ι ι R) (s : Finset ι) :
    Matrix.det (fun i j ↦ if j ∈ s then K i j else (1 : Matrix ι ι R) i j) =
      Matrix.det (K.submatrix (fun i : {x // x ∈ s} ↦ i.1) (fun i : {x // x ∈ s} ↦ i.1)) := by
  let e := Equiv.sumCompl (fun x ↦ x ∈ s)
  let D : Matrix ι ι R := fun i j ↦ if j ∈ s then K i j else (1 : Matrix ι ι R) i j
  have hre : Matrix.reindex e.symm e.symm D = Matrix.fromBlocks
      (K.submatrix (fun i : {x // x ∈ s} ↦ i.1) (fun i : {x // x ∈ s} ↦ i.1)) 0
      (K.submatrix (fun i : {x // ¬ x ∈ s} ↦ i.1) (fun i : {x // x ∈ s} ↦ i.1)) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Matrix.reindex_apply, Matrix.fromBlocks, D, e, Equiv.sumCompl]
    · have hj : j.1 ∉ s := j.2
      have hij : i.1 ≠ j.1 := fun h ↦ hj (h ▸ i.2)
      simp [Matrix.reindex_apply, Matrix.fromBlocks, D, e, Equiv.sumCompl,
        hj, Matrix.one_apply, hij]
    · simp [Matrix.reindex_apply, Matrix.fromBlocks, D, e, Equiv.sumCompl]
    · have hj : j.1 ∉ s := j.2
      simp [Matrix.reindex_apply, Matrix.fromBlocks, D, e, Equiv.sumCompl,
        hj, Matrix.one_apply, Subtype.ext_iff]
  change D.det = _
  rw [← Matrix.det_reindex_self e.symm D, hre, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

lemma det_select_cols_zero_of_skew
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (K : Matrix ι ι R) (s : Finset ι) (hK : K.transpose = -K)
    (htwo : (2 : R) ≠ 0) (hs : Odd s.card) :
    Matrix.det (fun i j ↦ if j ∈ s then K i j else (1 : Matrix ι ι R) i j) = 0 := by
  rw [det_select_cols_eq_principal]
  refine det_eq_zero_of_skew_of_odd _ ?_ htwo ?_
  · ext i j
    simpa [Matrix.transpose_apply] using congrFun (congrFun hK i.1) j.1
  · simpa using hs

lemma nonsing_inv_mul_skew
    {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (A B : Matrix ι ι F) (hA : A.transpose = -A) (hB : B.transpose = B)
    (hcomm : A * B = B * A) (hdet : B.det ≠ 0) :
    (B⁻¹ * A).transpose = -(B⁻¹ * A) := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have hi_comm : A * B⁻¹ = B⁻¹ * A := by
    calc
      A * B⁻¹ = (B⁻¹ * B) * (A * B⁻¹) := by rw [B.nonsing_inv_mul hu, one_mul]
      _ = B⁻¹ * (B * A) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (A * B) * B⁻¹ := by rw [hcomm]
      _ = B⁻¹ * A := by rw [Matrix.mul_assoc, Matrix.mul_assoc A B B⁻¹, B.mul_nonsing_inv hu, mul_one]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hA, hB]
  simp only [neg_mul]
  rw [hi_comm]

section Paley
variable (p : ℕ) [hp : Fact p.Prime]

local notation "Q" => {x : ZMod p // x ≠ 0 ∧ IsSquare x}
local notation "χ" => quadraticChar (ZMod p)

private noncomputable def paleyA : Matrix Q Q ℚ := fun x y ↦ (χ (x.1 - y.1) : ℚ)
private noncomputable def paleyB : Matrix Q Q ℚ := fun x y ↦ (χ (x.1 + y.1) : ℚ)

private lemma zmod_char_ne_two (h3 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

private lemma quadraticChar_neg (h3 : p % 4 = 3) (x : ZMod p) : χ (-x) = -χ x := by
  rw [show -x = -1 * x by ring, map_mul, quadraticChar_neg_one (zmod_char_ne_two p h3),
    ZMod.card, ZMod.χ₄_nat_three_mod_four h3]
  simp

private lemma paleyA_skew (h3 : p % 4 = 3) : (paleyA p).transpose = -paleyA p := by
  ext x y
  simp only [Matrix.transpose_apply, paleyA, Matrix.neg_apply]
  rw [show y.1 - x.1 = -(x.1 - y.1) by ring, quadraticChar_neg p h3]
  norm_cast

private lemma paleyB_symm : (paleyB p).transpose = paleyB p := by
  ext x y
  simp [paleyB, add_comm]

private noncomputable def qrMulDiv (x y : Q) : Q ≃ Q where
  toFun r := ⟨x.1 * y.1 / r.1, by
    constructor
    · exact div_ne_zero (mul_ne_zero x.2.1 y.2.1) r.2.1
    · exact (x.2.2.mul y.2.2).mul r.2.2.inv⟩
  invFun r := ⟨x.1 * y.1 / r.1, by
    constructor
    · exact div_ne_zero (mul_ne_zero x.2.1 y.2.1) r.2.1
    · exact (x.2.2.mul y.2.2).mul r.2.2.inv⟩
  left_inv r := by
    apply Subtype.ext
    apply (div_eq_iff (div_ne_zero (mul_ne_zero x.2.1 y.2.1) r.2.1)).2
    field_simp [r.2.1]
  right_inv r := by
    apply Subtype.ext
    apply (div_eq_iff (div_ne_zero (mul_ne_zero x.2.1 y.2.1) r.2.1)).2
    field_simp [r.2.1]

private lemma paley_comm (h3 : p % 4 = 3) : paleyA p * paleyB p = paleyB p * paleyA p := by
  ext x y
  simp only [Matrix.mul_apply, paleyA, paleyB]
  rw [← (qrMulDiv p x y).sum_comp (fun r : Q ↦
    (χ (x.1 - r.1) : ℚ) * (χ (r.1 + y.1) : ℚ))]
  apply Finset.sum_congr rfl
  intro r _
  dsimp [qrMulDiv]
  norm_cast
  have hid : (x.1 - x.1 * y.1 / r.1) * (x.1 * y.1 / r.1 + y.1) =
      (x.1 * y.1 / r.1 ^ 2) * ((x.1 + r.1) * (r.1 - y.1)) := by
    field_simp [r.2.1]
  rw [← quadraticCharFun_mul, ← quadraticCharFun_mul, hid, quadraticCharFun_mul]
  have hn : x.1 * y.1 / r.1 ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero x.2.1 y.2.1) (pow_ne_zero _ r.2.1)
  have hs : IsSquare (x.1 * y.1 / r.1 ^ 2) := by
    exact (x.2.2.mul y.2.2).div (by exact ⟨r.1, by ring⟩)
  have hq : quadraticCharFun (ZMod p) (x.1 * y.1 / r.1 ^ 2) = 1 :=
    quadraticChar_one_iff_isSquare hn |>.2 hs
  rw [hq, one_mul]

end Paley

section HalfSquares

private def halfSq {p m : ℕ} [Fact p.Prime] (hpm : p = 2 * m + 1) (i : Fin m) :
    {x : ZMod p // x ≠ 0 ∧ IsSquare x} := by
  let a := i.val + 1
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  exact ⟨(a : ZMod p) ^ 2, pow_ne_zero _ ha0, ⟨(a : ZMod p), by simp [pow_two]⟩⟩

private lemma halfSq_injective {p m : ℕ} [Fact p.Prime] (hpm : p = 2 * m + 1) :
    Function.Injective (halfSq hpm) := by
  intro i j hij
  apply Fin.ext
  have hs : ((i.val + 1 : ℕ) : ZMod p) ^ 2 = ((j.val + 1 : ℕ) : ZMod p) ^ 2 :=
    congrArg Subtype.val hij
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with heq | hneg
  · have hm := (ZMod.eq_iff_modEq_nat p).mp heq
    have := hm.eq_of_lt_of_lt (by omega) (by omega)
    omega
  · have hz : (((i.val + 1) + (j.val + 1) : ℕ) : ZMod p) = 0 := by
      push_cast
      have hneg' : (i.val : ZMod p) + 1 = -((j.val : ZMod p) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hneg
      rw [hneg']
      exact neg_add_cancel _
    rw [ZMod.natCast_eq_zero_iff] at hz
    exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hz)

private lemma halfSq_card_le {p m : ℕ} [Fact p.Prime] (hpm : p = 2 * m + 1) :
    Fintype.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} ≤ m := by
  let Q := {x : ZMod p // x ≠ 0 ∧ IsSquare x}
  let Z : Finset (ZMod p) := Finset.univ.image (fun x : Q ↦ x.1)
  have hcard : Z.card = Fintype.card Q := by
    rw [show Z.card = Finset.univ.card from Finset.card_image_of_injective _
      (fun x y h ↦ Subtype.ext h)]
    simp
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    have hpprime : p.Prime := Fact.out
    have := hpprime.two_le
    omega
  let P : Polynomial (ZMod p) := Polynomial.X ^ m - 1
  have hm : 0 < m := by
    have hpprime : p.Prime := Fact.out
    have := hpprime.two_le
    omega
  have hP : P ≠ 0 := by
    simpa [P] using Polynomial.X_pow_sub_C_ne_zero (R := ZMod p) hm 1
  have hsubset : Z.1 ⊆ P.roots := by
    intro x hx
    have hx' : x ∈ Z := hx
    simp only [Z, Finset.mem_image, Finset.mem_univ, true_and] at hx'
    obtain ⟨q, rfl⟩ := hx'
    rw [Polynomial.mem_roots hP]
    change Polynomial.eval q.1 P = 0
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, sub_eq_zero]
    have hd : (2 * m + 1) / 2 = m := by omega
    simpa [ZMod.card, hpm, hd] using (FiniteField.isSquare_iff hchar q.2.1).mp q.2.2
  rw [← hcard]
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans_eq (by simpa [P] using (Polynomial.natDegree_X_pow_sub_C (R := ZMod p) (n := m) (r := 1)))

private noncomputable def halfSqEquiv {p m : ℕ} [Fact p.Prime] (hpm : p = 2 * m + 1) :
    Fin m ≃ {x : ZMod p // x ≠ 0 ∧ IsSquare x} :=
  Equiv.ofBijective (halfSq hpm) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨halfSq_injective hpm, Nat.le_antisymm
      (Fintype.card_le_of_injective (halfSq hpm) (halfSq_injective hpm))
      (by simpa using (halfSq_card_le hpm))⟩)

end HalfSquares

section PowMatrix

private def halfRev {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m :=
  if h : i.val = 0 then ⟨0, hm⟩ else ⟨m - i.val, by omega⟩

private lemma halfRev_involutive {m : ℕ} (hm : 0 < m) : Function.Involutive (halfRev hm) := by
  intro i
  apply Fin.ext
  by_cases hi : i.val = 0
  · simp [halfRev, hi]
  · have hpos : 0 < m - i.val := Nat.sub_pos_of_lt i.isLt
    simp [halfRev, hi, hpos.ne']
    omega

private def halfRevEquiv {m : ℕ} (hm : 0 < m) : Fin m ≃ Fin m where
  toFun := halfRev hm
  invFun := halfRev hm
  left_inv := halfRev_involutive hm
  right_inv := halfRev_involutive hm

private lemma pow_matrix_factor {F : Type*} [Field F] {m : ℕ} (hm : 0 < m)
    (r : Fin m → F) (hr : ∀ i, r i ^ m = 1) :
    (fun i j ↦ (r i + r j) ^ m : Matrix (Fin m) (Fin m) F) =
      Matrix.vandermonde r * Matrix.of (fun k j ↦
        (if k.val = 0 then (2 : F) else (m.choose k.val : F)) *
          r j ^ (halfRev hm k).val) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vandermonde_apply]
  rw [add_pow]
  rw [Finset.sum_range_succ]
  have hlast : r i ^ m * r j ^ (m - m) * (m.choose m : F) = 1 := by simp [hr]
  rw [hlast]
  have hzero : r i ^ 0 * r j ^ (m - 0) * (m.choose 0 : F) = 1 := by simp [hr]
  have hzmem : (0 : ℕ) ∈ Finset.range m := by simp [hm]
  rw [Finset.sum_eq_add_sum_diff_singleton hzmem, hzero]
  change _ = ∑ x : Fin m, r i ^ x.val *
    ((if x.val = 0 then (2 : F) else (m.choose x.val : F)) * r j ^ (halfRev hm x).val)
  let g : ℕ → F := fun x ↦ if hx : x < m then
    r i ^ x * ((if x = 0 then (2 : F) else (m.choose x : F)) *
      r j ^ (halfRev hm ⟨x, hx⟩).val) else 0
  have hsum : (∑ x : Fin m, r i ^ x.val *
      ((if x.val = 0 then (2 : F) else (m.choose x.val : F)) * r j ^ (halfRev hm x).val)) =
      ∑ x : Fin m, g x.val := by
    apply Finset.sum_congr rfl
    intro x _
    simp [g]
  rw [hsum, Fin.sum_univ_eq_sum_range]
  simp only [g, Finset.sum_ite_irrel, Finset.mem_range, ↓reduceDIte]
  rw [Finset.sum_eq_add_sum_diff_singleton hzmem]
  have hrev0 : (halfRev hm ⟨0, hm⟩).val = 0 := by simp [halfRev]
  simp only [Fin.val_zero, if_pos, zero_pow, hrev0, pow_zero, mul_one]
  have hadd : (1 : F) +
      (∑ x ∈ Finset.range m \ {0}, r i ^ x * r j ^ (m - x) * (m.choose x : F)) + 1 =
      2 + (∑ x ∈ Finset.range m \ {0}, r i ^ x * r j ^ (m - x) * (m.choose x : F)) := by ring
  rw [hadd]
  congr 1
  · simp [hm]
  · apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hx
    have hx0 : x ≠ 0 := hx.2
    have hxm : x < m := hx.1
    simp [g, halfRev, hx0, hxm]
    ring


end PowMatrix

private lemma choose_cast_ne_zero {p m : ℕ} [Fact p.Prime] (hmp : m < p)
    (k : ℕ) (hk : k ≤ m) : (m.choose k : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro hd
  have hfac : p ∣ m.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    simpa [mul_assoc] using dvd_mul_of_dvd_left hd (k.factorial * (m - k).factorial)
  have hpprime : p.Prime := Fact.out
  exact (not_le_of_gt hmp) (hpprime.dvd_factorial.mp hfac)

private lemma pow_matrix_det_ne_zero {p m : ℕ} [Fact p.Prime]
    (hpm : p = 2 * m + 1) (r : Fin m → ZMod p) (hrinj : Function.Injective r)
    (hr : ∀ i, r i ^ m = 1) :
    Matrix.det (fun i j ↦ (r i + r j) ^ m : Matrix (Fin m) (Fin m) (ZMod p)) ≠ 0 := by
  have hm : 0 < m := by
    have hpprime : p.Prime := Fact.out
    have hp2 := hpprime.two_le
    omega
  let V := Matrix.vandermonde r
  let d : Fin m → ZMod p := fun k ↦ if k.val = 0 then 2 else m.choose k.val
  let W : Matrix (Fin m) (Fin m) (ZMod p) :=
    V.transpose.submatrix (halfRevEquiv hm) id
  let C : Matrix (Fin m) (Fin m) (ZMod p) := fun k j ↦
    d k * r j ^ (halfRev hm k).val
  have hC : C = Matrix.diagonal d * W := by
    ext k j
    simp [C, W, d, V, Matrix.diagonal_mul, Matrix.vandermonde_apply,
      halfRevEquiv]
  have hV : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hrinj
  have hW : W.det ≠ 0 := by
    rw [show W = V.transpose.submatrix (halfRevEquiv hm) id from rfl,
      Matrix.det_permute]
    have hsign : ((↑(Equiv.Perm.sign (halfRevEquiv hm)) : ℤ) : ZMod p) ≠ 0 :=
      (IsUnit.map (Int.castRingHom (ZMod p)) (Units.isUnit _)).ne_zero
    exact mul_ne_zero hsign (by simpa using hV)
  have hd : ∀ k, d k ≠ 0 := by
    intro k
    simp only [d]
    split_ifs with hk
    · rw [ne_eq, show (2 : ZMod p) = (2 : ℕ) by norm_num,
        ZMod.natCast_eq_zero_iff]
      intro hdvd
      have hp_le_two := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      omega
    · exact choose_cast_ne_zero (by omega) k.val (Nat.le_of_lt k.isLt)
  have hCdet : C.det ≠ 0 := by
    rw [hC, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hd k) hW
  rw [pow_matrix_factor hm r hr, Matrix.det_mul]
  exact mul_ne_zero hV hCdet

section PaleyBDet
variable (p m : ℕ) [Fact p.Prime]
local notation "Q" => {x : ZMod p // x ≠ 0 ∧ IsSquare x}
local notation "χ" => quadraticChar (ZMod p)

private noncomputable def paleyBInt : Matrix Q Q ℤ := fun x y ↦ χ (x.1 + y.1)

private lemma paleyB_det_ne_zero (hpm : p = 2 * m + 1) : (paleyB p).det ≠ 0 := by
  let e := halfSqEquiv hpm
  let r : Fin m → ZMod p := fun i ↦ (e i).1
  have hrinj : Function.Injective r := by
    intro i j h
    exact e.injective (Subtype.ext h)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    have hpprime : p.Prime := Fact.out
    have := hpprime.two_le
    omega
  have hmdiv : p / 2 = m := by omega
  have hr : ∀ i, r i ^ m = 1 := by
    intro i
    simpa [ZMod.card, hmdiv] using
      (FiniteField.isSquare_iff hchar (e i).2.1).mp (e i).2.2
  have hentry : (Int.castRingHom (ZMod p)).mapMatrix
      (Matrix.reindex e.symm e.symm (paleyBInt p)) =
      (fun i j ↦ (r i + r j) ^ m : Matrix (Fin m) (Fin m) (ZMod p)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.reindex_apply, paleyBInt, r]
    simpa [hmdiv] using quadraticChar_eq_pow_of_char_ne_two' hchar ((e i).1 + (e j).1)
  have hpow := pow_matrix_det_ne_zero hpm r hrinj hr
  have hBI : (paleyBInt p).det ≠ 0 := by
    intro hz
    apply hpow
    rw [← hentry, ← RingHom.map_det, Matrix.det_reindex_self, hz, map_zero]
  have hcast : (Int.castRingHom ℚ).mapMatrix (paleyBInt p) = paleyB p := by
    ext i j
    rfl
  intro hz
  have hdetmap : ((paleyBInt p).det : ℚ) = (paleyB p).det := by
    calc
      ((paleyBInt p).det : ℚ) = ((Int.castRingHom ℚ).mapMatrix (paleyBInt p)).det :=
        RingHom.map_det (Int.castRingHom ℚ) (paleyBInt p)
      _ = (paleyB p).det := congrArg Matrix.det hcast
  have hcne : ((paleyBInt p).det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hBI
  apply hcne
  rw [hdetmap, hz]

end PaleyBDet

section PaleySelected
variable (p m : ℕ) [Fact p.Prime]
local notation "Q" => {x : ZMod p // x ≠ 0 ∧ IsSquare x}
local notation "χ" => quadraticChar (ZMod p)

private lemma paley_selected_zero (hpm : p = 2 * m + 1) (h3 : p % 4 = 3)
    (c : Q → ZMod p) (hc : ∀ j, c j = j.1 ∨ c j = -j.1)
    (S : Finset Q) (hS : ∀ j, j ∈ S ↔ c j = j.1) (hodd : Odd S.card) :
    Matrix.det (fun i j ↦ (χ (i.1 - c j) : ℚ) : Matrix Q Q ℚ) = 0 := by
  let A := paleyA p
  let B := paleyB p
  let K := B⁻¹ * A
  have hA := paleyA_skew p h3
  have hB := paleyB_symm p
  have hcomm := paley_comm p h3
  have hdetB := paleyB_det_ne_zero p m hpm
  have hK : K.transpose = -K := nonsing_inv_mul_skew A B hA hB hcomm hdetB
  let D : Matrix Q Q ℚ := fun i j ↦ if j ∈ S then K i j else (1 : Matrix Q Q ℚ) i j
  have hBD : B * D = (fun i j ↦ (χ (i.1 - c j) : ℚ)) := by
    ext i j
    by_cases hj : j ∈ S
    · have hcj : c j = j.1 := (hS j).mp hj
      have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdetB
      simp only [Matrix.mul_apply, D, hj, if_pos]
      rw [show (∑ x, B i x * K x j) = (B * K) i j by rfl]
      simp only [K, ← Matrix.mul_assoc, B.mul_nonsing_inv hu, one_mul]
      simp [A, paleyA, hcj]
    · have hcj : c j = -j.1 := (hc j).resolve_left (fun h ↦ hj ((hS j).mpr h))
      simp only [Matrix.mul_apply, D, hj, if_false]
      rw [show (∑ x, B i x * (1 : Matrix Q Q ℚ) x j) = (B * (1 : Matrix Q Q ℚ)) i j by rfl,
        mul_one]
      simp [B, paleyB, hcj]
  rw [← hBD, Matrix.det_mul]
  have hD : D.det = 0 := det_select_cols_zero_of_skew K S hK (by norm_num) hodd
  rw [hD, mul_zero]

end PaleySelected

private lemma half_factorial_sq {p m : ℕ} [Fact p.Prime] (hpm : p = 2 * m + 1) :
    ((m.factorial : ℕ) : ZMod p) ^ 2 = (-1 : ZMod p) ^ (m + 1) := by
  let L := Finset.Ico 1 (m + 1)
  let U := Finset.Ico (m + 1) (2 * m + 1)
  have hwhole : Finset.Ico 1 (2 * m + 1) = L ∪ U := by
    ext x
    simp [L, U]
    omega
  have hdis : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro x hxL hxU
    simp [L] at hxL
    simp [U] at hxU
    omega
  have hupper : (∏ x ∈ U, (x : ZMod p)) =
      (-1 : ZMod p) ^ m * (m.factorial : ZMod p) := by
    have hb : (∏ x ∈ L, (-(x : ZMod p))) = ∏ x ∈ U, (x : ZMod p) := by
      apply Finset.prod_bij (fun x _ ↦ 2 * m + 1 - x)
      · intro x hx
        simp [L] at hx
        simp [U]
        omega
      · intro a ha b hb hab
        simp [L] at ha hb
        omega
      · intro b hb
        simp [U] at hb
        refine ⟨2 * m + 1 - b, ?_, by omega⟩
        simp [L]
        omega
      · intro a ha
        have ha' : a ≤ 2 * m + 1 := by
          simp [L] at ha
          omega
        rw [show ((2 * m + 1 - a : ℕ) : ZMod p) = -(a : ZMod p) by
          rw [show (2 * m + 1 : ℕ) = p from hpm.symm,
            Nat.cast_sub (R := ZMod p) (by omega : a ≤ p)]
          simp]
    rw [← hb, Finset.prod_neg]
    have hcard : L.card = m := by simp [L]
    have hlower : (∏ x ∈ L, (x : ZMod p)) = (m.factorial : ZMod p) := by
      simp only [L]
      rw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
    rw [hcard, hlower]
  have hw := ZMod.wilsons_lemma p
  have hpminus : p - 1 = 2 * m := by omega
  rw [hpminus, ← Finset.prod_Ico_id_eq_factorial] at hw
  push_cast at hw
  rw [hwhole, Finset.prod_union hdis] at hw
  have hlower : (∏ x ∈ L, (x : ZMod p)) = (m.factorial : ZMod p) := by
    simp only [L]
    rw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
  rw [hlower, hupper] at hw
  have hweq : (-1 : ZMod p) ^ m * (m.factorial : ZMod p) ^ 2 = -1 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hw
  have hs : ((-1 : ZMod p) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  calc
    (m.factorial : ZMod p) ^ 2 =
        (-1 : ZMod p) ^ m * ((-1 : ZMod p) ^ m * (m.factorial : ZMod p) ^ 2) := by
      rw [← mul_assoc, ← pow_two, hs, one_mul]
    _ = (-1 : ZMod p) ^ m * (-1) := by rw [hweq]
    _ = (-1 : ZMod p) ^ (m + 1) := by rw [pow_succ]

section PairRepresentatives
variable {p : ℕ} [Fact p.Prime]

private noncomputable def pairRep (h3 : p % 4 = 3) (z : ZMod p) (hz : z ≠ 0) :
    {x : ZMod p // x ≠ 0 ∧ IsSquare x} := by
  by_cases hs : IsSquare z
  · exact ⟨z, hz, hs⟩
  · refine ⟨-z, neg_ne_zero.mpr hz, ?_⟩
    have hchar : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      omega
    have hzq : quadraticChar (ZMod p) z = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hs
    have hnq : quadraticChar (ZMod p) (-1) = -1 := by
      rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_three_mod_four h3]
    have hq : quadraticChar (ZMod p) (-z) = 1 := by
      rw [show -z = -1 * z by ring, map_mul, hnq, hzq]
      norm_num
    exact (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hz)).mp hq

private lemma pairRep_eq_or_neg (h3 : p % 4 = 3) (z w : ZMod p) (hz : z ≠ 0) (hw : w ≠ 0)
    (h : (pairRep h3 z hz).1 = (pairRep h3 w hw).1) : z = w ∨ z = -w := by
  simp only [pairRep] at h
  split at h <;> split at h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr (neg_eq_iff_eq_neg.mp h)
  · exact Or.inl (neg_inj.mp h)

end PairRepresentatives

private lemma even_card_neg_one_of_prod_one {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ZMod p)
    (hpgt : 2 < p) (hf : ∀ i, f i = 1 ∨ f i = -1) (hprod : ∏ i, f i = 1) :
    Even (Finset.univ.filter fun i ↦ f i = -1).card := by
  let T := Finset.univ.filter fun i ↦ f i = -1
  have hpoint : ∀ i, f i = if i ∈ T then -1 else 1 := by
    intro i
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact h
    · exact (hf i).resolve_right h
  have hform : (∏ i, f i) = (-1 : ZMod p) ^ T.card := by
    calc
      (∏ i, f i) = ∏ i, (if i ∈ T then (-1 : ZMod p) else 1) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hpoint i
      _ = (-1 : ZMod p) ^ T.card := by simp
  have hp : (-1 : ZMod p) ^ T.card = 1 := hform.symm.trans hprod
  rcases Nat.even_or_odd T.card with he | ho
  · exact he
  · exfalso
    rw [ho.neg_one_pow] at hp
    have hne : (-1 : ZMod p) ≠ 1 := by
      intro h
      have htwo : (2 : ZMod p) = 0 := by
        calc
          (2 : ZMod p) = 1 - (-1) := by ring
          _ = 0 := by rw [h]; ring
      rw [show (2 : ZMod p) = (2 : ℕ) by norm_num, ZMod.natCast_eq_zero_iff] at htwo
      exact (not_le_of_gt hpgt) (Nat.le_of_dvd (by norm_num) htwo)
    exact hne hp

private lemma pairRep_val_eq_or_neg {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3)
    (z : ZMod p) (hz : z ≠ 0) :
    (pairRep h3 z hz).1 = z ∨ (pairRep h3 z hz).1 = -z := by
  simp only [pairRep]
  split <;> simp

private lemma determinant_zero_three_mod_four {p m : ℕ} [Fact p.Prime]
    (hpm : p = 2 * m + 1) (h3 : p % 4 = 3) :
    Matrix.det (fun i j : Fin m ↦
      jacobiSym (((i.val + 1 : ℕ) : ℤ) * (i.val + 1) -
        (m.factorial : ℤ) * (j.val + 1)) p) = 0 := by
  let cz : ZMod p := (m.factorial : ℕ)
  have hm : Odd m := by
    obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := by
      use p / 4
      omega
    use k
    omega
  obtain ⟨k, hmk⟩ := hm

  have hmpos : 0 < m := by omega
  have hcsq : cz ^ 2 = 1 := by
    rw [show cz = (m.factorial : ZMod p) from rfl, half_factorial_sq hpm]
    rw [show m + 1 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  have hczne : cz ≠ 0 := fun h ↦ by rw [h, zero_pow (by norm_num)] at hcsq; exact zero_ne_one hcsq
  let z : Fin m → ZMod p := fun j ↦ cz * (j.val + 1 : ℕ)
  have hz : ∀ j, z j ≠ 0 := by
    intro j
    apply mul_ne_zero hczne
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  let g : Fin m → {x : ZMod p // x ≠ 0 ∧ IsSquare x} := fun j ↦ pairRep h3 (z j) (hz j)
  have hginj : Function.Injective g := by
    intro i j hij
    have hpairs := pairRep_eq_or_neg h3 (z i) (z j) (hz i) (hz j) (congrArg Subtype.val hij)
    apply Fin.ext
    rcases hpairs with heq | hneg
    · have hc : ((i.val + 1 : ℕ) : ZMod p) = (j.val + 1 : ℕ) := by
        apply (mul_left_cancel₀ hczne)
        simpa [z] using heq
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
      have hijval := hmod.eq_of_lt_of_lt (by omega) (by omega)
      omega
    · have hc : ((i.val + 1 : ℕ) : ZMod p) = -((j.val + 1 : ℕ) : ZMod p) := by
        have hmul : cz * ((i.val + 1 : ℕ) : ZMod p) =
            cz * (-((j.val + 1 : ℕ) : ZMod p)) := by
          calc
            _ = -(cz * ((j.val + 1 : ℕ) : ZMod p)) := by simpa [z] using hneg
            _ = _ := by ring
        exact mul_left_cancel₀ hczne hmul
      have hzero : (((i.val + 1) + (j.val + 1) : ℕ) : ZMod p) = 0 := by
        push_cast
        have hc' : (i.val : ZMod p) + 1 = -((j.val : ZMod p) + 1) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hc
        rw [hc']
        ring
      rw [ZMod.natCast_eq_zero_iff] at hzero
      exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hzero)
  let e : Fin m ≃ {x : ZMod p // x ≠ 0 ∧ IsSquare x} :=
    Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).2
      ⟨hginj, Fintype.card_congr (halfSqEquiv hpm)⟩)
  let c : {x : ZMod p // x ≠ 0 ∧ IsSquare x} → ZMod p := fun q ↦ z (e.symm q)
  have hc : ∀ q, c q = q.1 ∨ c q = -q.1 := by
    intro q
    have hg : g (e.symm q) = q := e.apply_symm_apply q
    have hp := pairRep_val_eq_or_neg h3 (z (e.symm q)) (hz (e.symm q))
    rcases hp with hp | hp
    · left
      change z (e.symm q) = q.1
      rw [← hp]
      exact congrArg Subtype.val hg
    · right
      change z (e.symm q) = -q.1
      have hp' : z (e.symm q) = -(pairRep h3 (z (e.symm q)) (hz (e.symm q))).1 := by
        simpa using (congrArg Neg.neg hp).symm
      exact hp'.trans (congrArg Neg.neg (congrArg Subtype.val hg))
  let S : Finset {x : ZMod p // x ≠ 0 ∧ IsSquare x} :=
    Finset.univ.filter fun q ↦ c q = q.1
  have hS : ∀ q, q ∈ S ↔ c q = q.1 := by simp [S]
  let f : {x : ZMod p // x ≠ 0 ∧ IsSquare x} → ZMod p := fun q ↦
    quadraticChar (ZMod p) (c q)
  have hf : ∀ q, f q = 1 ∨ f q = -1 := by
    intro q
    have hcn : c q ≠ 0 := by
      rcases hc q with h | h <;> rw [h] <;> simp [q.2.1]
    rcases quadraticChar_dichotomy hcn with h | h
    · left
      change ((quadraticChar (ZMod p) (c q) : ℤ) : ZMod p) = 1
      rw [h]
      norm_num
    · right
      change ((quadraticChar (ZMod p) (c q) : ℤ) : ZMod p) = -1
      rw [h]
      norm_num
  have hzprod : ∏ q, c q = 1 := by
    rw [show (∏ q, c q) = ∏ j : Fin m, z j by
      simpa [c] using (e.symm.prod_comp z)]
    have hprodcast : (∏ j : Fin m, ((j.val + 1 : ℕ) : ZMod p)) = cz := by
      rw [Fin.prod_univ_eq_prod_range (fun x : ℕ ↦ ((x + 1 : ℕ) : ZMod p)) m]
      rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
    rw [show (∏ j : Fin m, z j) = cz ^ m *
        ∏ j : Fin m, ((j.val + 1 : ℕ) : ZMod p) by
      simp only [z, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]]
    rw [hprodcast, ← pow_succ]
    rw [show m + 1 = 2 * (k + 1) by omega, pow_mul, hcsq]
    simp
  have hfprod : ∏ q, f q = 1 := by
    rw [show (∏ q, f q) = quadraticChar (ZMod p) (∏ q, c q) by
      simp [f, map_prod]]
    rw [hzprod]
    change ((quadraticChar (ZMod p) (1 : ZMod p) : ℤ) : ZMod p) = 1
    rw [map_one]
    norm_num
  have hpgt : 2 < p := by omega
  have hTeven := even_card_neg_one_of_prod_one f hpgt hf hfprod
  let T := Finset.univ.filter fun q ↦ f q = -1
  have hST : S ∪ T = Finset.univ := by
    ext q
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hq : q ∈ S
    · exact Or.inl hq
    · right
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      have hcneg := (hc q).resolve_left (fun h ↦ hq ((hS q).mpr h))
      have hns : ¬ IsSquare (c q) := by
        intro hsquare
        have hcn : c q ≠ 0 := by rw [hcneg]; exact neg_ne_zero.mpr q.2.1
        have hrep : (pairRep h3 (c q) hcn).1 = c q := by
          simp [pairRep, hsquare]
        have heq : g (e.symm q) = q := e.apply_symm_apply q
        have heqv : (pairRep h3 (c q) hcn).1 = q.1 := by
          simpa [g, c] using congrArg Subtype.val heq
        have : c q = q.1 := hrep.symm.trans heqv
        exact hq ((hS q).mpr this)
      have hi : quadraticChar (ZMod p) (c q) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hns
      change ((quadraticChar (ZMod p) (c q) : ℤ) : ZMod p) = -1
      rw [hi]
      norm_num
  have hdis : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro q hqS hqT
    have hcq := (hS q).mp hqS
    have hqi : quadraticChar (ZMod p) q.1 = 1 :=
      (quadraticChar_one_iff_isSquare q.2.1).mpr q.2.2
    have hfq : f q = 1 := by
      change ((quadraticChar (ZMod p) (c q) : ℤ) : ZMod p) = 1
      rw [hcq, hqi]
      norm_num
    have hneg : f q = -1 := by simpa [T] using hqT
    have hone : (1 : ZMod p) ≠ -1 := by
      intro he
      have htwo : (2 : ZMod p) = 0 := by
        calc (2 : ZMod p) = 1 - (-1) := by ring
             _ = 0 := by rw [← he]; ring
      rw [show (2 : ZMod p) = (2 : ℕ) by norm_num, ZMod.natCast_eq_zero_iff] at htwo
      exact (not_le_of_gt hpgt) (Nat.le_of_dvd (by norm_num) htwo)
    exact hone (hfq.symm.trans hneg)
  have hcard : S.card + T.card = m := by
    rw [← Finset.card_union_of_disjoint hdis, hST, Finset.card_univ]
    simpa using Fintype.card_congr (halfSqEquiv hpm).symm
  have hSodd : Odd S.card := by
    change Even T.card at hTeven

    rcases hTeven with ⟨a, ha⟩
    have hab : a ≤ k := by omega
    use k - a
    omega
  have hzero := paley_selected_zero p m hpm h3 c hc S hS hSodd
  -- Reindexing the rows and columns gives the original matrix.
  let Mq : Matrix {x : ZMod p // x ≠ 0 ∧ IsSquare x}
      {x : ZMod p // x ≠ 0 ∧ IsSquare x} ℤ := fun q r ↦
    quadraticChar (ZMod p) (q.1 - c r)
  have hMq : Mq.det = 0 := by
    have hcast : (Int.castRingHom ℚ).mapMatrix Mq =
        (fun q r ↦ (quadraticChar (ZMod p) (q.1 - c r) : ℚ)) := by rfl
    have hmapped : ((Int.castRingHom ℚ).mapMatrix Mq).det = 0 := by
      rw [hcast]
      exact hzero
    have hcastdet : ((Mq.det : ℤ) : ℚ) = 0 := by
      calc
        ((Mq.det : ℤ) : ℚ) = ((Int.castRingHom ℚ).mapMatrix Mq).det :=
          RingHom.map_det (Int.castRingHom ℚ) Mq
        _ = 0 := hmapped
    exact Int.cast_eq_zero.mp hcastdet
  let eRow := halfSqEquiv hpm
  have hre : Matrix.det (Matrix.reindex eRow.symm e.symm Mq) = 0 := by
    rw [Matrix.det_reindex, hMq, mul_zero]
  have hmat : (fun i j : Fin m ↦
      jacobiSym (((i.val + 1 : ℕ) : ℤ) * (i.val + 1) -
        (m.factorial : ℤ) * (j.val + 1)) p) =
      Matrix.reindex eRow.symm e.symm Mq := by
    ext i j
    simp [Matrix.reindex_apply, Mq, eRow, e, g, c, z, halfSqEquiv, halfSq]
    rw [← jacobiSym.legendreSym.to_jacobiSym p]
    change quadraticChar (ZMod p) _ = quadraticChar (ZMod p) _
    congr 1
    push_cast
    ring
  rw [hmat]
  exact hre

section GeneralPowMatrix

private lemma sub_pow_matrix_factor {F : Type*} [Field F] {m : ℕ} (hm : 0 < m)
    (x y : Fin m → F) (hx : ∀ i, x i ^ m = 1) :
    (fun i j ↦ (x i - y j) ^ m : Matrix (Fin m) (Fin m) F) =
      Matrix.vandermonde x * Matrix.of (fun k j ↦
        if k.val = 0 then 1 + (-y j) ^ m
        else (m.choose k.val : F) * (-y j) ^ (m - k.val)) := by
  ext i j
  rw [show x i - y j = x i + (-y j) by ring, add_pow, Finset.sum_range_succ]
  have hlast : x i ^ m * (-y j) ^ (m - m) * (m.choose m : F) = 1 := by simp [hx]
  rw [hlast]
  change (∑ k ∈ Finset.range m, x i ^ k * (-y j) ^ (m - k) *
    (m.choose k : F)) + 1 = ∑ k : Fin m, x i ^ k.val *
      (if k.val = 0 then 1 + (-y j) ^ m
       else (m.choose k.val : F) * (-y j) ^ (m - k.val))

  let g : ℕ → F := fun k ↦ if hk : k < m then x i ^ k *
    (if k = 0 then 1 + (-y j) ^ m
      else (m.choose k : F) * (-y j) ^ (m - k)) else 0
  have hsum : (∑ k : Fin m, x i ^ k.val *
      (if k.val = 0 then 1 + (-y j) ^ m
       else (m.choose k.val : F) * (-y j) ^ (m - k.val))) = ∑ k : Fin m, g k.val := by
    apply Finset.sum_congr rfl
    intro k _
    simp [g]
  rw [hsum, Fin.sum_univ_eq_sum_range]
  simp only [g]
  have hzmem : (0 : ℕ) ∈ Finset.range m := by simp [hm]
  rw [Finset.sum_eq_add_sum_diff_singleton hzmem]
  rw [Finset.sum_eq_add_sum_diff_singleton hzmem]
  simp only [if_pos hm, if_pos, pow_zero, one_mul, Nat.choose_zero_right,
    Nat.cast_one]
  ring_nf
  congr 1
  · simp [hm]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hk
    have hk0 : k ≠ 0 := hk.2
    have hkm : k < m := hk.1
    simp [hkm, hk0]
    ring

private def lastCycle {m : ℕ} (hm : 0 < m) : Equiv.Perm (Fin m) :=
  (⟨m - 1, Nat.sub_lt hm (by omega)⟩ : Fin m).cycleRange

private lemma halfRev_lastCycle {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (halfRev hm (lastCycle hm i)).val = m - 1 - i.val := by
  haveI : NeZero m := ⟨hm.ne'⟩
  let l : Fin m := ⟨m - 1, Nat.sub_lt hm (by omega)⟩
  by_cases hi : i.val < m - 1
  · have hil : i < l := hi
    rw [show lastCycle hm i = i + 1 by
      simp only [lastCycle]
      exact Fin.cycleRange_of_lt hil]
    have hm2 : 1 < m := by omega
    let one : Fin m := ⟨1, hm2⟩
    have hione : i + 1 = i + one := by
      apply Fin.ext
      simp [Fin.val_add, one, Nat.mod_eq_of_lt hm2]
    have hadd : (i + 1).val = i.val + 1 := by
      rw [hione]
      exact Fin.val_add_eq_of_add_lt (by simp [one]; omega)
    have hne : (i + 1).val ≠ 0 := by omega
    simp [halfRev, hne, hadd]
    omega

  · have hieq : i = l := by
      apply Fin.ext
      change i.val = m - 1
      omega
    subst i
    have hcy : lastCycle hm l = (⟨0, hm⟩ : Fin m) := by
      change (⟨m - 1, Nat.sub_lt hm (by omega)⟩ : Fin m).cycleRange l = _
      have hl : l = (⟨m - 1, Nat.sub_lt hm (by omega)⟩ : Fin m) := by
        apply Fin.ext
        rfl
      rw [hl, Fin.cycleRange_self]
      apply Fin.ext
      rfl
    rw [hcy]
    change (halfRev hm ⟨0, hm⟩).val = m - 1 - l.val
    simp [halfRev, l]

private lemma det_general_coeff {F : Type*} [Field F] {m : ℕ} (hm : 0 < m)
    (y : Fin m → F) (hy : Function.Injective y)
    (hd : ∀ k : Fin m, k.val ≠ 0 → (m.choose k.val : F) ≠ 0)
    (hprod : ∏ j, y j ≠ 1) :
    Matrix.det (Matrix.of (fun k j ↦
      if k.val = 0 then 1 + (-y j) ^ m
      else (m.choose k.val : F) * (-y j) ^ (m - k.val))) ≠ 0 := by
  let z : Fin m → F := fun j ↦ -y j
  let d : Fin m → F := fun k ↦ if k.val = 0 then 1 else m.choose k.val
  let P : Matrix (Fin m) (Fin m) F := fun k j ↦ z j ^ (halfRev hm k).val
  let u : Fin m → F := fun j ↦ z j ^ m
  let i0 : Fin m := ⟨0, hm⟩

  let D : Matrix (Fin m) (Fin m) F := P.updateRow i0 (P i0 + u)
  let C : Matrix (Fin m) (Fin m) F := Matrix.diagonal d * D
  have hP : P.det ≠ 0 := by
    have hz : Function.Injective z := fun a b h ↦ hy (neg_inj.mp h)
    have hv : (Matrix.vandermonde z).det ≠ 0 :=
      Matrix.det_vandermonde_ne_zero_iff.mpr hz
    rw [show P = (Matrix.vandermonde z).transpose.submatrix (halfRevEquiv hm) id by
      ext i j
      simp [P, Matrix.vandermonde_apply, halfRevEquiv]]
    rw [Matrix.det_permute]
    exact mul_ne_zero
      (IsUnit.ne_zero (IsUnit.map (Int.castRingHom F) (Units.isUnit _))) (by simpa using hv)
  have hC : C = Matrix.of (fun k j ↦
      if k.val = 0 then 1 + (-y j) ^ m
      else (m.choose k.val : F) * (-y j) ^ (m - k.val)) := by
    ext k j
    by_cases hk : k.val = 0
    · have hki : k = i0 := Fin.ext hk
      subst k
      simp [C, D, P, u, d, z, i0, Matrix.diagonal_mul, halfRev]
    · have hki : k ≠ i0 := fun h ↦ hk (congrArg Fin.val h)
      simp [C, D, P, u, d, z, i0, Matrix.diagonal_mul, halfRev, hk, hki]
  have hD : D.det = P.det * (1 - ∏ j, y j) := by
    have hupdate : D.det = P.det + (P.updateRow i0 u).det := by
      rw [show D = P.updateRow i0 (P i0 + u) from rfl, Matrix.det_updateRow_add,
        Matrix.updateRow_eq_self]
    rw [hupdate]
    let R : Matrix (Fin m) (Fin m) F := P.submatrix (lastCycle hm) id
    have hE : P.updateRow i0 u = R * Matrix.diagonal z := by
      ext i j
      by_cases hi : i.val = 0
      · have hii : i = i0 := Fin.ext hi
        subst i
        simp only [Matrix.updateRow_self, u, Matrix.mul_diagonal, R,
          Matrix.submatrix_apply, id_eq, P]
        rw [halfRev_lastCycle hm]
        rw [← pow_succ]
        congr 1
        omega
      · have hii : i ≠ i0 := fun h ↦ hi (congrArg Fin.val h)
        simp only [Matrix.updateRow_ne hii, Matrix.mul_diagonal, R,
          Matrix.submatrix_apply, id_eq, P]
        rw [halfRev_lastCycle hm]
        rw [← pow_succ]
        congr 1
        simp [halfRev, hi]
        omega
    rw [hE, Matrix.det_mul, Matrix.det_diagonal]
    have hR : R.det = ((-1 : F) ^ (m - 1)) * P.det := by
      rw [show R = P.submatrix (lastCycle hm) id from rfl, Matrix.det_permute]
      have hs := Fin.sign_cycleRange (⟨m - 1, Nat.sub_lt hm (by omega)⟩ : Fin m)
      simp only [lastCycle]
      rw [hs]
      norm_cast
    rw [hR]
    have hzprod : (∏ j, z j) = (-1 : F) ^ m * ∏ j, y j := by
      simp [z, Finset.prod_neg]
    rw [hzprod]
    have hodd : Odd (m - 1 + m) := by
      use m - 1
      omega
    have hsign : (-1 : F) ^ (m - 1) * (-1 : F) ^ m = -1 := by
      rw [← pow_add, hodd.neg_one_pow]
    rw [show (-1 : F) ^ (m - 1) * P.det * ((-1 : F) ^ m * ∏ j, y j) =
      (((-1 : F) ^ (m - 1)) * (-1 : F) ^ m) * P.det * ∏ j, y j by ring,
      hsign]
    ring
  rw [← hC, show C = Matrix.diagonal d * D from rfl, Matrix.det_mul,
    Matrix.det_diagonal, hD]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro k _
    simp only [d]
    split_ifs with hk
    · exact one_ne_zero
    · exact hd k hk
  · exact mul_ne_zero hP (sub_ne_zero.mpr hprod.symm)

end GeneralPowMatrix

private lemma determinant_ne_zero_one_mod_four {p m : ℕ} [Fact p.Prime]
    (hpm : p = 2 * m + 1) (h1 : p % 4 = 1) :
    Matrix.det (fun i j : Fin m ↦
      jacobiSym (((i.val + 1 : ℕ) : ℤ) * (i.val + 1) -
        (m.factorial : ℤ) * (j.val + 1)) p) ≠ 0 := by
  let cz : ZMod p := (m.factorial : ℕ)
  have hpgt : 2 < p := by
    have hpprime : p.Prime := Fact.out
    have := hpprime.two_le
    omega
  have hmEven : Even m := by
    obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := by
      use p / 4
      omega
    use k
    omega
  obtain ⟨k, hmk⟩ := hmEven
  have hmpos : 0 < m := by omega
  have hcsq : cz ^ 2 = -1 := by
    rw [show cz = (m.factorial : ZMod p) from rfl, half_factorial_sq hpm]
    rw [show m + 1 = 2 * k + 1 by omega, pow_succ, pow_mul]
    norm_num
  have hminus : (-1 : ZMod p) ≠ 1 := by
    intro h
    have htwo : (2 : ZMod p) = 0 := by
      calc (2 : ZMod p) = 1 - (-1) := by ring
           _ = 0 := by rw [h]; ring
    rw [show (2 : ZMod p) = (2 : ℕ) by norm_num, ZMod.natCast_eq_zero_iff] at htwo
    exact (not_le_of_gt hpgt) (Nat.le_of_dvd (by norm_num) htwo)
  have hczne : cz ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hcsq
    exact (neg_ne_zero.mpr one_ne_zero) hcsq.symm
  let x : Fin m → ZMod p := fun i ↦ ((i.val + 1 : ℕ) : ZMod p) ^ 2
  let y : Fin m → ZMod p := fun j ↦ cz * ((j.val + 1 : ℕ) : ZMod p)
  have hxinj : Function.Injective x := by
    intro i j hij
    have he : halfSq hpm i = halfSq hpm j := Subtype.ext hij
    exact halfSq_injective hpm he
  have hyinj : Function.Injective y := by
    intro i j hij
    have hc : ((i.val + 1 : ℕ) : ZMod p) = ((j.val + 1 : ℕ) : ZMod p) :=
      mul_left_cancel₀ hczne (by simpa [y] using hij)
    have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
    have hv := hmod.eq_of_lt_of_lt (by omega) (by omega)
    exact Fin.ext (by omega)
  have hxpow : ∀ i, x i ^ m = 1 := by
    intro i
    have hi0 : (((i.val + 1 : ℕ) : ZMod p)) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hs : IsSquare (x i) := ⟨((i.val + 1 : ℕ) : ZMod p), by simp [x, pow_two]⟩
    have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
    have hd : p / 2 = m := by omega
    change ((((i.val + 1 : ℕ) : ZMod p) ^ 2) ^ m) = 1
    simpa [ZMod.card, hd] using
      (FiniteField.isSquare_iff hchar (pow_ne_zero _ hi0)).mp hs
  have hyprod : (∏ j, y j) = cz ^ (m + 1) := by
    have hprodcast : (∏ j : Fin m, ((j.val + 1 : ℕ) : ZMod p)) = cz := by
      rw [Fin.prod_univ_eq_prod_range (fun a : ℕ ↦ ((a + 1 : ℕ) : ZMod p)) m]
      rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
    rw [show (∏ j : Fin m, y j) = cz ^ m *
        ∏ j : Fin m, ((j.val + 1 : ℕ) : ZMod p) by
      simp [y, Finset.prod_mul_distrib]]
    rw [hprodcast, pow_succ]
  have hyprodne : ∏ j, y j ≠ 1 := by
    rw [hyprod]
    intro he
    have he' : (-1 : ZMod p) ^ k * cz = 1 := by
      calc
        (-1 : ZMod p) ^ k * cz = (cz ^ 2) ^ k * cz := by rw [← hcsq]
        _ = cz ^ (m + 1) := by rw [← pow_mul, pow_succ]; congr 2 <;> omega
        _ = 1 := he
    have hsignsq : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by
      rw [← pow_mul]
      simp
    have hczone : cz ^ 2 = 1 := by
      calc
        cz ^ 2 = (((-1 : ZMod p) ^ k) * cz) ^ 2 := by
          rw [mul_pow, hsignsq, one_mul]
        _ = 1 := by rw [he']; norm_num
    rw [hcsq] at hczone
    exact hminus hczone
  let Cmat : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.of (fun a b ↦
    if a.val = 0 then 1 + (-y b) ^ m
    else (m.choose a.val : ZMod p) * (-y b) ^ (m - a.val))
  have hC : Cmat.det ≠ 0 := det_general_coeff hmpos y hyinj
    (fun a ha ↦ choose_cast_ne_zero (by omega) a.val (Nat.le_of_lt a.isLt)) hyprodne
  have hV : (Matrix.vandermonde x).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hxinj
  have hpow : Matrix.det (fun i j ↦ (x i - y j) ^ m :
      Matrix (Fin m) (Fin m) (ZMod p)) ≠ 0 := by
    rw [sub_pow_matrix_factor hmpos x y hxpow, Matrix.det_mul]
    exact mul_ne_zero hV hC
  let Mint : Matrix (Fin m) (Fin m) ℤ := fun i j ↦
    jacobiSym (((i.val + 1 : ℕ) : ℤ) * (i.val + 1) -
      (m.factorial : ℤ) * (j.val + 1)) p
  have hmap : (Int.castRingHom (ZMod p)).mapMatrix Mint =
      (fun i j ↦ (x i - y j) ^ m : Matrix (Fin m) (Fin m) (ZMod p)) := by
    ext i j
    change ((jacobiSym (((i.val + 1 : ℕ) : ℤ) * (i.val + 1) -
      (m.factorial : ℤ) * (j.val + 1)) p : ℤ) : ZMod p) = _
    rw [← jacobiSym.legendreSym.to_jacobiSym p]
    rw [legendreSym.eq_pow]
    have hd : p / 2 = m := by omega
    rw [hd]
    simp [x, y, cz]
    ring
  intro hzero
  apply hpow
  rw [← hmap, ← RingHom.map_det, hzero, map_zero]


/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  let p := Nat.nth Nat.Prime (n - 1)
  let m := (p - 1) / 2
  have hp : p.Prime := Nat.prime_nth_prime (n - 1)
  letI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have hb := Nat.add_two_le_nth_prime (n - 1)
    omega
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left (by omega)
  have hpm : p = 2 * m + 1 := by
    dsimp [m]
    omega
  have hA : A226163 n = Matrix.det (fun i j : Fin m ↦
      jacobiSym (((i.val + 1 : ℕ) : ℤ) * (i.val + 1) -
        (m.factorial : ℤ) * (j.val + 1)) p) := by
    simp only [A226163, dif_neg (not_lt_of_ge h_n)]
    dsimp [p, m]
  rw [hA]
  change Matrix.det (fun i j : Fin m ↦
      jacobiSym (((i.val + 1 : ℕ) : ℤ) * (i.val + 1) -
        (m.factorial : ℤ) * (j.val + 1)) p) = 0 ↔ p % 4 = 3
  constructor
  · intro hz
    have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
      have hlt := Nat.mod_lt p (by omega : 0 < 4)
      have hpar : p % 4 % 2 = 1 := by omega
      omega
    rcases hmod with h1 | h3
    · exact False.elim ((determinant_ne_zero_one_mod_four hpm h1) hz)
    · exact h3
  · intro h3
    exact determinant_zero_three_mod_four hpm h3
