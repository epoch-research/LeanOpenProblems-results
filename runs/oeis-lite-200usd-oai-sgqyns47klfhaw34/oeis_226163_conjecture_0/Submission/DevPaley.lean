import FormalConjectures.Util.ProblemImports

open Matrix Polynomial
open scoped BigOperators

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R] [CharZero R]

lemma det_mixed_identity_principal' {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (p : n → Prop) [DecidablePred p]
    (T : Matrix n n R) :
    (Matrix.det (fun i j : n => if p j then T i j else if i = j then (1 : R) else 0)) =
      Matrix.det (T.submatrix (fun x : {i // p i} => (x : n)) (fun x : {i // p i} => (x : n))) := by
  let M : Matrix n n R := fun i j => if p j then T i j else if i = j then (1 : R) else 0
  let e : ({i : n // p i} ⊕ {i : n // ¬ p i}) ≃ n := Equiv.sumCompl p
  have hdet := (Matrix.det_submatrix_equiv_self e M).symm
  change M.det = _
  rw [hdet]
  let N : Matrix ({i : n // p i} ⊕ {i : n // ¬ p i}) ({i : n // p i} ⊕ {i : n // ¬ p i}) R := M.submatrix e e
  change Matrix.det N = _
  have hN : Matrix.fromBlocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂ = N :=
    Matrix.fromBlocks_toBlocks N
  rw [← hN]
  have h12 : N.toBlocks₁₂ = 0 := by
    ext i j
    simp [Matrix.toBlocks₁₂, N, Matrix.submatrix, M, e, j.2,
      Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
  have h22 : N.toBlocks₂₂ = 1 := by
    ext i j
    rw [Matrix.one_apply]
    simp [Matrix.toBlocks₂₂, N, Matrix.submatrix, M, e, j.2,
      Equiv.sumCompl_apply_inr]
  have h11 : N.toBlocks₁₁ = T.submatrix (fun x : {i // p i} => (x : n)) (fun x : {i // p i} => (x : n)) := by
    ext i j
    simp [Matrix.toBlocks₁₁, N, Matrix.submatrix, M, e, j.2,
      Equiv.sumCompl_apply_inl]
  rw [h12, Matrix.det_fromBlocks_zero₁₂, h22, Matrix.det_one, mul_one, h11]

lemma det_eq_zero_of_transpose_eq_neg_odd'' {m R : Type*} [Fintype m] [DecidableEq m]
    [CommRing R] [NoZeroDivisors R] [CharZero R]
    (M : Matrix m m R) (hM : Mᵀ = (-1 : R) • M) (hodd : Odd (Fintype.card m)) :
    M.det = 0 := by
  have hdet : M.det = (((-1 : R) • M).det) := by
    rw [← hM, Matrix.det_transpose]
  have hneg : (((-1 : R) • M).det) = (-1 : R) ^ Fintype.card m * M.det := by
    simpa using Matrix.det_smul M (-1 : R)
  rw [hneg] at hdet
  have hpow : (-1 : R) ^ Fintype.card m = -1 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    simp [pow_succ, pow_mul]
  rw [hpow] at hdet
  have hdneg : M.det = -M.det := by simpa using hdet
  have hadd : M.det + M.det = 0 := by
    nth_rewrite 2 [hdneg]
    exact add_neg_cancel M.det
  have htwo : (2 : R) * M.det = 0 := by
    simpa [two_mul] using hadd
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

lemma mixed_column_det_zero' {K : Type*} [Field K] [CharZero K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : n → Prop) [DecidablePred p]
    (A B : Matrix n n K) (hBunit : IsUnit B.det)
    (hTskew : (B⁻¹ * A)ᵀ = (-1 : K) • (B⁻¹ * A))
    (hodd : Odd (Fintype.card {j : n // p j})) :
    Matrix.det (fun i j : n => if p j then A i j else B i j) = 0 := by
  let C : Matrix n n K := fun i j => if p j then A i j else B i j
  let T : Matrix n n K := B⁻¹ * A
  let N : Matrix n n K := B⁻¹ * C
  have hNentry : N = fun i j : n => if p j then T i j else if i = j then (1 : K) else 0 := by
    ext i j
    by_cases hj : p j
    · simp [N, C, T, hj, Matrix.mul_apply]
    · have hmul := congr_fun (congr_fun (Matrix.nonsing_inv_mul B hBunit) i) j
      simp [N, C, T, hj, Matrix.mul_apply] at hmul ⊢
      simpa [Matrix.one_apply] using hmul
  have hpr_skew : ((T.submatrix (fun x : {j : n // p j} => (x : n)) (fun x : {j : n // p j} => (x : n)))ᵀ)
      = (-1 : K) • (T.submatrix (fun x : {j : n // p j} => (x : n)) (fun x : {j : n // p j} => (x : n))) := by
    ext i j
    have ht := congr_fun (congr_fun hTskew (i : n)) (j : n)
    simpa [Matrix.transpose_apply, Matrix.smul_apply, T] using ht
  have hpr_det : Matrix.det (T.submatrix (fun x : {j : n // p j} => (x : n)) (fun x : {j : n // p j} => (x : n))) = 0 :=
    det_eq_zero_of_transpose_eq_neg_odd'' _ hpr_skew hodd
  have hNdet : N.det = 0 := by
    rw [hNentry, det_mixed_identity_principal' p T, hpr_det]
  have hBC : B * N = C := by
    calc
      B * N = B * (B⁻¹ * C) := rfl
      _ = (B * B⁻¹) * C := by rw [Matrix.mul_assoc]
      _ = C := by rw [Matrix.mul_nonsing_inv B hBunit, Matrix.one_mul]
  have hdetC : C.det = (B * N).det := by rw [hBC]
  rw [hdetC, Matrix.det_mul, hNdet, mul_zero]

lemma transpose_nonsing_inv_mul_eq_neg' {K : Type*} [Field K]
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) (hBunit : IsUnit B.det)
    (hA : Aᵀ = (-1 : K) • A) (hB : Bᵀ = B) (hcomm : A * B = B * A) :
    (B⁻¹ * A)ᵀ = (-1 : K) • (B⁻¹ * A) := by
  calc
    (B⁻¹ * A)ᵀ = Aᵀ * (B⁻¹)ᵀ := by rw [Matrix.transpose_mul]
    _ = ((-1 : K) • A) * (Bᵀ)⁻¹ := by rw [hA, Matrix.transpose_nonsing_inv]
    _ = ((-1 : K) • A) * B⁻¹ := by rw [hB]
    _ = (-1 : K) • (A * B⁻¹) := by simp
    _ = (-1 : K) • (B⁻¹ * A) := by
      congr 1
      calc
        A * B⁻¹ = (B⁻¹ * B) * (A * B⁻¹) := by
          rw [Matrix.nonsing_inv_mul B hBunit, Matrix.one_mul]
        _ = B⁻¹ * (B * (A * B⁻¹)) := by rw [Matrix.mul_assoc]
        _ = B⁻¹ * ((B * A) * B⁻¹) := by rw [Matrix.mul_assoc]
        _ = B⁻¹ * ((A * B) * B⁻¹) := by rw [← hcomm]
        _ = B⁻¹ * (A * (B * B⁻¹)) := by rw [Matrix.mul_assoc]
        _ = B⁻¹ * A := by rw [Matrix.mul_nonsing_inv B hBunit, Matrix.mul_one]

set_option maxHeartbeats 800000 in

lemma mixed_column_det_zero_commuting
    (p : n → Prop) [DecidablePred p]
    (A B : Matrix n n R)
    (hA : Aᵀ = (-1 : R) • A) (hB : Bᵀ = B) (hcomm : A * B = B * A)
    (hodd : Odd (Fintype.card {j : n // p j})) :
    Matrix.det (fun i j : n => if p j then A i j else B i j) = 0 := by
  let P := R[X]
  let K := FractionRing P
  let fPK : P →+* K := algebraMap P K
  let fRK : R →+* K := algebraMap R K
  let Bpoly : Matrix n n P := (Polynomial.X : P) • (1 : Matrix n n P) + B.map Polynomial.C
  let Cpoly : Matrix n n P := fun i j => if p j then Polynomial.C (A i j) else Bpoly i j
  let AK : Matrix n n K := fRK.mapMatrix A
  let BK : Matrix n n K := fPK.mapMatrix Bpoly
  have hBpoly_ne : Bpoly.det ≠ 0 := by
    intro hzero
    have hlc := Polynomial.leadingCoeff_det_X_one_add_C B
    have : (Bpoly.det).leadingCoeff = 0 := by simp [hzero]
    have hBpoly_eq : Bpoly = (Polynomial.X : P) • (1 : Matrix n n P) + B.map Polynomial.C := rfl
    rw [← hBpoly_eq] at hlc
    rw [this] at hlc
    exact one_ne_zero hlc.symm
  have hBKunit : IsUnit BK.det := by
    rw [← RingHom.map_det]
    apply (isUnit_iff_ne_zero).mpr
    exact (IsFractionRing.to_map_eq_zero_iff.not).mpr hBpoly_ne
  have hAKskew : AKᵀ = (-1 : K) • AK := by
    ext i j
    have ht := congr_fun (congr_fun hA i) j
    have ht' := congr_arg fRK ht
    have ht'' : fRK (A j i) = - fRK (A i j) := by
      simpa [Matrix.transpose_apply, Matrix.smul_apply, map_neg] using ht'
    have hneg : - fRK (A i j) = (-1 : K) * fRK (A i j) := by ring
    simpa [AK, Matrix.transpose_apply, Matrix.smul_apply] using ht''.trans hneg
  have hBKsymm : BKᵀ = BK := by
    ext i j
    have ht := congr_fun (congr_fun hB i) j
    by_cases hij : i = j
    · subst j
      simp [BK, Bpoly, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply]
    · have hji : j ≠ i := by exact fun h => hij h.symm
      have ht' := congr_arg (fun x : R => fPK (Polynomial.C x)) ht
      simp [BK, Bpoly, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, hij, hji] at ht' ⊢
      exact ht'
  have hcommK : AK * BK = BK * AK := by
    let xK : K := fPK Polynomial.X
    let BKC : Matrix n n K := fRK.mapMatrix B
    have hBKdecomp : BK = xK • (1 : Matrix n n K) + BKC := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [BK, Bpoly, BKC, xK, fRK, fPK]
        rw [Algebra.smul_def, mul_one]
        congr 1

      · have hji : j ≠ i := fun h => hij h.symm
        simp [BK, Bpoly, BKC, xK, hij, hji, fRK, fPK]
        exact (IsScalarTower.algebraMap_apply R (R[X]) K (B i j)).symm
    have hABKC : AK * BKC = BKC * AK := by
      dsimp [AK, BKC]
      rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm]
    rw [hBKdecomp]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, hABKC]
  have hTskew := transpose_nonsing_inv_mul_eq_neg' AK BK hBKunit hAKskew hBKsymm hcommK
  have hdetK : Matrix.det (fun i j : n => if p j then AK i j else BK i j) = 0 :=
    mixed_column_det_zero' p AK BK hBKunit hTskew hodd
  have hmapC : fPK.mapMatrix Cpoly = (fun i j : n => if p j then AK i j else BK i j) := by
    ext i j
    by_cases hj : p j
    · simp [Cpoly, AK, BK, Bpoly, hj, fRK, fPK]
      rw [Polynomial.C_eq_algebraMap, IsScalarTower.algebraMap_apply R P K]
    · simp [Cpoly, AK, BK, Bpoly, hj, fRK, fPK]
  have hCpoly_det_zero : Cpoly.det = 0 := by
    have hm : fPK Cpoly.det = 0 := by
      rw [RingHom.map_det, hmapC, hdetK]
    exact (IsFractionRing.to_map_eq_zero_iff (K:=K)).mp hm
  have h_eval : (Polynomial.evalRingHom (0 : R)) Cpoly.det = Matrix.det (fun i j : n => if p j then A i j else B i j) := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases hj : p j
    · simp [Cpoly, Bpoly, hj]
    · by_cases hij : i = j
      · subst j
        simp [Cpoly, Bpoly, hj, Polynomial.evalRingHom]
        rw [Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero]
        simp
      · simp [Cpoly, Bpoly, hj, hij, Polynomial.evalRingHom, Polynomial.coeff_C_zero]
  rw [← h_eval, hCpoly_det_zero]
  simp

#print axioms mixed_column_det_zero_commuting

open Finset MulChar
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma jacobiSum_quadratic_quadratic (hF : ringChar F ≠ 2) :
    jacobiSum (quadraticChar F) (quadraticChar F) = -(quadraticChar F (-1)) := by
  have hne : quadraticChar F ≠ 1 := quadraticChar_ne_one hF
  have hinv : (quadraticChar F)⁻¹ = quadraticChar F := (quadraticChar_isQuadratic F).inv
  nth_rewrite 2 [← hinv]
  exact jacobiSum_nontrivial_inv hne

lemma sum_quadratic_mul_one_sub (hF : ringChar F ≠ 2) :
    (∑ x : F, (quadraticChar F) x * (quadraticChar F) (1 - x)) =
      -(quadraticChar F (-1)) := by
  simpa [jacobiSum] using jacobiSum_quadratic_quadratic (F:=F) hF

lemma sum_quadratic_mul_sub_one (hF : ringChar F ≠ 2) :
    (∑ x : F, (quadraticChar F) x * (quadraticChar F) (x - 1)) =
      -1 := by
  calc
    (∑ x : F, (quadraticChar F) x * (quadraticChar F) (x - 1))
        = ∑ x : F, (quadraticChar F) (-1) * ((quadraticChar F) x * (quadraticChar F) (1 - x)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [show x - 1 = -1 * (1 - x) by ring]
          rw [map_mul]
          ring
    _ = (quadraticChar F) (-1) * (∑ x : F, (quadraticChar F) x * (quadraticChar F) (1 - x)) := by
          rw [Finset.mul_sum]
    _ = (quadraticChar F) (-1) * (-(quadraticChar F (-1))) := by
          rw [sum_quadratic_mul_one_sub (F:=F) hF]
    _ = -1 := by
          have hneg : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
          have hs := quadraticChar_sq_one (F:=F) hneg
          nlinarith

#print axioms sum_quadratic_mul_sub_one

lemma sum_quadratic_mul_shift_ne (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - b)) = -1 := by
  let d : F := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  -- substitute x = a + d * y
  calc
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - b))
        = ∑ y : F, (quadraticChar F) (((Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a)) y - a) *
            (quadraticChar F) (((Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a)) y - b) := by
          exact (Equiv.sum_comp ((Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a))
            (fun x : F => (quadraticChar F) (x - a) * (quadraticChar F) (x - b))).symm
    _ = ∑ y : F, (quadraticChar F) ((a + d * y) - a) * (quadraticChar F) ((a + d * y) - b) := by
          simp [add_comm]
    _ = ∑ y : F, (quadraticChar F) d ^ 2 * ((quadraticChar F) y * (quadraticChar F) (y - 1)) := by
          apply Finset.sum_congr rfl
          intro y _
          have h1 : (a + d * y) - a = d * y := by ring
          have h2 : (a + d * y) - b = d * (y - 1) := by
            dsimp [d]
            ring
          rw [h1, h2, map_mul, map_mul]
          ring
    _ = ∑ y : F, (quadraticChar F) y * (quadraticChar F) (y - 1) := by
          apply Finset.sum_congr rfl
          intro y _
          have hs := quadraticChar_sq_one (F:=F) hd
          rw [hs]
          ring
    _ = -1 := sum_quadratic_mul_sub_one (F:=F) hF

#print axioms sum_quadratic_mul_shift_ne

lemma sum_quadratic_square_shift (hF : ringChar F ≠ 2) (a : F) :
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - a)) = (Fintype.card F : ℤ) - 1 := by
  calc
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - a))
        = ∑ y : F, (quadraticChar F) y * (quadraticChar F) y := by
          exact (Equiv.sum_comp (Equiv.addRight a)
            (fun x : F => (quadraticChar F) (x - a) * (quadraticChar F) (x - a))).symm.trans (by simp)
    _ = ∑ y : F, if y = 0 then (0 : ℤ) else 1 := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : y = 0
          · simp [hy]
          · have hs := quadraticChar_sq_one (F:=F) hy
            simpa [hy, pow_two] using hs
    _ = (Fintype.card F : ℤ) - 1 := by
          rw [Finset.sum_eq_sum_diff_singleton_add (s:=Finset.univ) (i:=(0:F)) (by simp)
            (fun y => if y = 0 then (0 : ℤ) else 1)]
          simp only [ite_true, add_zero]
          have hconst : (∑ x ∈ (Finset.univ \ {0} : Finset F), if x = 0 then (0 : ℤ) else 1) =
              ∑ x ∈ (Finset.univ \ {0} : Finset F), (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            simp [hx]
          rw [hconst, Finset.sum_const, nsmul_eq_mul]
          simp
          have hcard : #(Finset.univ \ ({0} : Finset F)) = Fintype.card F - 1 := by
            rw [Finset.card_sdiff]
            simp
          rw [hcard]
          have hpos : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
          rw [Nat.cast_sub hpos]
          simp

#print axioms sum_quadratic_square_shift

lemma sum_quadratic_mul_shift (hF : ringChar F ≠ 2) (a b : F) :
    (∑ x : F, (quadraticChar F) (x - a) * (quadraticChar F) (x - b)) =
      if a = b then (Fintype.card F : ℤ) - 1 else -1 := by
  by_cases hab : a = b
  · subst b
    simpa using sum_quadratic_square_shift (F:=F) hF a
  · simpa [hab] using sum_quadratic_mul_shift_ne (F:=F) hF hab

#print axioms sum_quadratic_mul_shift

open Matrix Finset MulChar
open scoped BigOperators

abbrev QR2 (F : Type*) [Field F] [Fintype F] [DecidableEq F] := {x : F // quadraticChar F x = 1}

lemma sum_QR_eq_half_weighted2 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (g : F → ℚ) :
    (∑ s : QR2 F, g s) = (1 / 2 : ℚ) *
      ∑ x : F, (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * g x) := by
  classical
  have hsub : (∑ s : QR2 F, g s) = (Finset.univ.filter (fun x : F => quadraticChar F x = 1)).sum (fun x => g x) := by
    symm
    simpa using (Finset.sum_subtype (s := Finset.univ.filter (fun x : F => quadraticChar F x = 1))
      (h := by intro x; simp) (f := g))
  rw [hsub]
  calc
    (Finset.univ.filter (fun x : F => quadraticChar F x = 1)).sum (fun x => g x)
        = ∑ x : F, if quadraticChar F x = 1 then g x else 0 := by
          simp [Finset.sum_filter]
    _ = (1 / 2 : ℚ) * ∑ x : F, (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * g x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · by_cases h1 : quadraticChar F x = 1
        · simp [h1]
        · have hsq := quadraticChar_sq_one (F:=F) hx0
          have hneg : quadraticChar F x = -1 := by
            exact quadraticChar_eq_neg_one_iff_not_one hx0 |>.2 h1
          simp [h1, hneg, hsq]

lemma sum_QR_neg_eq_half_weighted2 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hneg1 : quadraticChar F (-1) = -1) (g : F → ℚ) :
    (∑ s : QR2 F, g (-(s : F))) = (1 / 2 : ℚ) *
      ∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * g x) := by
  classical
  have hsub : (∑ s : QR2 F, g (-(s : F))) = (Finset.univ.filter (fun x : F => quadraticChar F x = 1)).sum (fun x => g (-x)) := by
    symm
    simpa using (Finset.sum_subtype (s := Finset.univ.filter (fun x : F => quadraticChar F x = 1))
      (h := by intro x; simp) (f := fun x => g (-x)))
  rw [hsub]
  calc
    (Finset.univ.filter (fun x : F => quadraticChar F x = 1)).sum (fun x => g (-x))
        = (Finset.univ.filter (fun y : F => quadraticChar F y = -1)).sum (fun y => g y) := by
          apply Finset.sum_bij (fun x _ => -x)
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            rw [show (-x) = (-1 : F) * x by ring]
            rw [map_mul, hneg1, hx]
            norm_num
          · intro x hx y hy hxy
            exact neg_injective hxy
          · intro y hy
            refine ⟨-y, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
              rw [show (-y) = (-1 : F) * y by ring]
              rw [map_mul, hneg1, hy]
              norm_num
            · simp
          · intro x hx
            simp
    _ = ∑ x : F, if quadraticChar F x = -1 then g x else 0 := by
          simp [Finset.sum_filter]
    _ = (1 / 2 : ℚ) * ∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * g x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hx0 : x = 0
          · simp [hx0]
          · by_cases hneg : quadraticChar F x = -1
            · have hsq : (quadraticChar F x)^2 = (1:ℤ) := by rw [hneg]; norm_num
              simp [hneg, hsq]
            · have hsq := quadraticChar_sq_one (F:=F) hx0
              have hcases := quadraticChar_dichotomy (F:=F) hx0
              rcases hcases with h1 | hm
              · simp [hneg, h1, hsq]
              · exact False.elim (hneg hm)

lemma paley_full_sum_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1) (r t : QR2 F) :
    (∑ x : F, (quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F))) = 1 := by
  have hrt : (r : F) ≠ -(t : F) := by
    intro h
    have hr : quadraticChar F (r:F) = 1 := r.2
    have ht : quadraticChar F (t:F) = 1 := t.2
    have hcalc : quadraticChar F (r:F) = -1 := by
      rw [h]
      rw [show (-(t : F)) = (-1 : F) * (t : F) by ring, map_mul, hneg1, ht]
      norm_num
    rw [hr] at hcalc
    norm_num at hcalc
  calc
    (∑ x : F, (quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F)))
        = ∑ x : F, (-(quadraticChar F) (x - (r:F))) * (quadraticChar F) (x - (-(t:F))) := by
          apply Finset.sum_congr rfl
          intro x hx
          have h1 : (r:F) - x = - ((x - (r:F))) := by ring
          have h2 : x + (t:F) = x - (-(t:F)) := by ring
          rw [h1, h2]
          rw [show (-(x - (r:F))) = (-1 : F) * (x - (r:F)) by ring, map_mul, hneg1]
          ring
    _ = - (∑ x : F, (quadraticChar F) (x - (r:F)) * (quadraticChar F) (x - (-(t:F)))) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = 1 := by
          have hs := sum_quadratic_mul_shift_ne (F:=F) hF hrt
          rw [hs]
          norm_num

#print axioms paley_full_sum_one

lemma paley_indicator_sum_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1) (r t : QR2 F) :
    (∑ x : F, (((quadraticChar F x)^2 : ℤ) : ℚ) *
      (((quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F)) : ℤ) : ℚ)) = 0 := by
  let f : F → ℤ := fun x => (quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F))
  have hfullZ := paley_full_sum_one (F:=F) hF hneg1 r t
  have hfullQ : (∑ x : F, ((f x : ℤ) : ℚ)) = 1 := by
    norm_num [f] at hfullZ ⊢
    exact_mod_cast hfullZ
  have hf0 : f 0 = 1 := by
    dsimp [f]
    rw [sub_zero, zero_add]
    change (quadraticChar F (r:F)) * (quadraticChar F (t:F)) = 1
    rw [r.2, t.2]
    norm_num
  calc
    (∑ x : F, (((quadraticChar F x)^2 : ℤ) : ℚ) * ((f x : ℤ) : ℚ))
        = ∑ x : F, (if x = 0 then (0 : ℚ) else ((f x : ℤ) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hx0 : x = 0
          · simp [hx0]
          · have hsq := quadraticChar_sq_one (F:=F) hx0
            simp [hx0]
            change ((((quadraticChar F x)^2 : ℤ) : ℚ) * ((f x : ℤ) : ℚ)) = ((f x : ℤ) : ℚ)
            rw [hsq]
            norm_num
    _ = (∑ x : F, ((f x : ℤ) : ℚ)) - ((f 0 : ℤ) : ℚ) := by
          have hset : Finset.univ \ ({0} : Finset F) = Finset.univ.erase (0:F) := by
            ext x; simp
          have hif : (∑ x : F, if x = 0 then (0 : ℚ) else ((f x : ℤ) : ℚ)) =
              (Finset.univ.erase (0:F)).sum (fun x => ((f x : ℤ) : ℚ)) := by
            rw [Finset.sum_eq_sum_diff_singleton_add (s:=Finset.univ) (i:=(0:F)) (by simp)
              (fun x => if x = 0 then (0:ℚ) else ((f x:ℤ):ℚ))]
            simp only [if_true, add_zero]
            rw [hset]
            apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            simp [hx]
          have htot : (∑ x : F, ((f x : ℤ) : ℚ)) =
              ((Finset.univ.erase (0:F)).sum (fun x => ((f x : ℤ) : ℚ))) + ((f 0 : ℤ) : ℚ) := by
            rw [Finset.sum_eq_sum_diff_singleton_add (s:=Finset.univ) (i:=(0:F)) (by simp)
              (fun x => ((f x:ℤ):ℚ))]
            rw [hset]
          rw [hif, htot]
          ring
    _ = 0 := by
          rw [hfullQ, hf0]
          norm_num

lemma paley_matrices_commute {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1) :
    let A : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) - (s:F)) : ℤ) : ℚ)
    let B : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) + (s:F)) : ℤ) : ℚ)
    A * B = B * A := by
  classical
  intro A B
  ext r t
  let f : F → ℚ := fun x => (((quadraticChar F) ((r:F) - x) * (quadraticChar F) (x + (t:F)) : ℤ) : ℚ)
  have hAB : (A * B) r t = (1 / 2 : ℚ) * ∑ x : F,
      (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
    calc
      (A * B) r t = ∑ s : QR2 F, f (s : F) := by
        simp [Matrix.mul_apply, A, B, f]
      _ = (1 / 2 : ℚ) * ∑ x : F,
          (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x) :=
        sum_QR_eq_half_weighted2 (F:=F) f
  have hBA : (B * A) r t = (1 / 2 : ℚ) * ∑ x : F,
      (((quadraticChar F x - (quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
    have hneg := sum_QR_neg_eq_half_weighted2 (F:=F) hneg1 f
    -- BA summand is `- f (-s)`.
    calc
      (B * A) r t = ∑ s : QR2 F, - f (-(s:F)) := by
        simp [Matrix.mul_apply, A, B, f]
        conv_rhs => rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro s hs
        rw [show (↑s - (t:F)) = - ((-(s:F)) + (t:F)) by ring]
        rw [show ((r:F) + ↑s) = (r:F) - (-(s:F)) by ring]
        rw [show (-((-(s:F)) + (t:F))) = (-1 : F) * ((-(s:F)) + (t:F)) by ring]
        change (((quadraticChar F) ((r:F) - (-(s:F))) : ℤ) : ℚ) *
            (((quadraticChar F) ((-1 : F) * ((-(s:F)) + (t:F))) : ℤ) : ℚ) =
          - ((((quadraticChar F) ((r:F) - (-(s:F))) : ℤ) : ℚ) *
            (((quadraticChar F) ((-(s:F)) + (t:F)) : ℤ) : ℚ))
        rw [map_mul, hneg1]
        rw [show (-1 : ℤ) * (quadraticChar F (-(s:F) + (t:F))) =
            - (quadraticChar F (-(s:F) + (t:F))) by ring]
        rw [Int.cast_neg]
        ring
      _ = - (∑ s : QR2 F, f (-(s:F))) := by rw [Finset.sum_neg_distrib]
      _ = - ((1 / 2 : ℚ) * ∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x)) := by rw [hneg]
      _ = (1 / 2 : ℚ) * ∑ x : F, (((quadraticChar F x - (quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
        rw [show -((1 / 2 : ℚ) * ∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x)) =
            (1 / 2 : ℚ) * (-(∑ x : F, (((-quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x))) by ring]
        rw [← Finset.sum_neg_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        norm_num
        ring
  have hS2 := paley_indicator_sum_zero (F:=F) hF hneg1 r t
  rw [hAB, hBA]
  have hsplit1 : (∑ x : F, (((quadraticChar F x + (quadraticChar F x)^2 : ℤ) : ℚ) * f x)) =
      (∑ x : F, ((quadraticChar F x : ℤ) : ℚ) * f x) +
      (∑ x : F, (((quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    norm_num
    ring
  have hsplit2 : (∑ x : F, (((quadraticChar F x - (quadraticChar F x)^2 : ℤ) : ℚ) * f x)) =
      (∑ x : F, ((quadraticChar F x : ℤ) : ℚ) * f x) -
      (∑ x : F, (((quadraticChar F x)^2 : ℤ) : ℚ) * f x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    norm_num
    ring
  rw [hsplit1, hsplit2, hS2]
  ring

#print axioms paley_matrices_commute

lemma paley_A_skew {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hneg1 : quadraticChar F (-1) = -1) :
    let A : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) - (s:F)) : ℤ) : ℚ)
    Aᵀ = (-1 : ℚ) • A := by
  intro A
  ext r s
  by_cases hrs : (r : F) = (s : F)
  · simp [A, Matrix.transpose_apply, Matrix.smul_apply, hrs]
  · have hsub : (s:F) - (r:F) = (-1 : F) * ((r:F) - (s:F)) := by ring
    rw [Matrix.transpose_apply, Matrix.smul_apply]
    simp [A]
    rw [hsub]
    change (((quadraticChar F) ((-1 : F) * ((r:F) - (s:F))) : ℤ) : ℚ) =
      - (((quadraticChar F) ((r:F) - (s:F)) : ℤ) : ℚ)
    rw [map_mul, hneg1]
    norm_num

lemma paley_B_symm {F : Type*} [Field F] [Fintype F] [DecidableEq F] :
    let B : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) + (s:F)) : ℤ) : ℚ)
    Bᵀ = B := by
  intro B
  ext r s
  simp [B, Matrix.transpose_apply, add_comm]

#print axioms paley_A_skew
#print axioms paley_B_symm

lemma paley_mixed_det_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (hneg1 : quadraticChar F (-1) = -1)
    (p : QR2 F → Prop) [DecidablePred p]
    (hodd : Odd (Fintype.card {j : QR2 F // p j})) :
    let A : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) - (s:F)) : ℤ) : ℚ)
    let B : Matrix (QR2 F) (QR2 F) ℚ := fun r s => ((quadraticChar F ((r:F) + (s:F)) : ℤ) : ℚ)
    Matrix.det (fun i j : QR2 F => if p j then A i j else B i j) = 0 := by
  intro A B
  exact mixed_column_det_zero_commuting (R:=ℚ) p A B
    (paley_A_skew (F:=F) hneg1)
    (paley_B_symm (F:=F))
    (paley_matrices_commute (F:=F) hF hneg1)
    hodd

#print axioms paley_mixed_det_zero
