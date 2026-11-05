import Submission.Common

/-! An arithmetic transfer from a separated, primitive integer kernel to
positive, distinct-subset-sum natural numbers. -/

namespace Erdos1Aux

private def blockDigit {d s : ℕ} (S : Finset (Fin (d + 1) × Fin (s + 1)))
    (i : Fin (d + 1)) : ℕ :=
  ∑ j : Fin (s + 1), if (i, j) ∈ S then 2 ^ (j : ℕ) else 0

private lemma blockDigit_lt {d s : ℕ} (S : Finset (Fin (d + 1) × Fin (s + 1)))
    (i : Fin (d + 1)) : blockDigit S i < 2 ^ (s + 1) := by
  calc
    blockDigit S i ≤ ∑ j : Fin (s + 1), 2 ^ (j : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs <;> simp
    _ = 2 ^ (s + 1) - 1 := by
      rw [Fin.sum_univ_eq_sum_range, Nat.geomSum_eq (by omega)]
      norm_num
    _ < 2 ^ (s + 1) := Nat.sub_lt (by positivity) (by omega)

private lemma blockDigit_injective {d s : ℕ}
    {S T : Finset (Fin (d + 1) × Fin (s + 1))}
    (h : ∀ i : Fin (d + 1), blockDigit S i = blockDigit T i) : S = T := by
  have hblock (i : Fin (d + 1)) :
      (Finset.univ.filter (fun j : Fin (s + 1) => (i, j) ∈ S)) =
        (Finset.univ.filter (fun j : Fin (s + 1) => (i, j) ∈ T)) := by
    apply Finset.image_injective Fin.val_injective
    apply Finset.geomSum_injective (n := 2) (by omega)
    simpa only [Finset.sum_image Fin.val_injective.injOn, Finset.sum_filter, blockDigit]
      using h i
  ext ⟨i, j⟩
  have hh := Finset.ext_iff.mp (hblock i) j
  simpa using hh

private def bitWeight {d s : ℕ} (t : Fin (d + 1) → ℕ)
    (p : Fin (d + 1) × Fin (s + 1)) : ℕ := t p.1 * 2 ^ (p.2 : ℕ)

private lemma sum_bitWeight {d s : ℕ} (t : Fin (d + 1) → ℕ)
    (S : Finset (Fin (d + 1) × Fin (s + 1))) :
    (∑ p ∈ S, bitWeight t p : ℕ) =
      ∑ i : Fin (d + 1), t i * blockDigit S i := by
  calc
    _ = ∑ p : Fin (d + 1) × Fin (s + 1),
        if p ∈ S then bitWeight t p else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ i : Fin (d + 1), ∑ j : Fin (s + 1),
        if (i, j) ∈ S then t i * 2 ^ (j : ℕ) else 0 := by
      conv_lhs => rw [← Finset.univ_product_univ (α := Fin (d + 1)) (β := Fin (s + 1)),
        Finset.sum_product]
      rfl
    _ = ∑ i : Fin (d + 1), t i * blockDigit S i := by
      simp only [blockDigit, Finset.mul_sum, mul_ite, mul_zero]

private lemma bitWeight_subset_injective {d s : ℕ} (t : Fin (d + 1) → ℕ)
    (hsep : ∀ u : Fin (d + 1) → ℤ,
      (∀ i, |u i| < (2 ^ (s + 1) : ℤ)) →
      (∑ i, (t i : ℤ) * u i) = 0 → u = 0) :
    Function.Injective (fun S : Finset (Fin (d + 1) × Fin (s + 1)) =>
      ∑ p ∈ S, bitWeight t p) := by
  intro S T hST
  have hnat : (∑ i : Fin (d + 1), t i * blockDigit S i) =
      ∑ i : Fin (d + 1), t i * blockDigit T i := by
    rw [← sum_bitWeight t S, ← sum_bitWeight t T]
    exact hST
  have hcast : (∑ i : Fin (d + 1), (t i : ℤ) * (blockDigit S i : ℤ)) =
      ∑ i : Fin (d + 1), (t i : ℤ) * (blockDigit T i : ℤ) := by
    exact_mod_cast hnat
  let u : Fin (d + 1) → ℤ := fun i => (blockDigit S i : ℤ) - (blockDigit T i : ℤ)
  have huBound (i : Fin (d + 1)) : |u i| < (2 ^ (s + 1) : ℤ) := by
    have hS := blockDigit_lt S i
    have hT := blockDigit_lt T i
    have hS' : (blockDigit S i : ℤ) < (2 ^ (s + 1) : ℤ) := by exact_mod_cast hS
    have hT' : (blockDigit T i : ℤ) < (2 ^ (s + 1) : ℤ) := by exact_mod_cast hT
    dsimp [u]
    rw [abs_lt]
    constructor <;> omega
  have huSum : (∑ i : Fin (d + 1), (t i : ℤ) * u i) = 0 := by
    calc
      _ = (∑ i : Fin (d + 1), (t i : ℤ) * (blockDigit S i : ℤ)) -
          (∑ i : Fin (d + 1), (t i : ℤ) * (blockDigit T i : ℤ)) := by
        simp only [u, mul_sub, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hcast
  have hu := hsep u huBound huSum
  apply blockDigit_injective
  intro i
  have hi : u i = 0 := congrFun hu i
  dsimp [u] at hi
  exact_mod_cast sub_eq_zero.mp hi

/-- The binary blocks of a positive separated integer kernel produce a finite
set of *actual* natural-number weights with globally distinct subset sums. -/
theorem small_family_of_separated_kernel {d s : ℕ} (t : Fin (d + 1) → ℕ) (c : ℚ)
    (hc : 0 < c) (ht : ∀ i, 0 < t i)
    (htbound : ∀ i, (t i : ℝ) < (c : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ d)
    (hsep : ∀ u : Fin (d + 1) → ℤ,
      (∀ i, |u i| < (2 ^ (s + 1) : ℤ)) →
      (∑ i, (t i : ℤ) * u i) = 0 → u = 0) :
    ∃ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧
      (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective ∧
      N ≠ 0 ∧ (N : ℝ) < (c : ℝ) * 2 ^ A.card := by
  let w : Fin (d + 1) × Fin (s + 1) → ℕ := bitWeight t
  let A : Finset ℕ := Finset.univ.image w
  let N : ℕ := (Finset.univ.sup t) * 2 ^ s
  have hlabels := bitWeight_subset_injective t hsep
  have hw : Function.Injective w := by
    intro p r hpr
    have hsingle : ({p} : Finset (Fin (d + 1) × Fin (s + 1))) = {r} := by
      apply hlabels
      simpa only [Finset.sum_singleton, w] using hpr
    exact Finset.singleton_injective hsingle
  have hcard : A.card = (d + 1) * (s + 1) := by
    simp only [A, Finset.card_image_of_injective _ hw, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin]
  refine ⟨N, A, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · change 1 ≤ t p.1 * 2 ^ (p.2 : ℕ)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt (ht p.1))
        (pow_ne_zero _ (by omega)))
    · change t p.1 * 2 ^ (p.2 : ℕ) ≤ (Finset.univ.sup t) * 2 ^ s
      apply Nat.mul_le_mul (Finset.le_sup (Finset.mem_univ p.1))
      exact pow_le_pow_right₀ (by omega) (by omega)
  · intro ⟨S, hS⟩ ⟨T, hT⟩ hST
    obtain ⟨S₀, hS₀, rfl⟩ :=
      (Finset.image_surjOn_powerset (s := (Finset.univ :
        Finset (Fin (d + 1) × Fin (s + 1)))) (f := w)) hS
    obtain ⟨T₀, hT₀, rfl⟩ :=
      (Finset.image_surjOn_powerset (s := (Finset.univ :
        Finset (Fin (d + 1) × Fin (s + 1)))) (f := w)) hT
    have hST₀ : S₀ = T₀ := by
      apply hlabels
      have hSsum := Finset.sum_image hw.injOn (s := S₀) (f := id)
      have hTsum := Finset.sum_image hw.injOn (s := T₀) (f := id)
      simpa only [w, Function.id_def] using hSsum.symm.trans (hST.trans hTsum)
    exact Subtype.ext (congrArg (Finset.image w) hST₀)
  · have hsup : 0 < (Finset.univ.sup t : ℕ) :=
      (ht (0 : Fin (d + 1))).trans_le (Finset.le_sup (Finset.mem_univ _))
    exact Nat.ne_of_gt (Nat.mul_pos hsup (pow_pos (by omega : 0 < (2 : ℕ)) s))
  · obtain ⟨i, hi, hisup⟩ :=
      Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (d + 1)))
        ⟨0, Finset.mem_univ _⟩ t
    have hsup : ((Finset.univ.sup t : ℕ) : ℝ) <
        (c : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ d := by
      rw [hisup]
      exact htbound i
    have hpow : (2 : ℝ) ^ ((d + 1) * (s + 1)) =
        ((2 : ℝ) ^ (s + 1)) ^ d * (2 : ℝ) ^ (s + 1) := by
      rw [add_mul, one_mul, pow_add, mul_comm d (s + 1), pow_mul]
    rw [hcard, hpow]
    have hmul := mul_lt_mul_of_pos_right hsup
      (pow_pos (show (0 : ℝ) < 2 by norm_num) s)
    have hlt : (2 : ℝ) ^ s < (2 : ℝ) ^ (s + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) s]
    have hcoeff : 0 < (c : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ d := by
      exact mul_pos (by exact_mod_cast hc) (pow_pos (by positivity) _)
    calc
      (N : ℝ) < ((c : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ d) * (2 : ℝ) ^ s := by
        simpa only [N, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hmul
      _ < ((c : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ d) * (2 : ℝ) ^ (s + 1) :=
        mul_lt_mul_of_pos_left hlt hcoeff
      _ = (c : ℝ) * (((2 : ℝ) ^ (s + 1)) ^ d * (2 : ℝ) ^ (s + 1)) := by ring

/- A determinant normal for a rectangular matrix. The appended column has
index `Fin.last d`; the first `d` columns are the original matrix. -/
private def normalBase {d : ℕ} {R : Type*} [Zero R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  fun i j => (Fin.snoc (fun k : Fin d => M i k) (0 : R) : Fin (d + 1) → R) j

private def normalAug {d : ℕ} {R : Type*} [Zero R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) (u : Fin (d + 1) → R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) R :=
  (normalBase M).updateCol (Fin.last d) u

private def signedNormal {d : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) (i : Fin (d + 1)) : R :=
  (normalAug M (fun j => if i = j then 1 else 0)).det

private lemma normalAug_castSucc {d : ℕ} {R : Type*} [Zero R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) (u : Fin (d + 1) → R)
    (i : Fin (d + 1)) (j : Fin d) :
    normalAug M u i j.castSucc = M i j := by
  simp [normalAug, normalBase, Fin.snoc_castSucc,
    Fin.castSucc_ne_last]

private lemma normalAug_last {d : ℕ} {R : Type*} [Zero R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) (u : Fin (d + 1) → R)
    (i : Fin (d + 1)) :
    normalAug M u i (Fin.last d) = u i := by
  simp [normalAug]

private lemma signedNormal_dot {d : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) (u : Fin (d + 1) → R) :
    (normalAug M u).det = ∑ i, signedNormal M i * u i := by
  let L : (Fin (d + 1) → R) →ₗ[R] R :=
    (LinearMap.proj (Fin.last d)).comp (Matrix.cramer (normalBase M))
  have hL (v : Fin (d + 1) → R) : L v = (normalAug M v).det :=
    Matrix.cramer_apply (normalBase M) v (Fin.last d)
  have h := LinearMap.pi_apply_eq_sum_univ L u
  rw [hL] at h
  simpa only [hL, smul_eq_mul, mul_comm, signedNormal] using h

private lemma signedNormal_mulVec {d : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) (z : Fin d → R) :
    (∑ i : Fin (d + 1), signedNormal M i * M.mulVec z i) = 0 := by
  rw [← signedNormal_dot]
  let H := normalBase M
  have hcol (j : Fin d) : H.cramer (M.col j) (Fin.last d) = 0 := by
    have hj : ∀ i, (M.col j) i = H i j.castSucc := by
      intro i
      simp [Matrix.col_apply, H, normalBase, Fin.snoc_castSucc]
    rw [Matrix.cramer_row_self H (M.col j) j.castSucc hj]
    simp [Fin.castSucc_ne_last]
  calc
    (normalAug M (M.mulVec z)).det = H.cramer (M.mulVec z) (Fin.last d) :=
      (Matrix.cramer_apply H _ _).symm
    _ = ∑ j : Fin d, z j * H.cramer (M.col j) (Fin.last d) := by
      rw [Matrix.mulVec_eq_sum]
      simp only [op_smul_eq_smul, map_sum, Finset.sum_apply, map_smul,
        Pi.smul_apply, smul_eq_mul, Matrix.col, Matrix.transpose]
    _ = 0 := by simp only [hcol, mul_zero, Finset.sum_const_zero]

private def graphMatrix {d : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin d) (Fin d) R) : Matrix (Fin (d + 1)) (Fin d) R :=
  fun i j => (Fin.snoc (fun k : Fin d => B k j) (-(∑ k : Fin d, B k j)) :
    Fin (d + 1) → R) i

private lemma graphMatrix_castSucc {d : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin d) (Fin d) R) (i j : Fin d) :
    graphMatrix B i.castSucc j = B i j := by
  simp [graphMatrix, Fin.snoc_castSucc]

private lemma graphMatrix_last {d : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin d) (Fin d) R) (j : Fin d) :
    graphMatrix B (Fin.last d) j = -(∑ k : Fin d, B k j) := by
  simp [graphMatrix, Fin.snoc_last]

private lemma signedNormal_graph_last {d : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin d) (Fin d) R) :
    signedNormal (graphMatrix B) (Fin.last d) = B.det := by
  let M := normalAug (graphMatrix B)
      (fun j : Fin (d + 1) => if Fin.last d = j then (1 : R) else 0)
  change M.det = B.det
  rw [Matrix.det_succ_column M (Fin.last d)]
  rw [Finset.sum_eq_single (Fin.last d)]
  · have hsgn : (-1 : R) ^ (d + d) = 1 := by
      simpa only [two_mul] using ((even_two_mul d).neg_one_pow : (-1 : R) ^ (2 * d) = 1)
    have hminor : (M.submatrix (Fin.last d).succAbove
        (Fin.last d).succAbove).det = B.det := by
      congr 1
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, M,
        normalAug_castSucc, graphMatrix_castSucc]
    simp only [Fin.val_last, hsgn, one_mul, hminor, M, normalAug_last, ite_true]
  · intro j hj hjne
    have hzero : M j (Fin.last d) = 0 := by
      simp only [M, normalAug_last, if_neg hjne.symm]
    simp only [hzero, mul_zero, zero_mul]
  · simp

private lemma graphMatrix_mulVec_castSucc {d : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin d) (Fin d) R) (z : Fin d → R) (i : Fin d) :
    (graphMatrix B).mulVec z i.castSucc = B.mulVec z i := by
  simp only [Matrix.mulVec, dotProduct, graphMatrix_castSucc]

private lemma graphMatrix_mulVec_last {d : ℕ} {R : Type*} [CommRing R]
    (B : Matrix (Fin d) (Fin d) R) (z : Fin d → R) :
    (graphMatrix B).mulVec z (Fin.last d) = -(∑ i : Fin d, B.mulVec z i) := by
  simp only [Matrix.mulVec, dotProduct, graphMatrix_last]
  change (∑ j : Fin d, (-(∑ i : Fin d, B i j)) * z j) =
    -(∑ i : Fin d, ∑ j : Fin d, B i j * z j)
  calc
    _ = -(∑ j : Fin d, ∑ i : Fin d, B i j * z j) := by
      simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    _ = -(∑ i : Fin d, ∑ j : Fin d, B i j * z j) := by rw [Finset.sum_comm]

private lemma signedNormal_graph {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℚ) (hdet : B.det ≠ 0)
    (i : Fin (d + 1)) : signedNormal (graphMatrix B) i = B.det := by
  let F := graphMatrix B
  have hlast : signedNormal F (Fin.last d) = B.det :=
    signedNormal_graph_last B
  induction i using Fin.lastCases with
  | last => exact hlast
  | cast i =>
    have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
    let z : Fin d → ℚ := B⁻¹.mulVec (Pi.single i 1)
    have hBz : B.mulVec z = Pi.single i 1 := by
      simp only [z, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hunit,
        Matrix.one_mulVec]
    have hFz : F.mulVec z =
        Pi.single i.castSucc (1 : ℚ) - Pi.single (Fin.last d) 1 := by
      ext j
      induction j using Fin.lastCases with
      | last =>
          rw [graphMatrix_mulVec_last, hBz]
          simp [Pi.single_apply]
      | cast j =>
          rw [graphMatrix_mulVec_castSucc, hBz]
          simp [Pi.single_apply, Fin.castSucc_ne_last]
    have horth := signedNormal_mulVec F z
    rw [hFz] at horth
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq'] at horth
    exact sub_eq_zero.mp (by simpa [F, hlast] using horth)

private lemma signedNormal_minor {d : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) (i : Fin (d + 1)) :
    signedNormal M i = (-1 : R) ^ ((i : ℕ) + d) *
      (M.submatrix i.succAbove id).det := by
  let H := normalAug M (fun j : Fin (d + 1) => if i = j then (1 : R) else 0)
  change H.det = _
  rw [Matrix.det_succ_column H (Fin.last d)]
  rw [Finset.sum_eq_single i]
  · have hminor : H.submatrix i.succAbove (Fin.last d).succAbove =
        M.submatrix i.succAbove id := by
      ext j k
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, H,
        normalAug_castSucc, id_eq]
    simp only [Fin.val_last, H, normalAug_last, ite_true, mul_one, hminor]
  · intro j hj hjne
    have hzero : H j (Fin.last d) = 0 := by
      simp only [H, normalAug_last, if_neg (Ne.symm hjne)]
    simp only [hzero, mul_zero, zero_mul]
  · simp

private lemma signedNormal_smul {d : ℕ} {R : Type*} [CommRing R]
    (M : Matrix (Fin (d + 1)) (Fin d) R) (r : R) (i : Fin (d + 1)) :
    signedNormal (r • M) i = r ^ d * signedNormal M i := by
  rw [signedNormal_minor, signedNormal_minor]
  have hsub : (r • M).submatrix i.succAbove id =
      r • M.submatrix i.succAbove id := by ext j k; rfl
  rw [hsub, Matrix.det_smul]
  simp only [Fintype.card_fin]
  ring

private lemma signedNormal_intCast {d : ℕ}
    (M : Matrix (Fin (d + 1)) (Fin d) ℤ) (i : Fin (d + 1)) :
    signedNormal (M.map ((↑) : ℤ → ℚ)) i = ((signedNormal M i : ℤ) : ℚ) := by
  rw [signedNormal_minor, signedNormal_minor]
  have hsub : ((M.map ((↑) : ℤ → ℚ)).submatrix i.succAbove id).det =
      ((M.submatrix i.succAbove id).det : ℚ) := by
    simpa only [Matrix.submatrix_apply, Matrix.map_apply,
      RingHom.mapMatrix_apply, Int.castRingHom] using
      ((Int.castRingHom ℚ).map_det (M.submatrix i.succAbove id)).symm
  rw [hsub]
  push_cast
  rfl

/-- Smith diagonalization of a nonsingular integer square matrix, with the
unimodular transformations retained as integer matrices. -/
private lemma integral_diagonalization {d : ℕ}
    (C : Matrix (Fin d) (Fin d) ℤ) (hC : C.det ≠ 0) :
    ∃ (U V : Matrix (Fin d) (Fin d) ℤ) (a : Fin d → ℤ),
      IsUnit U.det ∧ IsUnit V.det ∧ U * C * V = Matrix.diagonal a := by
  let f : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ) := C.mulVecLin
  have hf : Function.Injective f := by
    intro z w hzw
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_mulVec_eq_zero hC
    have hz : f (z - w) = 0 := by rw [map_sub, sub_eq_zero.mpr hzw]
    exact hz
  let L := LinearMap.range f
  have hrank : Module.finrank ℤ L = Module.finrank ℤ (Fin d → ℤ) :=
    LinearMap.finrank_range_of_inj hf
  obtain ⟨bM, a, bN, hsnf⟩ :=
    L.exists_smith_normal_form_of_rank_eq (Pi.basisFun ℤ (Fin d)) hrank
  let e : (Fin d → ℤ) ≃ₗ[ℤ] L := LinearEquiv.ofInjective f hf
  let bD : Module.Basis (Fin d) ℤ (Fin d → ℤ) := bN.map e.symm
  have hrel (j : Fin d) : f (bD j) = a j • bM j := by
    have he : f (bD j) = (bN j : Fin d → ℤ) := by
      change f (e.symm (bN j)) = (bN j : Fin d → ℤ)
      exact congrArg Subtype.val (e.apply_symm_apply (bN j))
    exact he.trans (hsnf j)
  let U : Matrix (Fin d) (Fin d) ℤ :=
    LinearMap.toMatrix' bM.equivFun.toLinearMap
  let V : Matrix (Fin d) (Fin d) ℤ :=
    LinearMap.toMatrix' bD.equivFun.symm.toLinearMap
  have hU : IsUnit U.det := by
    simpa only [U, ← LinearMap.toMatrix_eq_toMatrix'] using
      (bM.equivFun.isUnit_det (Pi.basisFun ℤ (Fin d)) (Pi.basisFun ℤ (Fin d)))
  have hV : IsUnit V.det := by
    simpa only [V, ← LinearMap.toMatrix_eq_toMatrix'] using
      (bD.equivFun.symm.isUnit_det (Pi.basisFun ℤ (Fin d))
        (Pi.basisFun ℤ (Fin d)))
  refine ⟨U, V, a, hU, hV, ?_⟩
  ext i j
  have hbD : bD.equivFun.symm (Pi.single j 1) = bD j := by
    apply bD.equivFun.injective
    simp only [bD.equivFun.apply_symm_apply]
    ext k
    simp [Pi.single_apply, eq_comm]
  have hleft : (U * C * V).mulVec (Pi.single j 1) =
      bM.equivFun (f (bD j)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [U, V, LinearMap.toMatrix'_mulVec, f, Matrix.mulVecLin_apply]
    exact congrArg (fun v => bM.equivFun (C.mulVec v)) hbD
  have hentry := congrFun hleft i
  simp only [hrel j, map_smul, Pi.smul_apply, bM.equivFun_self] at hentry
  by_cases hij : i = j
  · subst j
    simpa [Matrix.mulVec_single_one, Matrix.diagonal_apply] using hentry
  · simpa [Matrix.mulVec_single_one, Matrix.diagonal_apply, hij, Ne.symm hij] using hentry

/-- Unimodular row change: transform the top coordinates by `U`, and take
the sum of all original coordinates as the final coordinate. -/
private def graphRowTransform {d : ℕ} {R : Type*} [CommRing R]
    (U : Matrix (Fin d) (Fin d) R) :
    (Fin (d + 1) → R) →ₗ[R] (Fin (d + 1) → R) where
  toFun u := Fin.snoc (U.mulVec (Fin.init u))
    ((∑ i : Fin d, u i.castSucc) + u (Fin.last d))
  map_add' u v := by
    funext i
    induction i using Fin.lastCases with
    | last => simp [Fin.snoc_last, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]
    | cast i =>
        simp only [Fin.snoc_castSucc, Pi.add_apply]
        have hinit : Fin.init (u + v) = Fin.init u + Fin.init v := rfl
        rw [hinit, Matrix.mulVec_add]
        rfl
  map_smul' r u := by
    funext i
    induction i using Fin.lastCases with
    | last => simp [Fin.snoc_last, Finset.mul_sum, smul_eq_mul, mul_add]
    | cast i =>
        simp only [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]
        have hinit : Fin.init (r • u) = r • Fin.init u := rfl
        rw [hinit, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        simp

private noncomputable def graphRowInverse {d : ℕ} {R : Type*} [CommRing R]
    (U : Matrix (Fin d) (Fin d) R) (v : Fin (d + 1) → R) :
    Fin (d + 1) → R :=
  Fin.snoc (U⁻¹.mulVec (Fin.init v))
    (v (Fin.last d) - ∑ i : Fin d, U⁻¹.mulVec (Fin.init v) i)

private lemma graphRow_rightInverse {d : ℕ} {R : Type*} [CommRing R]
    (U : Matrix (Fin d) (Fin d) R) (hU : IsUnit U.det)
    (v : Fin (d + 1) → R) :
    graphRowTransform U (graphRowInverse U v) = v := by
  funext i
  induction i using Fin.lastCases with
  | last =>
      simp [graphRowTransform, graphRowInverse, Fin.snoc_last, Fin.snoc_castSucc]
  | cast i =>
      simp only [graphRowTransform, graphRowInverse, LinearMap.coe_mk,
        AddHom.coe_mk, Fin.snoc_castSucc, Fin.init_snoc]
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv U hU,
        Matrix.one_mulVec]
      rfl

private lemma graphRow_leftInverse {d : ℕ} {R : Type*} [CommRing R]
    (U : Matrix (Fin d) (Fin d) R) (hU : IsUnit U.det)
    (v : Fin (d + 1) → R) :
    graphRowInverse U (graphRowTransform U v) = v := by
  funext i
  induction i using Fin.lastCases with
  | last =>
      have htop : U⁻¹.mulVec (U.mulVec (Fin.init v)) = Fin.init v := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul U hU,
          Matrix.one_mulVec]
      simp only [graphRowTransform, graphRowInverse, LinearMap.coe_mk,
        AddHom.coe_mk, Fin.snoc_last, Fin.init_snoc, htop]
      change (∑ j : Fin d, v j.castSucc) + v (Fin.last d) -
        (∑ j : Fin d, v j.castSucc) = v (Fin.last d)
      abel
  | cast i =>
      simp only [graphRowTransform, graphRowInverse, LinearMap.coe_mk,
        AddHom.coe_mk, Fin.snoc_castSucc, Fin.init_snoc]
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul U hU,
        Matrix.one_mulVec]
      rfl

private noncomputable def graphRowEquiv {d : ℕ} {R : Type*} [CommRing R]
    (U : Matrix (Fin d) (Fin d) R) (hU : IsUnit U.det) :
    (Fin (d + 1) → R) ≃ₗ[R] (Fin (d + 1) → R) :=
  LinearEquiv.ofBijective (graphRowTransform U) ⟨
    (fun x y h => by
      have h' := congrArg (graphRowInverse U) h
      simpa only [graphRow_leftInverse U hU] using h'),
    (fun y => ⟨graphRowInverse U y, graphRow_rightInverse U hU y⟩)⟩

private def shiftMatrix {d : ℕ} {R : Type*} [Zero R] [One R] :
    Matrix (Fin (d + 1)) (Fin d) R :=
  fun i j => if i = j.succ then 1 else 0

private def diagGraph {d : ℕ} {R : Type*} [Zero R] [One R]
    (a : Fin d → R) : Matrix (Fin (d + 1)) (Fin d) R :=
  fun i j => (Fin.snoc (fun k : Fin d => Matrix.diagonal a k j) (0 : R) :
    Fin (d + 1) → R) i

private lemma rowTransform_graph {d : ℕ} {R : Type*} [CommRing R]
    (U C : Matrix (Fin d) (Fin d) R) (z : Fin d → R) :
    graphRowTransform U ((graphMatrix C).mulVec z) =
      Fin.snoc (U.mulVec (C.mulVec z)) 0 := by
  funext i
  induction i using Fin.lastCases with
  | last =>
      simp only [graphRowTransform, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last,
        graphMatrix_mulVec_last]
      simp only [graphMatrix_mulVec_castSucc, add_neg_cancel]
  | cast i =>
      simp only [graphRowTransform, LinearMap.coe_mk, AddHom.coe_mk,
        Fin.snoc_castSucc]
      have htop : Fin.init ((graphMatrix C).mulVec z) = C.mulVec z := by
        ext j
        exact graphMatrix_mulVec_castSucc C z j
      rw [htop]

private lemma rowTransform_graph_matrix {d : ℕ} {R : Type*} [CommRing R]
    (U C V : Matrix (Fin d) (Fin d) R) (hU : IsUnit U.det)
    (a : Fin d → R) (hdiag : U * C * V = Matrix.diagonal a) :
    (LinearMap.toMatrix' (graphRowEquiv U hU).toLinearMap) * graphMatrix C * V =
      diagGraph a := by
  let W := LinearMap.toMatrix' (graphRowEquiv U hU).toLinearMap
  ext i j
  have hvec : (W * graphMatrix C * V).mulVec (Pi.single j 1) =
      Fin.snoc ((Matrix.diagonal a).mulVec (Pi.single j 1)) (0 : R) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp only [W, LinearMap.toMatrix'_mulVec]
    change graphRowTransform U ((graphMatrix C).mulVec (V.mulVec (Pi.single j 1))) = _
    rw [rowTransform_graph]
    congr 1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdiag]
  have hentry := congrFun hvec i
  simpa only [W, Matrix.mulVec_single_one, Matrix.col_apply, diagGraph] using hentry

private lemma diagGraph_succ_eq_zero {d : ℕ} {R : Type*} [CommRing R]
    (a : Fin d → R) (i j : Fin d) (hji : (j : ℕ) ≤ (i : ℕ)) :
    diagGraph a i.succ j = 0 := by
  by_cases h : (i.succ : Fin (d + 1)).val < d
  · have hne : (Fin.castLT i.succ h) ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castLT, Fin.val_succ] at hv
      omega
    have hp : (i : ℕ) + 1 < d := by simpa only [Fin.val_succ] using h
    simp [diagGraph, Fin.snoc, hp, hne]
  · have hn : ¬ ((i : ℕ) + 1 < d) := by simpa only [Fin.val_succ] using h
    simp [diagGraph, Fin.snoc, hn]

private lemma downShift_tail_det {d : ℕ} {R : Type*} [CommRing R]
    (a : Fin d → R) (k : R) :
    ((k • diagGraph a + shiftMatrix).submatrix Fin.succ id).det = 1 := by
  let P : Matrix (Fin d) (Fin d) R :=
    (k • diagGraph a + shiftMatrix).submatrix Fin.succ id
  have htri : P.BlockTriangular id := by
    intro i j hji
    have hh := diagGraph_succ_eq_zero a i j (by exact_mod_cast hji.le)
    have hneq : i.succ ≠ j.succ := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_succ] at hv
      exact (Nat.ne_of_gt hji) (Nat.add_right_cancel hv)
    simp [P, Matrix.submatrix_apply, shiftMatrix, hh, hneq]
  have hones (i : Fin d) : P i i = 1 := by
    have hh := diagGraph_succ_eq_zero a i i le_rfl
    simp [P, Matrix.submatrix_apply, shiftMatrix, hh]
  rw [Matrix.det_of_upperTriangular htri]
  simp [hones]

/-- A fixed correction `E` makes every `k F + E` a primitive integer
column lattice: in Smith coordinates its lower square minor is identically one. -/
private lemma exists_primitive_lift {d : ℕ}
    (C : Matrix (Fin d) (Fin d) ℤ) (hC : C.det ≠ 0) :
    ∃ (W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ)
        (V : Matrix (Fin d) (Fin d) ℤ)
        (E : Matrix (Fin (d + 1)) (Fin d) ℤ) (a : Fin d → ℤ),
      IsUnit W.det ∧ IsUnit V.det ∧
        ∀ k : ℤ, W * (k • graphMatrix C + E) * V =
          k • diagGraph a + shiftMatrix := by
  obtain ⟨U, V, a, hU, hV, hdiag⟩ := integral_diagonalization C hC
  let eW := graphRowEquiv U hU
  let W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ :=
    LinearMap.toMatrix' eW.toLinearMap
  have hW : IsUnit W.det := by
    simpa only [W, ← LinearMap.toMatrix_eq_toMatrix'] using
      (eW.isUnit_det (Pi.basisFun ℤ (Fin (d + 1)))
        (Pi.basisFun ℤ (Fin (d + 1))))
  let E : Matrix (Fin (d + 1)) (Fin d) ℤ :=
    W⁻¹ * (shiftMatrix (d := d) (R := ℤ)) * V⁻¹
  refine ⟨W, V, E, a, hW, hV, ?_⟩
  have hbase : W * graphMatrix C * V = diagGraph a :=
    rowTransform_graph_matrix U C V hU a hdiag
  have hcorr : W * E * V = shiftMatrix := by
    dsimp only [E]
    calc
      W * (W⁻¹ * (shiftMatrix (d := d) (R := ℤ)) * V⁻¹) * V =
          W * W⁻¹ * ((shiftMatrix (d := d) (R := ℤ)) * V⁻¹ * V) := by
        simp only [Matrix.mul_assoc]
      _ = shiftMatrix := by
        rw [Matrix.mul_nonsing_inv W hW, Matrix.one_mul,
          Matrix.nonsing_inv_mul_cancel_right V (shiftMatrix (d := d) (R := ℤ)) hV]
  intro k
  calc
    W * (k • graphMatrix C + E) * V =
        k • (W * graphMatrix C * V) + W * E * V := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = k • diagGraph a + shiftMatrix := by rw [hbase, hcorr]















/- A nonzero cofactor makes the normal equation precisely the rational column span. -/
private lemma signedNormal_span {d : ℕ}
    (M : Matrix (Fin (d + 1)) (Fin d) ℚ) (i : Fin (d + 1))
    (hi : signedNormal M i ≠ 0) (u : Fin (d + 1) → ℚ)
    (hu : (∑ j, signedNormal M j * u j) = 0) :
    ∃ z : Fin d → ℚ, M.mulVec z = u := by
  let P : Matrix (Fin d) (Fin d) ℚ := M.submatrix i.succAbove id
  have hPdet : P.det ≠ 0 := by
    intro hp
    apply hi
    rw [signedNormal_minor]
    simp [P, hp]
  have hP : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdet
  let z : Fin d → ℚ := P⁻¹.mulVec (u ∘ i.succAbove)
  have htail (j : Fin d) : M.mulVec z (i.succAbove j) = u (i.succAbove j) := by
    have hp : P.mulVec z = u ∘ i.succAbove := by
      change P.mulVec (P⁻¹.mulVec (u ∘ i.succAbove)) = _
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
    simpa only [P, Matrix.mulVec, Matrix.submatrix_apply, dotProduct,
      Function.comp_apply] using congrFun hp j
  have horth := signedNormal_mulVec M z
  have hzero : (∑ j, signedNormal M j * (u j - M.mulVec z j)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, hu, horth, sub_self]
  have hsingle : (∑ j, signedNormal M j * (u j - M.mulVec z j)) =
      signedNormal M i * (u i - M.mulVec z i) := by
    apply Finset.sum_eq_single i
    · intro j _ hj
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hj
      rw [← hr, htail, sub_self, mul_zero]
    · simp
  have hfirst : M.mulVec z i = u i := by
    have hh : signedNormal M i * (u i - M.mulVec z i) = 0 :=
      hsingle.symm.trans hzero
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hi)).symm
  refine ⟨z, funext (fun j => ?_)⟩
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨r, rfl⟩
  · exact hfirst
  · exact htail r

private lemma intMatrix_cast_mulVec {m n : Type*} [Fintype n]
    (T : Matrix m n ℤ) (v : n → ℤ) :
    (T.map ((↑) : ℤ → ℚ)).mulVec (fun j => (v j : ℚ)) =
      fun i => ((T.mulVec v i : ℤ) : ℚ) := by
  funext i
  exact ((Int.castRingHom ℚ).map_mulVec T v i).symm

/-- An integer column lattice with a unit maximal minor after integral row and
column operations is saturated inside its rational column span. -/
private lemma integral_span_of_unit_tail {d : ℕ}
    (M : Matrix (Fin (d + 1)) (Fin d) ℤ)
    (W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ)
    (V : Matrix (Fin d) (Fin d) ℤ)
    (H : Matrix (Fin (d + 1)) (Fin d) ℤ)
    (hW : IsUnit W.det) (hV : IsUnit V.det)
    (hmat : W * M * V = H)
    (hP : IsUnit (H.submatrix Fin.succ id).det)
    (u : Fin (d + 1) → ℤ)
    (hspan : ∃ z : Fin d → ℚ,
      (M.map ((↑) : ℤ → ℚ)).mulVec z = fun i => (u i : ℚ)) :
    ∃ z : Fin d → ℤ, M.mulVec z = u := by
  let P : Matrix (Fin d) (Fin d) ℤ := H.submatrix Fin.succ id
  let v := W.mulVec u
  let r : Fin d → ℤ := P⁻¹.mulVec (v ∘ Fin.succ)
  have hPr : P.mulVec r = v ∘ Fin.succ := by
    change P.mulVec (P⁻¹.mulVec (v ∘ Fin.succ)) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
  let f := (Int.castRingHom ℚ)
  let Wq : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ := W.map f
  let Mq : Matrix (Fin (d + 1)) (Fin d) ℚ := M.map f
  let Vq : Matrix (Fin d) (Fin d) ℚ := V.map f
  let Hq : Matrix (Fin (d + 1)) (Fin d) ℚ := H.map f
  let Pq : Matrix (Fin d) (Fin d) ℚ := P.map f
  have hVq : IsUnit Vq.det := by
    change IsUnit (f.mapMatrix V).det
    rw [← f.map_det]
    exact hV.map f
  have hPq : IsUnit Pq.det := by
    change IsUnit (f.mapMatrix P).det
    rw [← f.map_det]
    exact hP.map f
  have hmq : Wq * Mq * Vq = Hq := by
    simpa only [Wq, Mq, Vq, Hq, ← Matrix.map_mul] using
      congrArg (fun X : Matrix (Fin (d + 1)) (Fin d) ℤ => X.map f) hmat
  obtain ⟨z, hz⟩ := hspan
  let z' : Fin d → ℚ := Vq⁻¹.mulVec z
  have hVzin : Vq.mulVec z' = z := by
    change Vq.mulVec (Vq⁻¹.mulVec z) = z
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Vq hVq, Matrix.one_mulVec]
  have hHz : Hq.mulVec z' = fun i => (v i : ℚ) := by
    calc
      Hq.mulVec z' = (Wq * Mq * Vq).mulVec z' := by rw [hmq]
      _ = Wq.mulVec (Mq.mulVec (Vq.mulVec z')) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = Wq.mulVec (Mq.mulVec z) := by rw [hVzin]
      _ = Wq.mulVec (fun i => (u i : ℚ)) := by
        exact congrArg (Wq.mulVec) (show Mq.mulVec z = _ from hz)
      _ = fun i => (v i : ℚ) := intMatrix_cast_mulVec W u
  have hPz : Pq.mulVec z' = fun j => (v j.succ : ℚ) := by
    funext j
    have h := congrFun hHz j.succ
    simpa only [Pq, P, Hq, Matrix.mulVec, Matrix.submatrix_apply,
      Matrix.map_apply, RingHom.mapMatrix_apply, dotProduct] using h
  have hrz : (fun j => (r j : ℚ)) = z' := by
    have heq : Pq.mulVec (fun j => (r j : ℚ)) = Pq.mulVec z' := by
      have hcast : Pq.mulVec (fun j => (r j : ℚ)) =
          fun j => ((P.mulVec r j : ℤ) : ℚ) := intMatrix_cast_mulVec P r
      rw [hcast, hPz]
      exact funext (fun j => congrArg (fun x : ℤ => (x : ℚ)) (congrFun hPr j))
    have heq' := congrArg (Pq⁻¹.mulVec) heq
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Pq hPq,
      Matrix.one_mulVec] using heq'
  have hHr : H.mulVec r = v := by
    funext j
    have hh : ((H.mulVec r j : ℤ) : ℚ) = (v j : ℚ) := by
      have h := congrFun hHz j
      rw [← hrz] at h
      change (H.map ((↑) : ℤ → ℚ)).mulVec (fun k => (r k : ℚ)) j = _ at h
      exact (congrFun (intMatrix_cast_mulVec H r) j).symm.trans h
    exact_mod_cast hh
  have hWMr : W.mulVec (M.mulVec (V.mulVec r)) = W.mulVec u := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
    exact hHr
  refine ⟨V.mulVec r, ?_⟩
  have hh := congrArg (W⁻¹.mulVec) hWMr
  rw [Matrix.mulVec_mulVec (M.mulVec (V.mulVec r)) W⁻¹ W,
    Matrix.mulVec_mulVec u W⁻¹ W,
    Matrix.nonsing_inv_mul W hW] at hh
  simpa only [Matrix.one_mulVec] using hh

/-- The Smith shift identifies the *entire integral normal kernel*, not just its
rational span, with the column lattice. -/
private lemma primitive_lift_kernel {d : ℕ}
    (M : Matrix (Fin (d + 1)) (Fin d) ℤ)
    (W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ)
    (V : Matrix (Fin d) (Fin d) ℤ) (a : Fin d → ℤ) (k : ℤ)
    (hW : IsUnit W.det) (hV : IsUnit V.det)
    (hmat : W * M * V = k • diagGraph a + shiftMatrix)
    (ht : signedNormal M (Fin.last d) ≠ 0)
    (u : Fin (d + 1) → ℤ)
    (hu : (∑ i, signedNormal M i * u i) = 0) :
    ∃ z : Fin d → ℤ, M.mulVec z = u := by
  let Mq := M.map ((↑) : ℤ → ℚ)
  have htq : signedNormal Mq (Fin.last d) ≠ 0 := by
    change signedNormal (M.map ((↑) : ℤ → ℚ)) (Fin.last d) ≠ 0
    rw [signedNormal_intCast]
    exact_mod_cast ht
  have huq : (∑ i, signedNormal Mq i * (u i : ℚ)) = 0 := by
    change (∑ i, signedNormal (M.map ((↑) : ℤ → ℚ)) i * (u i : ℚ)) = 0
    simpa only [signedNormal_intCast, ← Int.cast_mul,
      ← Int.cast_sum, Int.cast_zero] using congrArg (fun x : ℤ => (x : ℚ)) hu
  obtain ⟨z, hz⟩ := signedNormal_span Mq (Fin.last d) htq
    (fun i => (u i : ℚ)) huq
  exact integral_span_of_unit_tail M W V (k • diagGraph a + shiftMatrix)
    hW hV hmat (by rw [downShift_tail_det]; exact isUnit_one) u ⟨z, hz⟩

open scoped Matrix.Norms.Operator Topology
open Filter

private lemma rat_abs_lt_one_of_norm {x : ℚ} (hx : ‖x‖ < (1 : ℝ)) : |x| < 1 := by
  have hh : (|x| : ℝ) < 1 := by
    simpa only [Rat.cast_abs, ← Real.norm_eq_abs, Rat.norm_cast_real] using hx
  exact_mod_cast hh

/-- Admissibility gives a uniform non-strict gap for the original graph at
all nonzero integer arguments. -/
private lemma good_graph_norm_ge_one {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℚ) (hgood : CubeSlabAdmissible B)
    (z : Fin d → ℤ) (hz : z ≠ 0) :
    (1 : ℝ) ≤ ‖(graphMatrix B).mulVec (fun j => (z j : ℚ))‖ := by
  let v : Fin d → ℚ := fun j => (z j : ℚ)
  let F := graphMatrix B
  by_contra hn
  have hsmall : ‖F.mulVec v‖ < (1 : ℝ) := lt_of_not_ge hn
  apply hz
  apply hgood z
  · intro i
    have hi := (norm_le_pi_norm (F.mulVec v) i.castSucc).trans_lt hsmall
    rw [graphMatrix_mulVec_castSucc] at hi
    exact rat_abs_lt_one_of_norm hi
  · have hi := (norm_le_pi_norm (F.mulVec v) (Fin.last d)).trans_lt hsmall
    rw [graphMatrix_mulVec_last, norm_neg] at hi
    exact rat_abs_lt_one_of_norm hi

/-- The inverse of the top square block controls all integer preimages of
the graph, with the operator and vector sup norms. -/
private lemma graph_inverse_norm_bound {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℚ) (hdet : B.det ≠ 0)
    (v : Fin d → ℚ) :
    ‖v‖ ≤ ‖B⁻¹‖ * ‖(graphMatrix B).mulVec v‖ := by
  let F := graphMatrix B
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have htop : ‖B.mulVec v‖ ≤ ‖F.mulVec v‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [F, graphMatrix_mulVec_castSucc] using
      (norm_le_pi_norm (F.mulVec v) i.castSucc)
  have hvinv : v = B⁻¹.mulVec (B.mulVec v) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hB, Matrix.one_mulVec]
  calc
    ‖v‖ = ‖B⁻¹.mulVec (B.mulVec v)‖ := congrArg norm hvinv
    _ ≤ ‖B⁻¹‖ * ‖B.mulVec v‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ ‖B⁻¹‖ * ‖F.mulVec v‖ := mul_le_mul_of_nonneg_left htop (norm_nonneg _)

/-- A small operator-norm perturbation of a strictly dilated graph has
no nonzero lattice point even on the closed unit cube. -/
private lemma close_graph_gap {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℚ) (hdet : B.det ≠ 0)
    (hgood : CubeSlabAdmissible B) (lam : ℚ) (hlam : 1 < lam)
    (X : Matrix (Fin (d + 1)) (Fin d) ℚ)
    (hclose : ‖X - lam • graphMatrix B‖ * ‖B⁻¹‖ < (lam : ℝ) - 1)
    (z : Fin d → ℤ) (hz : z ≠ 0) :
    (1 : ℝ) < ‖X.mulVec (fun j => (z j : ℚ))‖ := by
  let F := graphMatrix B
  let v : Fin d → ℚ := fun j => (z j : ℚ)
  let G := lam • F
  have hF : (1 : ℝ) ≤ ‖F.mulVec v‖ := good_graph_norm_ge_one B hgood z hz
  have hv : ‖v‖ ≤ ‖B⁻¹‖ * ‖F.mulVec v‖ :=
    graph_inverse_norm_bound B hdet v
  have herror : ‖(X - G).mulVec v‖ ≤
      (‖X - G‖ * ‖B⁻¹‖) * ‖F.mulVec v‖ := by
    calc
      _ ≤ ‖X - G‖ * ‖v‖ := Matrix.linfty_opNorm_mulVec _ _
      _ ≤ ‖X - G‖ * (‖B⁻¹‖ * ‖F.mulVec v‖) :=
        mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ = (‖X - G‖ * ‖B⁻¹‖) * ‖F.mulVec v‖ := by ring
  have hG : ‖G.mulVec v‖ = (lam : ℝ) * ‖F.mulVec v‖ := by
    change ‖(lam • F).mulVec v‖ = _
    rw [Matrix.smul_mulVec, norm_smul]
    congr 1
    rw [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (by exact_mod_cast (lt_trans (by norm_num) hlam))]
  have htriangle : ‖G.mulVec v‖ ≤ ‖X.mulVec v‖ + ‖(X - G).mulVec v‖ := by
    calc
      ‖G.mulVec v‖ = ‖X.mulVec v - (X - G).mulVec v‖ := by
        rw [Matrix.sub_mulVec]
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  have hcoeff : 1 < (lam : ℝ) - ‖X - G‖ * ‖B⁻¹‖ := by
    have hh : ‖X - G‖ * ‖B⁻¹‖ < (lam : ℝ) - 1 := hclose
    linarith
  have hscale : 1 < ((lam : ℝ) - ‖X - G‖ * ‖B⁻¹‖) * ‖F.mulVec v‖ := by
    have ht : (lam : ℝ) - ‖X - G‖ * ‖B⁻¹‖ ≤
        ((lam : ℝ) - ‖X - G‖ * ‖B⁻¹‖) * ‖F.mulVec v‖ := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hF (by linarith :
          0 ≤ (lam : ℝ) - ‖X - G‖ * ‖B⁻¹‖))
    exact hcoeff.trans_le ht
  linarith

/-- Floor division does not alter the asymptotic ratio. -/
private lemma quotient_ratio_tendsto (D : ℕ) (hD : 0 < D) :
    Filter.Tendsto (fun q : ℕ => ((q / D : ℕ) : ℚ) / (q : ℚ))
      Filter.atTop (𝓝 (1 / (D : ℚ))) := by
  have hreal : Filter.Tendsto
      (fun q : ℕ => ((q / D : ℕ) : ℝ) / (q : ℝ))
      Filter.atTop (𝓝 (1 / (D : ℝ))) := by
    have ht := (tendsto_nat_floor_mul_div_atTop
      (a := 1 / (D : ℝ)) (by positivity)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have heq (q : ℕ) : ⌊(1 / (D : ℝ)) * (q : ℝ)⌋₊ = q / D := by
      rw [show (1 / (D : ℝ)) * (q : ℝ) = (q : ℝ) / D by ring,
        Nat.floor_div_eq_div]
    change Filter.Tendsto
      (fun q : ℕ => ((⌊(1 / (D : ℝ)) * (q : ℝ)⌋₊ : ℝ) / (q : ℝ)))
      Filter.atTop (𝓝 (1 / (D : ℝ))) at ht
    simpa only [heq] using ht
  apply (Rat.isEmbedding_coe_real.tendsto_nhds_iff).2
  simpa only [Function.comp_def, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_one] using hreal

private lemma two_pow_succ_tendsto_atTop :
    Filter.Tendsto (fun s : ℕ => 2 ^ (s + 1)) Filter.atTop Filter.atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℕ) < 2)).comp (Filter.tendsto_add_atTop_nat 1)

private def liftedMatrix {d : ℕ} (C : Matrix (Fin d) (Fin d) ℤ)
    (E : Matrix (Fin (d + 1)) (Fin d) ℤ) (D s : ℕ) :
    Matrix (Fin (d + 1)) (Fin d) ℤ :=
  (((2 ^ (s + 1) / D : ℕ) : ℤ) • graphMatrix C) + E

private def normalizedLift {d : ℕ} (C : Matrix (Fin d) (Fin d) ℤ)
    (E : Matrix (Fin (d + 1)) (Fin d) ℤ) (D s : ℕ) :
    Matrix (Fin (d + 1)) (Fin d) ℚ :=
  (1 / ((2 ^ (s + 1) : ℕ) : ℚ)) • (liftedMatrix C E D s).map ((↑) : ℤ → ℚ)

private lemma normalizedLift_tendsto {d : ℕ}
    (C : Matrix (Fin d) (Fin d) ℤ)
    (E : Matrix (Fin (d + 1)) (Fin d) ℤ) (D : ℕ) (hD : 0 < D) :
    Filter.Tendsto (normalizedLift C E D) Filter.atTop
      (𝓝 ((1 / (D : ℚ)) • (graphMatrix C).map ((↑) : ℤ → ℚ))) := by
  let q : ℕ → ℕ := fun s => 2 ^ (s + 1)
  let k : ℕ → ℕ := fun s => q s / D
  let F : Matrix (Fin (d + 1)) (Fin d) ℚ := (graphMatrix C).map ((↑) : ℤ → ℚ)
  let E' : Matrix (Fin (d + 1)) (Fin d) ℚ := E.map ((↑) : ℤ → ℚ)
  have hratio : Filter.Tendsto (fun s => ((k s : ℕ) : ℚ) / (q s : ℚ))
      Filter.atTop (𝓝 (1 / (D : ℚ))) :=
    (quotient_ratio_tendsto D hD).comp two_pow_succ_tendsto_atTop
  have hq : Filter.Tendsto (fun s => (q s : ℚ)) Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℚ)).comp two_pow_succ_tendsto_atTop
  have hinv : Filter.Tendsto (fun s => 1 / (q s : ℚ)) Filter.atTop (𝓝 0) :=
    hq.const_div_atTop 1
  have heq (s : ℕ) : normalizedLift C E D s =
      (((k s : ℕ) : ℚ) / (q s : ℚ)) • F + (1 / (q s : ℚ)) • E' := by
    ext i j
    have hdef : normalizedLift C E D s =
        (1 / (q s : ℚ)) • (((k s : ℤ) • graphMatrix C + E).map ((↑) : ℤ → ℚ)) := by
      rfl
    rw [hdef]
    simp only [Matrix.smul_apply, Matrix.map_apply,
      Matrix.add_apply, F, E', smul_eq_mul, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, div_eq_mul_inv]
    ring
  have hh := (hratio.smul (tendsto_const_nhds (x := F))).add
    (hinv.smul (tendsto_const_nhds (x := E')))
  have hh' : Filter.Tendsto (fun s =>
      (((k s : ℕ) : ℚ) / (q s : ℚ)) • F + (1 / (q s : ℚ)) • E')
      Filter.atTop (𝓝 ((1 / (D : ℚ)) • F)) := by
    simpa only [zero_smul, add_zero] using hh
  exact hh'.congr' (Filter.Eventually.of_forall fun s => (heq s).symm)

private lemma graphMatrix_intCast {d : ℕ}
    (C : Matrix (Fin d) (Fin d) ℤ) :
    (graphMatrix C).map ((↑) : ℤ → ℚ) =
      graphMatrix (C.map ((↑) : ℤ → ℚ)) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
      simp only [Matrix.map_apply, graphMatrix_last, Int.cast_neg,
        Int.cast_sum]
  | cast i =>
      simp only [Matrix.map_apply, graphMatrix_castSucc]

private lemma graphMatrix_smul {d : ℕ} {R : Type*} [CommRing R]
    (r : R) (B : Matrix (Fin d) (Fin d) R) :
    graphMatrix (r • B) = r • graphMatrix B := by
  ext i j
  induction i using Fin.lastCases with
  | last => simp only [graphMatrix_last, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_neg]
  | cast i => simp only [graphMatrix_castSucc, Matrix.smul_apply,
      smul_eq_mul]

private lemma exists_rational_dilation {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℚ) (c : ℚ) (hc : B.det < c) :
    ∃ lam : ℚ, 1 < lam ∧ lam ^ d * B.det < c := by
  have hcont : ContinuousAt (fun t : ℚ => t ^ d * B.det) 1 := by
    fun_prop
  have hev : ∀ᶠ t : ℚ in 𝓝 1, t ^ d * B.det < c :=
    hcont.tendsto.eventually (eventually_lt_nhds (by simpa using hc))
  have hlim : Filter.Tendsto (fun n : ℕ =>
      (1 : ℚ) + 1 / ((n : ℚ) + 1)) Filter.atTop (𝓝 (1 : ℚ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℚ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℚ))
  obtain ⟨n, hn⟩ := (hlim.eventually hev).exists
  refine ⟨1 + 1 / ((n : ℚ) + 1), ?_, hn⟩
  have h : (0 : ℚ) < 1 / ((n : ℚ) + 1) := by positivity
  linarith

private lemma signedNormal_continuous {d : ℕ} (i : Fin (d + 1)) :
    Continuous (fun X : Matrix (Fin (d + 1)) (Fin d) ℚ => signedNormal X i) := by
  have hminor : Continuous (fun X : Matrix (Fin (d + 1)) (Fin d) ℚ =>
      (X.submatrix i.succAbove id).det) :=
    (continuous_id.matrix_submatrix i.succAbove id).matrix_det
  have hh : Continuous (fun X : Matrix (Fin (d + 1)) (Fin d) ℚ =>
      (-1 : ℚ) ^ ((i : ℕ) + d) * (X.submatrix i.succAbove id).det) :=
    continuous_const.mul hminor
  simpa only [signedNormal_minor] using hh

private lemma numerator_det_ne_zero {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℚ) (hH : H.det ≠ 0) :
    H.num.det ≠ 0 := by
  have hD : ((H.den : ℚ)⁻¹ • H.num.map ((↑) : ℤ → ℚ)) = H :=
    Matrix.inv_denom_smul_num H
  have hCq : (H.num.map ((↑) : ℤ → ℚ)).det ≠ 0 := by
    intro hc
    have hh := congrArg Matrix.det hD
    rw [Matrix.det_smul] at hh
    simp only [Fintype.card_fin, hc, mul_zero] at hh
    exact hH hh.symm
  intro hc
  apply hCq
  have hh := (Int.castRingHom ℚ).map_det H.num
  rw [hc, map_zero] at hh
  exact hh.symm

private lemma normalizedLift_limit {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℚ) (lam : ℚ)
    (E : Matrix (Fin (d + 1)) (Fin d) ℤ) :
    Filter.Tendsto (normalizedLift (lam • B).num E (lam • B).den)
      Filter.atTop (𝓝 (lam • graphMatrix B)) := by
  let H := lam • B
  let C := H.num
  let D := H.den
  have hD : 0 < D := Nat.pos_of_ne_zero H.den_ne_zero
  have ht := normalizedLift_tendsto C E D hD
  have hlim : (1 / (D : ℚ)) • (graphMatrix C).map ((↑) : ℤ → ℚ) =
      lam • graphMatrix B := by
    rw [graphMatrix_intCast, ← graphMatrix_smul]
    have hH : ((D : ℚ)⁻¹ • C.map ((↑) : ℤ → ℚ)) = H :=
      Matrix.inv_denom_smul_num H
    rw [show (1 / (D : ℚ)) = (D : ℚ)⁻¹ by ring, hH,
      graphMatrix_smul]
  simpa only [H, C, D, hlim] using ht

private lemma lifted_cofactor_bounds {d s : ℕ}
    (C : Matrix (Fin d) (Fin d) ℤ)
    (E : Matrix (Fin (d + 1)) (Fin d) ℤ) (D : ℕ)
    (c : ℚ) (i : Fin (d + 1))
    (hi : 0 < signedNormal (normalizedLift C E D s) i ∧
      signedNormal (normalizedLift C E D s) i < c) :
    0 < signedNormal (liftedMatrix C E D s) i ∧
      ((signedNormal (liftedMatrix C E D s) i : ℤ) : ℝ) <
      (c : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ d := by
  let q : ℕ := 2 ^ (s + 1)
  let M := liftedMatrix C E D s
  have hq : (0 : ℚ) < (q : ℚ) := by positivity
  have hqd : (0 : ℚ) < (q : ℚ) ^ d := pow_pos hq d
  have hscale : signedNormal (normalizedLift C E D s) i =
      ((signedNormal M i : ℤ) : ℚ) / (q : ℚ) ^ d := by
    change signedNormal ((1 / (q : ℚ)) • M.map ((↑) : ℤ → ℚ)) i = _
    rw [signedNormal_smul, signedNormal_intCast]
    ring
  have hposq : (0 : ℚ) < (signedNormal M i : ℤ) := by
    have hh := hi.1
    rw [hscale] at hh
    rcases div_pos_iff.mp hh with ⟨hp, _⟩ | ⟨_, hn⟩
    · exact hp
    · exact (not_lt_of_ge hqd.le hn).elim
  have huq : ((signedNormal M i : ℤ) : ℚ) < c * (q : ℚ) ^ d := by
    apply (div_lt_iff₀ hqd).mp
    simpa only [← hscale] using hi.2
  constructor
  · exact_mod_cast hposq
  · have hur : ((signedNormal M i : ℤ) : ℝ) <
        (c : ℝ) * ((q : ℕ) : ℝ) ^ d := by exact_mod_cast huq
    simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using hur

private lemma lifted_kernel_separated {d s : ℕ}
    (B : Matrix (Fin d) (Fin d) ℚ) (hdet : B.det ≠ 0)
    (hgood : CubeSlabAdmissible B) (lam : ℚ) (hlam : 1 < lam)
    (C : Matrix (Fin d) (Fin d) ℤ)
    (E : Matrix (Fin (d + 1)) (Fin d) ℤ) (D : ℕ)
    (W : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ)
    (V : Matrix (Fin d) (Fin d) ℤ) (a : Fin d → ℤ)
    (hW : IsUnit W.det) (hV : IsUnit V.det)
    (hmat : W * liftedMatrix C E D s * V =
      (((2 ^ (s + 1) / D : ℕ) : ℤ) • diagGraph a) + shiftMatrix)
    (htpos : ∀ i, 0 < signedNormal (liftedMatrix C E D s) i)
    (hclose : ‖normalizedLift C E D s - lam • graphMatrix B‖ * ‖B⁻¹‖ <
      (lam : ℝ) - 1) :
    ∀ u : Fin (d + 1) → ℤ,
      (∀ i, |u i| < (2 ^ (s + 1) : ℤ)) →
      (∑ i, (((signedNormal (liftedMatrix C E D s) i).toNat : ℕ) : ℤ) * u i) = 0 →
      u = 0 := by
  let q : ℕ := 2 ^ (s + 1)
  let M := liftedMatrix C E D s
  let X := normalizedLift C E D s
  have hq : (0 : ℚ) < (q : ℚ) := by positivity
  intro u huBound huSum
  have hcast (i : Fin (d + 1)) : ((signedNormal M i).toNat : ℤ) =
      signedNormal M i := Int.toNat_of_nonneg (htpos i).le
  have huM : (∑ i, signedNormal M i * u i) = 0 := by
    change (∑ i, ((signedNormal M i).toNat : ℤ) * u i) = 0 at huSum
    simpa only [hcast] using huSum
  obtain ⟨z, hz⟩ := primitive_lift_kernel M W V a ((q / D : ℕ) : ℤ)
    hW hV hmat (htpos (Fin.last d)).ne' u huM
  by_cases hz0 : z = 0
  · simpa [hz0] using hz.symm
  have hlarge : (1 : ℝ) < ‖X.mulVec (fun j => (z j : ℚ))‖ :=
    close_graph_gap B hdet hgood lam hlam X hclose z hz0
  have hMV : (M.map ((↑) : ℤ → ℚ)).mulVec (fun j => (z j : ℚ)) =
      fun i => (u i : ℚ) := by
    rw [intMatrix_cast_mulVec M z, hz]
  have hentry (i : Fin (d + 1)) :
      X.mulVec (fun j => (z j : ℚ)) i = (u i : ℚ) / (q : ℚ) := by
    change ((1 / (q : ℚ)) • (M.map ((↑) : ℤ → ℚ))).mulVec
      (fun j => (z j : ℚ)) i = _
    rw [Matrix.smul_mulVec, hMV]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsmall : ‖X.mulVec (fun j => (z j : ℚ))‖ < (1 : ℝ) := by
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).2
    intro i
    rw [hentry i]
    have hiQ : |(u i : ℚ)| < (q : ℚ) := by
      have hu := huBound i
      have hh : ((|u i| : ℤ) : ℚ) < (q : ℚ) := by
        exact_mod_cast hu
      simpa only [Int.cast_abs] using hh
    have hrat : |(u i : ℚ) / (q : ℚ)| < 1 := by
      rw [abs_div, abs_of_pos hq]
      exact (div_lt_one hq).mpr hiQ
    have hr : ((|(u i : ℚ) / (q : ℚ)| : ℚ) : ℝ) < 1 := by
      exact_mod_cast hrat
    simpa only [Rat.cast_abs, ← Real.norm_eq_abs, Rat.norm_cast_real] using hr
  exact (not_lt_of_ge hlarge.le hsmall).elim

/-- A rational cube–slab admissible lattice transfers to arbitrarily large
binary blocks of positive integer weights with distinct subset sums and
exponential maximum bounded by any prescribed determinant slack. -/
theorem transfer_to_small_family {d : ℕ} (hd : 0 < d)
    (B : Matrix (Fin d) (Fin d) ℚ) (hdet : 0 < B.det)
    (hgood : CubeSlabAdmissible B) (c : ℚ) (hc : B.det < c) :
    ∃ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧
      (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective ∧
      N ≠ 0 ∧ (N : ℝ) < (c : ℝ) * 2 ^ A.card := by
  obtain ⟨lam, hlam, hlimc⟩ := exists_rational_dilation B c hc
  let H : Matrix (Fin d) (Fin d) ℚ := lam • B
  let C : Matrix (Fin d) (Fin d) ℤ := H.num
  let D : ℕ := H.den
  have hHdet : H.det ≠ 0 := by
    change (lam • B).det ≠ 0
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin]
    have hpow : (0 : ℚ) < lam ^ d :=
      (by norm_num : (0 : ℚ) < 1).trans (one_lt_pow₀ hlam (Nat.ne_of_gt hd))
    exact mul_ne_zero (ne_of_gt hpow) (ne_of_gt hdet)
  have hCdet : C.det ≠ 0 := numerator_det_ne_zero H hHdet
  obtain ⟨W, V, E, a, hW, hV, hprimitive⟩ := exists_primitive_lift C hCdet
  let G : Matrix (Fin (d + 1)) (Fin d) ℚ := lam • graphMatrix B
  let X : ℕ → Matrix (Fin (d + 1)) (Fin d) ℚ := normalizedLift C E D
  have hX : Filter.Tendsto X Filter.atTop (𝓝 G) := by
    simpa only [X, G, H, C, D] using normalizedLift_limit B lam E
  have hcontinuous_gap : Continuous (fun Y : Matrix (Fin (d + 1)) (Fin d) ℚ =>
      ‖Y - G‖ * ‖B⁻¹‖) := by fun_prop
  have hgap_at_limit : ‖G - G‖ * ‖B⁻¹‖ < (lam : ℝ) - 1 := by
    simp only [sub_self, norm_zero, zero_mul]
    exact_mod_cast sub_pos.mpr hlam
  have hgap_event : ∀ᶠ s : ℕ in Filter.atTop,
      ‖X s - G‖ * ‖B⁻¹‖ < (lam : ℝ) - 1 :=
    hX.eventually (hcontinuous_gap.continuousAt.tendsto.eventually
      (eventually_lt_nhds hgap_at_limit))
  have hnormal_event_i (i : Fin (d + 1)) :
      ∀ᶠ Y : Matrix (Fin (d + 1)) (Fin d) ℚ in 𝓝 G,
        0 < signedNormal Y i ∧ signedNormal Y i < c := by
    have hGnormal : signedNormal G i = lam ^ d * B.det := by
      simpa only [G, signedNormal_smul] using
        congrArg (fun x : ℚ => lam ^ d * x)
          (signedNormal_graph B (ne_of_gt hdet) i)
    have hGpos : 0 < signedNormal G i := by
      rw [hGnormal]
      exact mul_pos (pow_pos (lt_trans (by norm_num) hlam) d) hdet
    have hGupper : signedNormal G i < c := by
      rwa [hGnormal]
    have ht : Filter.Tendsto
        (fun Y : Matrix (Fin (d + 1)) (Fin d) ℚ => signedNormal Y i)
        (𝓝 G) (𝓝 (signedNormal G i)) :=
      (signedNormal_continuous i).continuousAt.tendsto
    exact (ht.eventually (eventually_gt_nhds hGpos)).and
      (ht.eventually (eventually_lt_nhds hGupper))
  have hnormal_event : ∀ᶠ s : ℕ in Filter.atTop,
      ∀ i : Fin (d + 1),
        0 < signedNormal (X s) i ∧ signedNormal (X s) i < c :=
    hX.eventually (Filter.eventually_all.mpr hnormal_event_i)
  obtain ⟨s, hgap, hnormal⟩ := (hgap_event.and hnormal_event).exists
  let M : Matrix (Fin (d + 1)) (Fin d) ℤ := liftedMatrix C E D s
  let t : Fin (d + 1) → ℕ := fun i => (signedNormal M i).toNat
  have htpos (i : Fin (d + 1)) : 0 < signedNormal M i :=
    (lifted_cofactor_bounds C E D c i (hnormal i)).1
  have htnat (i : Fin (d + 1)) : 0 < t i := by
    have hh : ((t i : ℕ) : ℤ) = signedNormal M i :=
      Int.toNat_of_nonneg (htpos i).le
    exact_mod_cast (hh.symm ▸ htpos i)
  have htbound (i : Fin (d + 1)) :
      (t i : ℝ) < (c : ℝ) * ((2 : ℝ) ^ (s + 1)) ^ d := by
    have hb := (lifted_cofactor_bounds C E D c i (hnormal i)).2
    have hh : ((t i : ℕ) : ℤ) = signedNormal M i :=
      Int.toNat_of_nonneg (htpos i).le
    have heq : (t i : ℝ) = ((signedNormal M i : ℤ) : ℝ) := by
      exact_mod_cast hh
    exact heq.trans_lt hb
  have hmat : W * M * V = (((2 ^ (s + 1) / D : ℕ) : ℤ) • diagGraph a) +
      shiftMatrix := hprimitive _
  have hsep := lifted_kernel_separated B (ne_of_gt hdet) hgood lam hlam
    C E D W V a hW hV hmat htpos hgap
  exact small_family_of_separated_kernel t c (lt_trans hdet hc)
    htnat htbound hsep

end Erdos1Aux
