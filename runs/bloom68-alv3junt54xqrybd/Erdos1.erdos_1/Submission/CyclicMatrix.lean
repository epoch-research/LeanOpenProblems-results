import Submission.Kernel
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Extracting a cyclic kernel from an integral presentation

A determinant of absolute value `B` gives an index-`B` image lattice, but does
not by itself make the quotient cyclic. A single adjugate entry coprime to
`B` supplies a surjective cyclic character. Its kernel is exactly the image
lattice. A ternary restriction on that lattice then gives `CyclicKernel`.
-/

namespace ErdosDSS

open scoped BigOperators

namespace CyclicMatrix

/-- The normalized adjugate character; the coordinate `j` has weight one
when `G.adjugate i j` is coprime to `B`. -/
def character {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) :
    (Fin m → ℤ) →+ ZMod B where
  toFun e := (G.adjugate i j : ZMod B)⁻¹ * (G.adjugate.mulVec e i : ZMod B)
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mulVec_add, mul_add]

/-- The residue weight at a coordinate. -/
def weight {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (i j k : Fin m) : ZMod B :=
  (G.adjugate i j : ZMod B)⁻¹ * (G.adjugate i k : ZMod B)

@[simp]
theorem character_single {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j k : Fin m) (t : ℤ) :
    character (B := B) G i j (Pi.single k t) = weight (B := B) G i j k * (t : ZMod B) := by
  simp [character, weight, Matrix.mulVec_single, mul_assoc]

theorem weight_self {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m)
    (h : IsCoprime (G.adjugate i j) (B : ℤ)) : weight (B := B) G i j j = 1 :=
  ZMod.coe_int_inv_mul_eq_one h

/-- A nonzero determinant makes the integral matrix map injective. -/
theorem mulVecLin_injective {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (hdet : G.det ≠ 0) : Function.Injective G.mulVecLin := by
  intro x y hxy
  have h := congrArg G.adjugate.mulVec hxy
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec] at h
  ext k
  have hk := congrFun h k
  change G.det * x k = G.det * y k at hk
  exact mul_left_cancel₀ hdet hk

/-- The image lattice has index the absolute determinant. -/
theorem image_index {m : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (hdet : G.det ≠ 0) : (LinearMap.range G.mulVecLin).toAddSubgroup.index = G.det.natAbs := by
  let N := LinearMap.range G.mulVecLin
  let E := LinearEquiv.ofInjective G.mulVecLin (mulVecLin_injective G hdet)
  have h := Submodule.natAbs_det_equiv N E
  have heq : N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (E : (Fin m → ℤ) →+ N) =
      G.mulVecLin := by
    ext x k
    rfl
  rw [heq] at h
  change (LinearMap.det (Matrix.toLin' G)).natAbs = _ at h
  rw [LinearMap.det_toLin'] at h
  exact h.symm

/-- The normalized character is surjective because its `j`-th weight is one. -/
theorem character_surjective {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hB : 0 < B) (h : IsCoprime (G.adjugate i j) (B : ℤ)) :
    Function.Surjective (character (B := B) G i j) := by
  letI : NeZero B := ⟨ne_of_gt hB⟩
  intro t
  refine ⟨Pi.single j (t.val : ℤ), ?_⟩
  rw [character_single, weight_self G i j h, one_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val]

/-- The adjugate identity puts the image lattice in the character kernel. -/
theorem image_le_ker {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hB : B = G.det.natAbs) :
    (LinearMap.range G.mulVecLin).toAddSubgroup ≤ (character (B := B) G i j).ker := by
  intro e he
  obtain ⟨y, rfl⟩ := he
  change (G.adjugate i j : ZMod B)⁻¹ *
    (G.adjugate.mulVec (G.mulVecLin y) i : ZMod B) = 0
  have hd : (G.det : ZMod B) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    rw [hB, Int.natCast_dvd]
  simp [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hd]

/-- The primitive cofactor is essential: it makes the character surjective,
so its index is the same as the determinant index of the image lattice. -/
theorem ker_eq_image {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hBpos : 0 < B) (hB : B = G.det.natAbs)
    (hcop : IsCoprime (G.adjugate i j) (B : ℤ)) :
    (character (B := B) G i j).ker = (LinearMap.range G.mulVecLin).toAddSubgroup := by
  have hdet : G.det ≠ 0 := by
    intro h
    simp [h] at hB
    omega
  let L := (LinearMap.range G.mulVecLin).toAddSubgroup
  let K := (character (B := B) G i j).ker
  have hLK : L ≤ K := image_le_ker G i j hB
  have hL : L.index = B := (image_index G hdet).trans hB.symm
  have hK : K.index = B := by
    rw [AddSubgroup.index_ker,
      AddMonoidHom.range_eq_top_of_surjective _ (character_surjective G i j hBpos hcop),
      AddSubgroup.card_top, Nat.card_zmod]
  have hrel : L.relIndex K = 1 := by
    have h := AddSubgroup.relIndex_mul_index hLK
    rw [hL, hK] at h
    exact Nat.mul_right_cancel hBpos (by simpa using h)
  exact le_antisymm (AddSubgroup.relIndex_eq_one.mp hrel) hLK

/-- The character vanishes precisely on the integral image lattice. -/
theorem character_eq_zero_iff_image {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hBpos : 0 < B) (hB : B = G.det.natAbs)
    (hcop : IsCoprime (G.adjugate i j) (B : ℤ)) (e : Fin m → ℤ) :
    character (B := B) G i j e = 0 ↔ ∃ y : Fin m → ℤ, G.mulVec y = e := by
  change e ∈ (character (B := B) G i j).ker ↔ _
  rw [ker_eq_image G i j hBpos hB hcop]
  rfl

/-- The canonical natural representatives of the normalized character. -/
def residues {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) : Fin m → ℕ :=
  fun k => (weight (B := B) G i j k).val

/-- Signed sums against the natural representatives compute the character. -/
theorem cast_signedSum_residues {m B : ℕ} [NeZero B]
    (G : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m) (e : Fin m → ℤ) :
    (signedSum (residues (B := B) G i j) e : ZMod B) = character (B := B) G i j e := by
  change (signedSum (residues (B := B) G i j) e : ZMod B) =
    (G.adjugate i j : ZMod B)⁻¹ * (G.adjugate.mulVec e i : ZMod B)
  simp only [signedSum, residues, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val, Matrix.mulVec, dotProduct, weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Divisibility of the signed sum is equivalent to integral membership in
`G`'s image. This statement does not use any ternary restriction. -/
theorem dvd_signedSum_residues_iff_image {m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hBpos : 0 < B) (hB : B = G.det.natAbs)
    (hcop : IsCoprime (G.adjugate i j) (B : ℤ)) (e : Fin m → ℤ) :
    (B : ℤ) ∣ signedSum (residues (B := B) G i j) e ↔
      ∃ y : Fin m → ℤ, G.mulVec y = e := by
  letI : NeZero B := ⟨ne_of_gt hBpos⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, cast_signedSum_residues]
  exact character_eq_zero_iff_image G i j hBpos hB hcop e

private theorem ternary_single_one {m : ℕ} (k : Fin m) :
    Ternary (Pi.single k (1 : ℤ)) := by
  intro l
  by_cases h : k = l <;> simp [Pi.single_apply, h]

/-- A zero coordinate weight would put a charge-one coordinate unit in the
image lattice, contradicting the ternary restriction and `q ≥ 2`. -/
theorem weight_ne_zero {q m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hq : 2 ≤ q) (hBpos : 0 < B) (hB : B = G.det.natAbs)
    (hcop : IsCoprime (G.adjugate i j) (B : ℤ))
    (htern : ∀ y : Fin m → ℤ, Ternary (G.mulVec y) →
      G.mulVec y = 0 ∨ charge (G.mulVec y) = (q : ℤ) ∨
        charge (G.mulVec y) = -(q : ℤ)) (k : Fin m) :
    weight (B := B) G i j k ≠ 0 := by
  intro hk
  have hz : character (B := B) G i j (Pi.single k 1) = 0 := by
    simp [hk]
  obtain ⟨y, hy⟩ := (character_eq_zero_iff_image G i j hBpos hB hcop _).mp hz
  have ht : Ternary (G.mulVec y) := hy.symm ▸ ternary_single_one k
  have hq' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  rcases htern y ht with he | hc | hc
  · have h := congrFun (hy.symm.trans he) k
    simp at h
  · simp [hy, charge] at hc
    omega
  · simp [hy, charge] at hc
    omega

/-- The residues are in `[1,B-1]`; positivity is derived, not assumed. -/
theorem residues_small {q m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hq : 2 ≤ q) (hBpos : 0 < B) (hB : B = G.det.natAbs)
    (hcop : IsCoprime (G.adjugate i j) (B : ℤ))
    (htern : ∀ y : Fin m → ℤ, Ternary (G.mulVec y) →
      G.mulVec y = 0 ∨ charge (G.mulVec y) = (q : ℤ) ∨
        charge (G.mulVec y) = -(q : ℤ)) (k : Fin m) :
    0 < residues (B := B) G i j k ∧ residues (B := B) G i j k < B := by
  letI : NeZero B := ⟨ne_of_gt hBpos⟩
  refine ⟨Nat.pos_of_ne_zero ?_, ZMod.val_lt _⟩
  intro hz
  exact weight_ne_zero G i j hq hBpos hB hcop htern k
    ((ZMod.val_eq_zero _).mp hz)

/-- Extraction with a specified primitive adjugate entry. -/
def extract {q m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hq : 2 ≤ q) (hBpos : 0 < B) (hBodd : Odd B)
    (hB : B = G.det.natAbs) (hcop : IsCoprime (G.adjugate i j) (B : ℤ))
    (htern : ∀ y : Fin m → ℤ, Ternary (G.mulVec y) →
      G.mulVec y = 0 ∨ charge (G.mulVec y) = (q : ℤ) ∨
        charge (G.mulVec y) = -(q : ℤ)) : CyclicKernel q m B where
  b := residues (B := B) G i j
  q_pos := by omega
  B_pos := hBpos
  B_odd := hBodd
  small := residues_small G i j hq hBpos hB hcop htern
  kernel e he hd := by
    obtain ⟨y, hy⟩ := (dvd_signedSum_residues_iff_image G i j hBpos hB hcop e).mp hd
    have h := htern y (hy.symm ▸ he)
    simpa only [hy] using h

/-- The chosen primitive coordinate has natural representative one. -/
theorem extract_root {q m B : ℕ} (G : Matrix (Fin m) (Fin m) ℤ)
    (i j : Fin m) (hq : 2 ≤ q) (hBpos : 0 < B) (hBodd : Odd B)
    (hB : B = G.det.natAbs) (hcop : IsCoprime (G.adjugate i j) (B : ℤ))
    (htern : ∀ y : Fin m → ℤ, Ternary (G.mulVec y) →
      G.mulVec y = 0 ∨ charge (G.mulVec y) = (q : ℤ) ∨
        charge (G.mulVec y) = -(q : ℤ)) :
    (extract G i j hq hBpos hBodd hB hcop htern).b j = 1 := by
  have hs := residues_small G i j hq hBpos hB hcop htern j
  haveI : Fact (1 < B) := ⟨by omega⟩
  change (weight (B := B) G i j j).val = 1
  rw [weight_self G i j hcop, ZMod.val_one]

end CyclicMatrix

/-- The exact input interface for an integral-matrix formalizer. The
primitive adjugate entry is a separate hypothesis, not a consequence of
the determinant assumption. -/
structure IntegralPresentation (q m B : ℕ) where
  G : Matrix (Fin m) (Fin m) ℤ
  q_ge_two : 2 ≤ q
  B_pos : 0 < B
  B_odd : Odd B
  abs_det : B = G.det.natAbs
  primitive : ∃ i j : Fin m, IsCoprime (G.adjugate i j) (B : ℤ)
  ternary_image : ∀ y : Fin m → ℤ, Ternary (G.mulVec y) →
    G.mulVec y = 0 ∨ charge (G.mulVec y) = (q : ℤ) ∨
      charge (G.mulVec y) = -(q : ℤ)

/-- Choose a primitive adjugate entry and extract its cyclic kernel. -/
noncomputable def cyclicKernelOfIntegralMatrix {q m B : ℕ}
    (G : Matrix (Fin m) (Fin m) ℤ) (hq : 2 ≤ q) (hBpos : 0 < B) (hBodd : Odd B)
    (hB : B = G.det.natAbs)
    (hcop : ∃ i j : Fin m, IsCoprime (G.adjugate i j) (B : ℤ))
    (htern : ∀ y : Fin m → ℤ, Ternary (G.mulVec y) →
      G.mulVec y = 0 ∨ charge (G.mulVec y) = (q : ℤ) ∨
        charge (G.mulVec y) = -(q : ℤ)) : CyclicKernel q m B :=
  CyclicMatrix.extract G hcop.choose hcop.choose_spec.choose hq hBpos hBodd hB
    hcop.choose_spec.choose_spec htern

/-- Packaged extraction, for use by a concrete matrix construction. -/
noncomputable def IntegralPresentation.cyclicKernel {q m B : ℕ}
    (p : IntegralPresentation q m B) : CyclicKernel q m B :=
  cyclicKernelOfIntegralMatrix p.G p.q_ge_two p.B_pos p.B_odd p.abs_det
    p.primitive p.ternary_image

/-- Proposition-valued form of the generic extraction theorem. -/
theorem nonempty_cyclicKernel_of_integralMatrix {q m B : ℕ}
    (G : Matrix (Fin m) (Fin m) ℤ) (hq : 2 ≤ q) (hBpos : 0 < B) (hBodd : Odd B)
    (hB : B = G.det.natAbs)
    (hcop : ∃ i j : Fin m, IsCoprime (G.adjugate i j) (B : ℤ))
    (htern : ∀ y : Fin m → ℤ, Ternary (G.mulVec y) →
      G.mulVec y = 0 ∨ charge (G.mulVec y) = (q : ℤ) ∨
        charge (G.mulVec y) = -(q : ℤ)) : Nonempty (CyclicKernel q m B) :=
  ⟨cyclicKernelOfIntegralMatrix G hq hBpos hBodd hB hcop htern⟩

end ErdosDSS
