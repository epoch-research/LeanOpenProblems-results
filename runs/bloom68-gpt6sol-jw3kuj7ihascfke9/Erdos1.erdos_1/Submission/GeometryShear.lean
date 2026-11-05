import Submission.GeometryBase

/-! Determinant and separation of rational height shears. -/

namespace Erdos1Aux

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Include the outer block's height slots in the full product-coordinate space. -/
private def heightInclusion (h : α) : Matrix (α × β) β ℚ :=
  fun ab j => if ab.1 = h then (if ab.2 = j then 1 else 0) else 0

/-- Project the full product-coordinate space to its height slots. -/
private def heightProjection (h : α) : Matrix β (α × β) ℚ :=
  fun j ab => if ab.1 = h then (if j = ab.2 then 1 else 0) else 0

private theorem heightProjection_mul_inclusion (h : α) :
    heightProjection (β := β) h * heightInclusion (β := β) h = 1 := by
  ext i j
  rw [Matrix.mul_apply, ← Finset.univ_product_univ, Finset.sum_product]
  simp [heightProjection, heightInclusion, Matrix.one_apply]

private theorem heightProjection_mulVec (h : α) (x : α × β → ℚ) (j : β) :
    (heightProjection h).mulVec x j = x (h, j) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [heightProjection]

private theorem heightInclusion_mulVec (h : α) (x : β → ℚ) (ab : α × β) :
    (heightInclusion h).mulVec x ab = if ab.1 = h then x ab.2 else 0 := by
  by_cases ha : ab.1 = h
  · simp [Matrix.mulVec, dotProduct, heightInclusion, ha]
  · simp [Matrix.mulVec, dotProduct, heightInclusion, ha]

/-- The identity off the height slots, and `D` on the height slots. -/
private def heightShear (h : α) (D : Matrix β β ℚ) :
    Matrix (α × β) (α × β) ℚ :=
  (1 : Matrix (α × β) (α × β) ℚ) +
    ((heightInclusion (β := β) h * (D - 1)) * heightProjection (β := β) h)

private theorem heightShear_mulVec (h : α) (D : Matrix β β ℚ)
    (x : α × β → ℚ) (ab : α × β) :
    (heightShear h D).mulVec x ab =
      if ab.1 = h then D.mulVec (fun j => x (h, j)) ab.2 else x ab := by
  have hproj : (heightProjection h).mulVec x = fun j => x (h, j) :=
    funext (heightProjection_mulVec h x)
  rw [heightShear, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hproj]
  simp only [Pi.add_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    heightProjection_mulVec, heightInclusion_mulVec, Pi.sub_apply]
  split_ifs with ha
  · cases ab with
    | mk a b =>
        dsimp at ha ⊢
        subst a
        ring
  · simp

private theorem heightShear_det (h : α) (D : Matrix β β ℚ) :
    (heightShear h D).det = D.det := by
  unfold heightShear
  rw [Matrix.det_one_add_mul_comm (heightInclusion h * (D - 1)) (heightProjection h)]
  rw [← Matrix.mul_assoc, heightProjection_mul_inclusion, Matrix.one_mul,
    add_comm (1 : Matrix β β ℚ), sub_add_cancel]

private theorem blockDiagonal_const_mulVec (B : Matrix α α ℚ)
    (x : α × β → ℚ) (ab : α × β) :
    (Matrix.blockDiagonal (fun _ : β => B)).mulVec x ab =
      B.mulVec (fun i => x (i, ab.2)) ab.1 := by
  rcases ab with ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product,
    Matrix.blockDiagonal_apply]
  simp

/-- A shear of `β` copies of a block matrix `B`, acting nontrivially only on
    its marked height coordinate `h`. -/
def heightShearedBlock (h : α) (B : Matrix α α ℚ) (D : Matrix β β ℚ) :
    Matrix (α × β) (α × β) ℚ :=
  Matrix.blockDiagonal (fun _ : β => B) * heightShear h D

/-- An explicit rowwise formula: the integer nonheight coordinates remain separate
    between blocks, while the rational block heights are mixed by `D`. -/
theorem heightShearedBlock_apply (h : α) (B : Matrix α α ℚ)
    (D : Matrix β β ℚ) (x : α × β → ℚ) (ab : α × β) :
    (heightShearedBlock h B D).mulVec x ab =
      B.mulVec (fun i => if i = h then 0 else x (i, ab.2)) ab.1 +
        D.mulVec (fun j => x (h, j)) ab.2 * B.col h ab.1 := by
  rw [heightShearedBlock, ← Matrix.mulVec_mulVec, blockDiagonal_const_mulVec]
  have hv : (fun i => (heightShear h D).mulVec x (i, ab.2)) =
      (fun i => if i = h then 0 else x (i, ab.2)) +
        (D.mulVec (fun j => x (h, j)) ab.2) • (Pi.single h 1 : α → ℚ) := by
    funext i
    rw [heightShear_mulVec]
    by_cases hi : i = h <;> simp [hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The determinant of a height shear: the block product times the outer height determinant. -/
theorem heightShearedBlock_det (h : α) (B : Matrix α α ℚ) (D : Matrix β β ℚ) :
    (heightShearedBlock h B D).det = B.det ^ Fintype.card β * D.det := by
  rw [heightShearedBlock, Matrix.det_mul, heightShear_det,
    Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ]


/-- A lattice basis whose marked integer input controls total height,
    with cube separation in the zero-height lattice and uniform escape. -/
structure EscapeTriple (ι : Type*) [Fintype ι] [DecidableEq ι] where
  B : Matrix ι ι ℚ
  ht : ι
  H : ℚ
  Hpos : 0 < H
  height : ∀ x : ι → ℚ, (∑ i, B.mulVec x i) = x ht
  cube : ∀ z : ι → ℤ, z ht = 0 →
    (∀ i, |B.mulVec (fun j => (z j : ℚ)) i| < 1) → z = 0
  escape : ∀ (z : ι → ℤ) (a : ℚ), z ht = 0 → H ≤ |a| →
    ¬ ∀ i, |B.mulVec (fun j => (z j : ℚ)) i + a * B.col ht i| < 1
  detpos : 0 < B.det

/-- The explicit odd-cycle escape triple. -/
def oddEscapeTriple (n : ℕ) (t : ℚ) (ht0 : 0 < t) (ht1 : t < 1) :
    EscapeTriple (Fin (2 * n + 3)) where
  B := oddBlock n t
  ht := Fin.last (2 * n + 2)
  H := (1 + t) / t
  Hpos := div_pos (by linarith) ht0
  height x := oddBlock_height n t (by linarith) x
  cube z hz hs := oddBlock_cube n t ht0 ht1 z hz hs
  escape z a hz ha := by
    intro hs
    apply oddBlock_escape n t ht0 ht1 z hz a ha
    simpa only [Matrix.mulVec_single_one] using hs
  detpos := by
    rw [oddBlock_det]
    exact div_pos (by positivity) (by linarith)

/-- Multiply every outer nonheight input coordinate by the inner escape threshold. -/
def scaledOuter (inner : EscapeTriple α) (outer : EscapeTriple β) : Matrix β β ℚ :=
  outer.B * Matrix.diagonal (fun j => if j = outer.ht then 1 else inner.H)

private theorem scaledOuter_apply (inner : EscapeTriple α) (outer : EscapeTriple β)
    (z : β → ℤ) (i : β) :
    (scaledOuter inner outer).mulVec (fun j => (z j : ℚ)) i =
      inner.H * outer.B.mulVec (fun j => ((if j = outer.ht then 0 else z j : ℤ) : ℚ)) i +
        (z outer.ht : ℚ) * outer.B.col outer.ht i := by
  have hv : (Matrix.diagonal (fun j => if j = outer.ht then (1 : ℚ) else inner.H)).mulVec
      (fun j => (z j : ℚ)) =
      inner.H • (fun j => ((if j = outer.ht then 0 else z j : ℤ) : ℚ)) +
        (z outer.ht : ℚ) • (Pi.single outer.ht 1 : β → ℚ) := by
    funext j
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = outer.ht
    · subst j
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · simp [Pi.add_apply, Pi.smul_apply, hj, smul_eq_mul]
  rw [scaledOuter, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem scaledOuter_height (inner : EscapeTriple α) (outer : EscapeTriple β)
    (x : β → ℚ) :
    (∑ i, (scaledOuter inner outer).mulVec x i) = x outer.ht := by
  rw [scaledOuter, ← Matrix.mulVec_mulVec, outer.height]
  rw [Matrix.mulVec_diagonal]
  simp

private theorem scaledOuter_column (inner : EscapeTriple α) (outer : EscapeTriple β)
    (i : β) :
    (scaledOuter inner outer).col outer.ht i = outer.B.col outer.ht i := by
  have hh := (Matrix.mulVec_single_one (scaledOuter inner outer) outer.ht)
  have hh' := (Matrix.mulVec_single_one outer.B outer.ht)
  have hv : (Matrix.diagonal (fun j => if j = outer.ht then (1 : ℚ) else inner.H)).mulVec
      (Pi.single outer.ht 1) = Pi.single outer.ht 1 := by
    funext j
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = outer.ht <;> simp [hj]
  have hc := congrFun hh i
  have hc' := congrFun hh' i
  rw [scaledOuter, ← Matrix.mulVec_mulVec, hv] at hc
  exact hc.symm.trans hc'

private theorem scaledOuter_det (inner : EscapeTriple α) (outer : EscapeTriple β) :
    (scaledOuter inner outer).det =
      outer.B.det * inner.H ^ (Fintype.card β - 1) := by
  rw [scaledOuter, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  have hmem : outer.ht ∈ (Finset.univ : Finset β) := Finset.mem_univ _
  rw [← Finset.prod_erase_mul Finset.univ
      (fun j => if j = outer.ht then (1 : ℚ) else inner.H) hmem]
  have heq : (∏ x ∈ (Finset.univ : Finset β).erase outer.ht,
      if x = outer.ht then (1 : ℚ) else inner.H) =
      ∏ _x ∈ (Finset.univ : Finset β).erase outer.ht, inner.H := by
    apply Finset.prod_congr rfl
    intro x hx
    simp [(Finset.mem_erase.mp hx).1]
  rw [heq]
  simp [Finset.card_erase_of_mem hmem]


/-- Sum of coordinates of the marked height column is exactly one. -/
private theorem EscapeTriple.weight_sum (T : EscapeTriple α) :
    (∑ i, T.B.col T.ht i) = 1 := by
  have hh := T.height (Pi.single T.ht 1)
  simpa only [Matrix.mulVec_single_one, Pi.single_eq_same] using hh

/-- The inner blocks, mixed only in their height directions by the outer block. -/
def shearedTripleMatrix (inner : EscapeTriple α) (outer : EscapeTriple β) :
    Matrix (α × β) (α × β) ℚ :=
  heightShearedBlock inner.ht inner.B (scaledOuter inner outer)

private theorem shearedTripleMatrix_height (inner : EscapeTriple α)
    (outer : EscapeTriple β) (x : α × β → ℚ) :
    (∑ ab, (shearedTripleMatrix inner outer).mulVec x ab) =
      x (inner.ht, outer.ht) := by
  change (∑ ab, (heightShearedBlock inner.ht inner.B (scaledOuter inner outer)).mulVec x ab) = _
  rw [Fintype.sum_prod_type_right]
  calc
    (∑ j : β, ∑ i : α,
        (heightShearedBlock inner.ht inner.B (scaledOuter inner outer)).mulVec x (i, j)) =
      ∑ j : β, (scaledOuter inner outer).mulVec (fun k => x (inner.ht, k)) j := by
        apply Finset.sum_congr rfl
        intro j _
        simp_rw [heightShearedBlock_apply]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, inner.height, inner.weight_sum]
        simp
    _ = x (inner.ht, outer.ht) := scaledOuter_height inner outer _

private theorem shearedTripleMatrix_column (inner : EscapeTriple α)
    (outer : EscapeTriple β) (ab : α × β) :
    (shearedTripleMatrix inner outer).col (inner.ht, outer.ht) ab =
      inner.B.col inner.ht ab.1 * outer.B.col outer.ht ab.2 := by
  let e : α × β → ℚ := Pi.single (inner.ht, outer.ht) 1
  have hnonheight (j : β) :
      (fun i => if i = inner.ht then (0 : ℚ) else e (i, j)) = 0 := by
    funext i
    by_cases hi : i = inner.ht
    · simp [hi]
    · simp [e, Pi.single_apply, hi]
  have hheight : (fun j => e (inner.ht, j)) = Pi.single outer.ht 1 := by
    funext j
    by_cases hj : j = outer.ht <;> simp [e, hj, Pi.single_apply]
  have hh := heightShearedBlock_apply inner.ht inner.B (scaledOuter inner outer) e ab
  rw [hnonheight, Matrix.mulVec_zero, Pi.zero_apply, zero_add, hheight] at hh
  rw [show e = Pi.single (inner.ht, outer.ht) 1 from rfl,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hh
  rw [scaledOuter_column] at hh
  change (heightShearedBlock inner.ht inner.B (scaledOuter inner outer)).col
    (inner.ht, outer.ht) ab = _
  rw [hh]
  ring

theorem shearedTripleMatrix_det (inner : EscapeTriple α)
    (outer : EscapeTriple β) :
    (shearedTripleMatrix inner outer).det =
      inner.B.det ^ Fintype.card β *
        (outer.B.det * inner.H ^ (Fintype.card β - 1)) := by
  rw [shearedTripleMatrix, heightShearedBlock_det, scaledOuter_det]

private def zeroInner (h : α) (z : α × β → ℤ) (j : β) : α → ℤ :=
  fun i => if i = h then 0 else z (i, j)

private def zeroOuter (h : α) (g : β) (z : α × β → ℤ) : β → ℤ :=
  fun j => if j = g then 0 else z (h, j)

private theorem shearedTripleMatrix_apply_int (inner : EscapeTriple α)
    (outer : EscapeTriple β) (z : α × β → ℤ)
    (hz : z (inner.ht, outer.ht) = 0) (ab : α × β) :
    (shearedTripleMatrix inner outer).mulVec (fun ij => (z ij : ℚ)) ab =
      inner.B.mulVec (fun i => (zeroInner inner.ht z ab.2 i : ℚ)) ab.1 +
        (inner.H * outer.B.mulVec
          (fun j => (zeroOuter inner.ht outer.ht z j : ℚ)) ab.2) *
          inner.B.col inner.ht ab.1 := by
  have hh := heightShearedBlock_apply inner.ht inner.B (scaledOuter inner outer)
    (fun ij => (z ij : ℚ)) ab
  have hv : (fun i => if i = inner.ht then (0 : ℚ) else (z (i, ab.2) : ℚ)) =
      fun i => (zeroInner inner.ht z ab.2 i : ℚ) := by
    funext i
    by_cases hi : i = inner.ht <;> simp [zeroInner, hi]
  rw [hv, scaledOuter_apply inner outer (fun j => z (inner.ht, j)) ab.2] at hh
  simpa [shearedTripleMatrix, zeroOuter, hz] using hh

/-- The zero-height part of a sheared block is cube separated, for every integer input. -/
private theorem shearedTriple_cube (inner : EscapeTriple α) (outer : EscapeTriple β)
    (z : α × β → ℤ) (hz : z (inner.ht, outer.ht) = 0)
    (hshort : ∀ ab,
      |(shearedTripleMatrix inner outer).mulVec (fun ij => (z ij : ℚ)) ab| < 1) :
    z = 0 := by
  have houter (j : β) :
      |outer.B.mulVec (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j| < 1 := by
    by_contra hj
    have hge : (1 : ℚ) ≤
        |outer.B.mulVec (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j| :=
      le_of_not_gt hj
    have hcoef : inner.H ≤
        |inner.H * outer.B.mulVec
          (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j| := by
      rw [abs_mul, abs_of_pos inner.Hpos]
      calc
        inner.H = inner.H * 1 := (mul_one _).symm
        _ ≤ inner.H * |outer.B.mulVec
            (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j| :=
          mul_le_mul_of_nonneg_left hge inner.Hpos.le
    have hblock (i : α) :
        |inner.B.mulVec (fun q => (zeroInner inner.ht z j q : ℚ)) i +
          (inner.H * outer.B.mulVec
            (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j) *
              inner.B.col inner.ht i| < 1 := by
      simpa only [shearedTripleMatrix_apply_int inner outer z hz (i, j)] using
        hshort (i, j)
    exact inner.escape (zeroInner inner.ht z j)
      (inner.H * outer.B.mulVec
        (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j)
      (by simp [zeroInner]) hcoef hblock
  have hzero : zeroOuter inner.ht outer.ht z = 0 :=
    outer.cube (zeroOuter inner.ht outer.ht z) (by simp [zeroOuter]) houter
  have hheight (j : β) : z (inner.ht, j) = 0 := by
    by_cases hj : j = outer.ht
    · simpa [hj] using hz
    · have hh := congrFun hzero j
      simpa [zeroOuter, hj] using hh
  have houtervec : (fun j => (zeroOuter inner.ht outer.ht z j : ℚ)) = 0 := by
    funext j
    rw [congrFun hzero j]
    rfl
  have hinner (j : β) : zeroInner inner.ht z j = 0 := by
    apply inner.cube (zeroInner inner.ht z j) (by simp [zeroInner])
    intro i
    have hh := hshort (i, j)
    rw [shearedTripleMatrix_apply_int inner outer z hz (i, j), houtervec,
      Matrix.mulVec_zero] at hh
    simpa only [Pi.zero_apply, mul_zero, zero_mul, add_zero] using hh
  funext ⟨i, j⟩
  by_cases hi : i = inner.ht
  · simpa [hi] using hheight j
  · have hh := congrFun (hinner j) i
    simpa [zeroInner, hi] using hh

/-- The sheared zero-height lattice has uniform escape threshold `H_inner * H_outer`. -/
private theorem shearedTriple_escape (inner : EscapeTriple α) (outer : EscapeTriple β)
    (z : α × β → ℤ) (a : ℚ)
    (hz : z (inner.ht, outer.ht) = 0)
    (ha : inner.H * outer.H ≤ |a|) :
    ¬ ∀ ab,
      |(shearedTripleMatrix inner outer).mulVec (fun ij => (z ij : ℚ)) ab +
        a * (shearedTripleMatrix inner outer).col (inner.ht, outer.ht) ab| < 1 := by
  intro hshort
  have houter (j : β) :
      |outer.B.mulVec (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j +
        (a / inner.H) * outer.B.col outer.ht j| < 1 := by
    by_contra hj
    have hge : (1 : ℚ) ≤
        |outer.B.mulVec (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j +
          (a / inner.H) * outer.B.col outer.ht j| := le_of_not_gt hj
    have hcoef : inner.H ≤
        |inner.H * outer.B.mulVec
          (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j +
            a * outer.B.col outer.ht j| := by
      have heq : inner.H *
          (outer.B.mulVec (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j +
            (a / inner.H) * outer.B.col outer.ht j) =
          inner.H * outer.B.mulVec
            (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j +
            a * outer.B.col outer.ht j := by
        field_simp [ne_of_gt inner.Hpos]
      rw [← heq, abs_mul, abs_of_pos inner.Hpos]
      calc
        inner.H = inner.H * 1 := (mul_one _).symm
        _ ≤ inner.H * |outer.B.mulVec
            (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j +
              (a / inner.H) * outer.B.col outer.ht j| :=
          mul_le_mul_of_nonneg_left hge inner.Hpos.le
    have hblock (i : α) :
        |inner.B.mulVec (fun q => (zeroInner inner.ht z j q : ℚ)) i +
          (inner.H * outer.B.mulVec
            (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j +
              a * outer.B.col outer.ht j) * inner.B.col inner.ht i| < 1 := by
      have hh := hshort (i, j)
      rw [shearedTripleMatrix_apply_int inner outer z hz (i, j),
        shearedTripleMatrix_column] at hh
      convert hh using 1 <;> ring
    exact inner.escape (zeroInner inner.ht z j)
      (inner.H * outer.B.mulVec
        (fun q => (zeroOuter inner.ht outer.ht z q : ℚ)) j +
          a * outer.B.col outer.ht j)
      (by simp [zeroInner]) hcoef hblock
  have hthreshold : outer.H ≤ |a / inner.H| := by
    rw [abs_div, abs_of_pos inner.Hpos]
    exact (le_div_iff₀ inner.Hpos).2 (by simpa [mul_comm] using ha)
  exact outer.escape (zeroOuter inner.ht outer.ht z) (a / inner.H)
    (by simp [zeroOuter]) hthreshold houter

/-- The inductive cross-block rational shear, retaining all-vector cube separation. -/
def shearEscapeTriple (inner : EscapeTriple α) (outer : EscapeTriple β) :
    EscapeTriple (α × β) where
  B := shearedTripleMatrix inner outer
  ht := (inner.ht, outer.ht)
  H := inner.H * outer.H
  Hpos := mul_pos inner.Hpos outer.Hpos
  height x := shearedTripleMatrix_height inner outer x
  cube z hz hs := shearedTriple_cube inner outer z hz hs
  escape z a hz ha := shearedTriple_escape inner outer z a hz ha
  detpos := by
    rw [shearedTripleMatrix_det]
    exact mul_pos (pow_pos inner.detpos _) (mul_pos outer.detpos (pow_pos inner.Hpos _))




end Erdos1Aux
