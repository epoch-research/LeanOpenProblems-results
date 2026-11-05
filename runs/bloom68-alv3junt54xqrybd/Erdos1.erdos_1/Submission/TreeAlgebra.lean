import Submission.TreeBasic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Int.Basic

/-! Algebra of the integral path-feedback tree construction.

The signed determinant and a primitive adjugate entry are computed on the
recursive leaf index.  Oddness follows from integral scalar recurrences,
without any mod-two matrix combinatorics.
-/

namespace ErdosDSS.TreeCode

open scoped BigOperators

namespace Algebra

open Tree

noncomputable section

private lemma path_root (t : Tree) (j : t.Leaf) : t.path t.root j = 1 := by
  cases t with
  | tip a => rfl
  | fork l r => simp [path, root]

private lemma feedback_root (t : Tree) (j : t.Leaf) : t.feedback t.root j = 0 := by
  cases t with
  | tip a => rfl
  | fork l r => simp [feedback, root]

private lemma core_root (t : Tree) (j : t.Leaf) : t.core t.root j = 1 := by
  simp [core, path_root, feedback_root]

/-- Applying sum and difference to two distinct rows multiplies the
oriented determinant by `-2`. -/
private lemma det_sum_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (a b : ι) (hab : a ≠ b) :
    let A' := A.updateRow a (A a + A b)
    (A'.updateRow b (A' a + (-2 : ℤ) • A' b)).det = -2 * A.det := by
  dsimp
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_eq_zero hab,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_add_self A hab]
  ring

private def cross (l r : Tree) : Matrix l.Leaf r.Leaf ℤ := fun i j =>
  if i = l.root then 0 else
    if l.isNode && r.isNode && decide (j = r.firstCherry)
    then l.path i l.firstAbs else 0

private def upper (l r : Tree) : Matrix (Leaf l ⊕ Leaf r) (Leaf l ⊕ Leaf r) ℤ :=
  Matrix.fromBlocks l.core (cross l r) 0 r.core

private lemma core_sum_difference (l r : Tree) :
    (fork l r).core =
      let A := upper l r
      let A' := A.updateRow (Sum.inl l.root) (A (Sum.inl l.root) + A (Sum.inr r.root))
      A'.updateRow (Sum.inr r.root)
        (A' (Sum.inl l.root) + (-2 : ℤ) • A' (Sum.inr r.root)) := by
  classical
  ext i j
  cases i with
  | inl i =>
    by_cases hi : i = l.root
    · subst i
      cases j <;> simp [upper, cross, Matrix.updateRow_apply, core,
        path, feedback, path_root, feedback_root]
    · cases j <;> simp [upper, cross, Matrix.updateRow_apply, core, path, feedback, hi]
  | inr i =>
    by_cases hi : i = r.root
    · subst i
      cases j <;> simp [upper, cross, Matrix.updateRow_apply, core,
        path, feedback, path_root, feedback_root]
    · cases j <;> simp [upper, Matrix.updateRow_apply, core, path, feedback, hi]

/-- The core has the Haar determinant, with its recursive orientation. -/
theorem core_det (t : Tree) : t.core.det = (-2 : ℤ) ^ t.nodes := by
  induction t with
  | tip a =>
    rw [Matrix.det_eq_elem_of_subsingleton _ ()]
    simp [core, path, feedback, nodes]
  | fork l r ihl ihr =>
    rw [core_sum_difference]
    rw [det_sum_difference (upper l r) (Sum.inl l.root) (Sum.inr r.root) (by simp)]
    rw [upper, Matrix.det_fromBlocks_zero₂₁, ihl, ihr, nodes]
    simp only [pow_add, pow_one]
    ring

/-- The absolute core determinant is a power of two. -/
theorem core_det_natAbs (t : Tree) : t.core.det.natAbs = 2 ^ t.nodes := by
  rw [core_det, Int.natAbs_pow]
  norm_num

private lemma firstAbs_absorbed (t : Tree) (h : t.hasAbs = true) :
    t.absorbed t.firstAbs = true := by
  induction t with
  | tip a => simpa [hasAbs, firstAbs, absorbed] using h
  | fork l r ihl ihr =>
    by_cases hl : l.hasAbs = true
    · simpa [firstAbs, hl, absorbed] using ihl hl
    · have hl' : l.hasAbs = false := by cases hla : l.hasAbs <;> simp_all
      have hr : r.hasAbs = true := by simpa [hasAbs, hl'] using h
      simpa [firstAbs, hl', absorbed] using ihr hr

private lemma mixed_has_both (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    t.hasAbs = true ∧ t.hasTime = true := by
  induction t with
  | tip a => simp [isNode] at hn
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    cases l with
    | fork ll lr =>
      obtain ⟨ha, ht⟩ := ihl hml rfl
      rw [hasAbs, hasTime, ha, ht]
      simp
    | tip a =>
      cases r with
      | fork rl rr =>
        obtain ⟨ha, ht⟩ := ihr hmr rfl
        rw [hasAbs, hasTime, ha, ht]
        simp
      | tip b =>
        have hab : a ≠ b := hch rfl rfl
        cases a <;> cases b <;> simp_all [hasAbs, hasTime]

private lemma mixed_firstCherry_timeout (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    t.absorbed t.firstCherry = false := by
  induction t with
  | tip a => simp [isNode] at hn
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    cases l with
    | fork ll lr =>
      simpa [firstCherry, isNode, absorbed] using ihl hml rfl
    | tip a =>
      cases r with
      | fork rl rr =>
        simpa [firstCherry, isNode, absorbed] using ihr hmr rfl
      | tip b =>
        have hab : a ≠ b := hch rfl rfl
        cases a <;> cases b <;> simp_all [firstCherry, isNode, hasAbs, root, absorbed]

private lemma mixed_firstAbs_absorbed (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    t.absorbed t.firstAbs = true :=
  firstAbs_absorbed t (mixed_has_both t hm hn).1

private lemma firstAbs_ne_firstCherry (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    t.firstAbs ≠ t.firstCherry := by
  intro h
  have ha := mixed_firstAbs_absorbed t hm hn
  have ht := mixed_firstCherry_timeout t hm hn
  rw [h, ht] at ha
  contradiction

private lemma feedback_absorbed (t : Tree) (hm : t.Mixed) (j : t.Leaf)
    (hj : t.absorbed j = true) (i : t.Leaf) : t.feedback i j = 0 := by
  induction t with
  | tip a => rfl
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    cases j with
    | inl j =>
      cases i with
      | inl i =>
        by_cases hi : i = l.root
        · simp [feedback, hi]
        · simp [feedback, hi, ihl hml j hj i]
      | inr i => simp [feedback]
    | inr j =>
      cases i with
      | inl i =>
        by_cases hb : (l.isNode && r.isNode) = true
        · have hrn : r.isNode = true := (Bool.and_eq_true_iff.mp hb).2
          have ht := mixed_firstCherry_timeout r hmr hrn
          have hne : j ≠ r.firstCherry := by
            intro he
            subst j
            simp [absorbed, ht] at hj
          simp [feedback, hb, hne]
        · have hb' : (l.isNode && r.isNode) = false := by
            cases h : (l.isNode && r.isNode) <;> simp_all
          simp [feedback, hb']
      | inr i =>
        by_cases hi : i = r.root
        · simp [feedback, hi]
        · simp [feedback, hi, ihr hmr j hj i]

/-- The core matrix viewed over the rationals. -/
def qcore (t : Tree) : Matrix t.Leaf t.Leaf ℚ := t.core.map (fun a => (a : ℚ))

private lemma qcore_absorbed (t : Tree) (hm : t.Mixed) (j : t.Leaf)
    (hj : t.absorbed j = true) (i : t.Leaf) :
    qcore t i j = (t.path i j : ℚ) := by
  simp [qcore, core, feedback_absorbed t hm j hj i]

private lemma qcore_root_mulVec (t : Tree) (v : t.Leaf → ℚ) :
    ((qcore t).mulVec v) t.root = ∑ j, v j := by
  simp [qcore, Matrix.mulVec, dotProduct, core_root]

private lemma qcore_query (l r : Tree) (v : (fork l r).Leaf → ℚ) :
    ((qcore (fork l r)).mulVec v) (Sum.inr r.root) =
      (∑ j, v (Sum.inl j)) - ∑ j, v (Sum.inr j) := by
  simp [qcore, core, Matrix.mulVec, dotProduct, Leaf, Fintype.sum_sum_type,
    path, feedback, Finset.sum_neg_distrib, sub_eq_add_neg]

private lemma qcore_right (l r : Tree) (v : (fork l r).Leaf → ℚ)
    (i : r.Leaf) (hi : i ≠ r.root) :
    ((qcore (fork l r)).mulVec v) (Sum.inr i) =
      ((qcore r).mulVec (fun j => v (Sum.inr j))) i := by
  simp [qcore, core, Matrix.mulVec, dotProduct, Leaf, Fintype.sum_sum_type,
    path, feedback, hi]

private lemma qcore_left (l r : Tree) (v : (fork l r).Leaf → ℚ)
    (i : l.Leaf) (hi : i ≠ l.root) :
    ((qcore (fork l r)).mulVec v) (Sum.inl i) =
      ((qcore l).mulVec (fun j => v (Sum.inl j))) i +
        (l.path i l.firstAbs : ℚ) *
          (if l.isNode && r.isNode then v (Sum.inr r.firstCherry) else 0) := by
  classical
  simp only [qcore, Matrix.mulVec, dotProduct, Leaf, Fintype.sum_sum_type,
    Matrix.map_apply, core, Matrix.add_apply, path, feedback, if_neg hi,
    Int.cast_add, Int.cast_zero, zero_add]
  by_cases hb : (l.isNode && r.isNode) = true
  · simp [hb, Finset.sum_ite_eq', mul_comm]
  · have hb' : (l.isNode && r.isNode) = false := by
      cases h : (l.isNode && r.isNode) <;> simp_all
    simp [hb']

private def branchMass (l r : Tree) : ℚ :=
  if l.isNode && r.isNode then r.z / 2 else 0

/-- A recursively specified solution of the core root equation.  Absorbing
coordinates may be negative; no row-norm estimate is used. -/
def rootSolution : (t : Tree) → t.Leaf → ℚ
  | tip _, _ => 1
  | fork l r, Sum.inl i =>
      (1 / 2 + branchMass l r) * rootSolution l i -
        branchMass l r * (Pi.single l.firstAbs (1 : ℚ) : l.Leaf → ℚ) i
  | fork _ r, Sum.inr j => (1 / 2) * rootSolution r j

/-- The rational root solution has total mass one. -/
theorem rootSolution_sum (t : Tree) : ∑ j, rootSolution t j = 1 := by
  induction t with
  | tip a => simp [Leaf, rootSolution]
  | fork l r ihl ihr =>
    simp only [Leaf, Fintype.sum_sum_type, rootSolution, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
    simp [Pi.single_apply, ihl, ihr]
    ring

private lemma rootSolution_sum_left (l r : Tree) :
    (∑ j, rootSolution (fork l r) (Sum.inl j)) = 1 / 2 := by
  simp only [rootSolution, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Pi.single_apply, rootSolution_sum]

private lemma rootSolution_sum_right (l r : Tree) :
    (∑ j, rootSolution (fork l r) (Sum.inr j)) = 1 / 2 := by
  simp [rootSolution, ← Finset.mul_sum, rootSolution_sum]

/-- On a mixed query tree the first-cherry coordinate is the scalar `z`. -/
theorem rootSolution_firstCherry (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    rootSolution t t.firstCherry = t.z := by
  induction t with
  | tip a => simp [isNode] at hn
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    by_cases hl : l.isNode = true
    · have hne := firstAbs_ne_firstCherry l hml hl
      simp only [firstCherry, hl, if_true, rootSolution,
        Pi.single_eq_of_ne' hne, mul_zero, sub_zero, ihl hml hl]
      rw [z]
      cases hr : r.isNode <;> simp [branchMass, hl, hr] <;> ring
    · have hl' : l.isNode = false := by cases h : l.isNode <;> simp_all
      by_cases hr : r.isNode = true
      · simp [firstCherry, hl', hr, rootSolution, ihr hmr hr, z]
        ring
      · have hr' : r.isNode = false := by cases h : r.isNode <;> simp_all
        cases l with
        | fork ll lr => simp [isNode] at hl'
        | tip a =>
          cases r with
          | fork rl rr => simp [isNode] at hr'
          | tip b =>
            cases a <;> cases b <;>
              simp [rootSolution, firstCherry, isNode, branchMass, z, hasAbs, root]

private lemma rootSolution_left_eq (l r : Tree) :
    (fun j => rootSolution (fork l r) (Sum.inl j)) =
      (1 / 2 + branchMass l r) • rootSolution l -
        branchMass l r • (Pi.single l.firstAbs 1 : l.Leaf → ℚ) := rfl

private lemma rootSolution_right_eq (l r : Tree) :
    (fun j => rootSolution (fork l r) (Sum.inr j)) = (1 / 2 : ℚ) • rootSolution r := rfl

/-- The recursive vector solves the rational core root equation. -/
theorem rootSolution_core (t : Tree) (hm : t.Mixed) :
    (qcore t).mulVec (rootSolution t) = Pi.single t.root 1 := by
  induction t with
  | tip a =>
    ext i
    cases i
    simp [qcore, core, path, feedback, rootSolution, Leaf, Matrix.mulVec, dotProduct, root]
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    ext i
    cases i with
    | inl i =>
      by_cases hi : i = l.root
      · subst i
        change ((qcore (fork l r)).mulVec (rootSolution (fork l r))) (fork l r).root = _
        rw [qcore_root_mulVec, rootSolution_sum]
        simp [root]
      · rw [qcore_left l r _ i hi, rootSolution_left_eq, Matrix.mulVec_sub,
          Matrix.mulVec_smul, Matrix.mulVec_smul, ihl hml]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one,
          Matrix.col_apply, Pi.single_eq_of_ne hi, mul_zero, zero_sub]
        have hni : (Sum.inl i : (fork l r).Leaf) ≠ (fork l r).root := by
          intro he
          exact hi (Sum.inl.inj he)
        rw [Pi.single_eq_of_ne hni]
        by_cases hb : (l.isNode && r.isNode) = true
        · obtain ⟨hln, hrn⟩ := Bool.and_eq_true_iff.mp hb
          rw [qcore_absorbed l hml l.firstAbs (mixed_firstAbs_absorbed l hml hln)]
          simp [rootSolution, rootSolution_firstCherry r hmr hrn, branchMass, hb]
          ring
        · have hb' : (l.isNode && r.isNode) = false := by
            cases h : (l.isNode && r.isNode) <;> simp_all
          simp [branchMass, hb']
    | inr i =>
      by_cases hi : i = r.root
      · subst i
        rw [qcore_query, rootSolution_sum_left, rootSolution_sum_right]
        simp [root]
      · rw [qcore_right l r _ i hi, rootSolution_right_eq, Matrix.mulVec_smul, ihr hmr]
        simp [root, hi]

/-- Every leaf depth is at most the number of query vertices. -/
theorem depth_le_nodes (t : Tree) (j : t.Leaf) : t.depth j ≤ t.nodes := by
  induction t with
  | tip a => simp [depth, nodes]
  | fork l r ihl ihr =>
    cases j with
    | inl j =>
      have h := ihl j
      simp only [depth, nodes]
      omega
    | inr j =>
      have h := ihr j
      simp only [depth, nodes]
      omega

/-- The rightmost timeout has its unmodified fair mass, since no suffix
feedback enters a later timeout. -/
theorem rootSolution_lastTime (t : Tree) (hm : t.Mixed) :
    rootSolution t t.lastTime = 1 / (2 : ℚ) ^ (t.depth t.lastTime) := by
  induction t with
  | tip a => simp [rootSolution, depth]
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    by_cases hr : r.hasTime = true
    · simp only [lastTime, hr, if_true, rootSolution, depth, ihr hmr,
        pow_succ]
      ring
    · have hr' : r.hasTime = false := by cases h : r.hasTime <;> simp_all
      have hrn : r.isNode = false := by
        cases h : r.isNode with
        | false => rfl
        | true =>
          have ht := (mixed_has_both r hmr h).2
          rw [hr'] at ht
          contradiction
      simp only [lastTime, hr', Bool.false_eq_true, if_false, rootSolution, depth,
        branchMass, hrn, Bool.and_false, if_false, add_zero, zero_mul, sub_zero,
        ihl hml, pow_succ]
      ring

/-- Total rational mass on timeout leaves. -/
def timeoutSum (t : Tree) (v : t.Leaf → ℚ) : ℚ :=
  ∑ j, if t.absorbed j then 0 else v j

private lemma timeoutSum_sub (t : Tree) (v w : t.Leaf → ℚ) :
    timeoutSum t (v - w) = timeoutSum t v - timeoutSum t w := by
  unfold timeoutSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases t.absorbed j <;> simp

private lemma timeoutSum_smul (t : Tree) (c : ℚ) (v : t.Leaf → ℚ) :
    timeoutSum t (c • v) = c * timeoutSum t v := by
  unfold timeoutSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases t.absorbed j <;> simp

private lemma timeoutSum_single (t : Tree) (a : t.Leaf) (c : ℚ) :
    timeoutSum t (Pi.single a c) = if t.absorbed a then 0 else c := by
  classical
  unfold timeoutSum
  rw [Finset.sum_eq_single a]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private lemma timeoutSum_fork (l r : Tree) (v : (fork l r).Leaf → ℚ) :
    timeoutSum (fork l r) v =
      timeoutSum l (fun j => v (Sum.inl j)) + timeoutSum r (fun j => v (Sum.inr j)) := by
  simp [timeoutSum, Leaf, Fintype.sum_sum_type, absorbed]

/-- The scalar `f` is exactly the root solution's timeout mass. -/
theorem rootSolution_timeoutSum (t : Tree) (hm : t.Mixed) :
    timeoutSum t (rootSolution t) = t.f := by
  induction t with
  | tip a => cases a <;> simp [timeoutSum, Leaf, absorbed, rootSolution, f]
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    rw [timeoutSum_fork, rootSolution_left_eq, rootSolution_right_eq,
      timeoutSum_sub, timeoutSum_smul, timeoutSum_smul, timeoutSum_smul,
      timeoutSum_single, ihl hml, ihr hmr, f]
    by_cases hb : (l.isNode && r.isNode) = true
    · have hln := (Bool.and_eq_true_iff.mp hb).1
      have ha := mixed_firstAbs_absorbed l hml hln
      simp [branchMass, hb, ha]
      ring
    · have hb' : (l.isNode && r.isNode) = false := by
        cases h : (l.isNode && r.isNode) <;> simp_all
      simp [branchMass, hb']
      ring

private lemma adjugate_updateRow {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) (r : ι) (v : ι → R) (j : ι) :
    (A.updateRow r v).adjugate j r = A.adjugate j r := by
  rw [Matrix.adjugate_apply, Matrix.updateRow_idem, ← Matrix.adjugate_apply]

private lemma adjugate_col_of_solution {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) (p : ι → R) (r : ι)
    (hp : A.mulVec p = Pi.single r 1) (j : ι) :
    A.adjugate j r = A.det * p j := by
  have h := congrArg A.adjugate.mulVec hp
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_single_one] at h
  exact (congrFun h j).symm

private lemma det_root_update {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : Matrix ι ι R) (p : ι → R) (r : ι)
    (hp : A.mulVec p = Pi.single r 1) (v : ι → R) :
    (A.updateRow r (A r + v)).det = A.det * (1 + ∑ j, v j * p j) := by
  have hsum : ∑ j, A r j * p j = 1 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hp r
  rw [Matrix.det_eq_sum_mul_adjugate_row _ r]
  simp only [Matrix.updateRow_self, Pi.add_apply, adjugate_updateRow,
    adjugate_col_of_solution A p r hp]
  calc
    (∑ j, (A r j + v j) * (A.det * p j)) =
        A.det * ∑ j, (A r j + v j) * p j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = A.det * (1 + ∑ j, v j * p j) := by
      rw [show (∑ j, (A r j + v j) * p j) =
        (∑ j, A r j * p j) + ∑ j, v j * p j by
          simp only [add_mul, Finset.sum_add_distrib], hsum]

private def rootUpdate (t : Tree) (u : ℕ) : t.Leaf → ℚ := fun j =>
  (if t.absorbed j then 0 else 1) + (if j = t.lastTime then 2 * (u : ℚ) else 0)

private def qadjusted (t : Tree) (u : ℕ) : Matrix t.Leaf t.Leaf ℚ :=
  (t.adjusted u).map (fun a => (a : ℚ))

private lemma qadjusted_eq_updateRow (t : Tree) (u : ℕ) :
    qadjusted t u = (qcore t).updateRow t.root ((qcore t) t.root + rootUpdate t u) := by
  classical
  ext i j
  by_cases hi : i = t.root
  · simp [qadjusted, qcore, rootUpdate, adjusted, Matrix.updateRow_apply, hi]
  · simp [qadjusted, qcore, adjusted, Matrix.updateRow_apply, hi]

private lemma qcore_det (t : Tree) : (qcore t).det = (-2 : ℚ) ^ t.nodes := by
  rw [qcore, ← Int.cast_det, core_det]
  norm_cast

private lemma rootUpdate_dot (t : Tree) (hm : t.Mixed) (u : ℕ) :
    (∑ j, rootUpdate t u j * rootSolution t j) =
      t.f + 2 * (u : ℚ) * rootSolution t t.lastTime := by
  classical
  simp only [rootUpdate, add_mul, ite_mul, zero_mul, one_mul, Finset.sum_add_distrib]
  rw [show (∑ j, if t.absorbed j then 0 else rootSolution t j) = t.f from
    rootSolution_timeoutSum t hm]
  simp

/-- Oriented rational determinant formula for every nonnegative root
adjustment. -/
theorem adjusted_det_rat (t : Tree) (hm : t.Mixed) (u : ℕ) :
    ((t.adjusted u).det : ℚ) = (-2 : ℚ) ^ t.nodes *
      (1 + t.f + 2 * (u : ℚ) / (2 : ℚ) ^ (t.depth t.lastTime)) := by
  rw [Int.cast_det]
  change (qadjusted t u).det = _
  rw [qadjusted_eq_updateRow, det_root_update _ _ _ (rootSolution_core t hm),
    qcore_det, rootUpdate_dot t hm u, rootSolution_lastTime t hm]
  ring

/-- The entire root column of the adjugate is unchanged by root-row
updates and is the oriented core determinant times the root solution. -/
theorem adjusted_adjugate_root_rat (t : Tree) (hm : t.Mixed) (u : ℕ) (j : t.Leaf) :
    ((t.adjusted u).adjugate j t.root : ℚ) =
      (-2 : ℚ) ^ t.nodes * rootSolution t j := by
  have hmap := (Int.castRingHom ℚ).map_adjugate (t.adjusted u)
  have h := congrFun (congrFun hmap j) t.root
  change ((t.adjusted u).adjugate j t.root : ℚ) = (qadjusted t u).adjugate j t.root at h
  rw [h, qadjusted_eq_updateRow, adjugate_updateRow,
    adjugate_col_of_solution _ _ _ (rootSolution_core t hm), qcore_det]

/-- The last-timeout/root cofactor, before taking absolute values. -/
theorem adjusted_lastTime_adjugate_rat (t : Tree) (hm : t.Mixed) (u : ℕ) :
    ((t.adjusted u).adjugate t.lastTime t.root : ℚ) =
      (-2 : ℚ) ^ t.nodes / (2 : ℚ) ^ (t.depth t.lastTime) := by
  rw [adjusted_adjugate_root_rat t hm u, rootSolution_lastTime t hm]
  ring

/-- Integral numerator of the transformed first-cherry mass. -/
def scaledZ : Tree → ℕ
  | tip _ => 0
  | fork l r =>
      if l.isNode then scaledZ l * (2 ^ r.nodes + if r.isNode then scaledZ r else 0)
      else if r.isNode then 2 ^ l.nodes * scaledZ r
      else 2 ^ l.nodes * 2 ^ r.nodes

/-- Integral numerator of the transformed timeout mass. -/
def scaledF : Tree → ℕ
  | tip a => if a then 0 else 1
  | fork l r => 2 ^ r.nodes * scaledF l + 2 ^ l.nodes * scaledF r +
      if l.isNode && r.isNode then scaledZ r * scaledF l else 0

private lemma pow_nodes_fork (l r : Tree) :
    (2 : ℚ) ^ (fork l r).nodes = 2 * (2 : ℚ) ^ l.nodes * (2 : ℚ) ^ r.nodes := by
  simp only [nodes, pow_add, pow_one]

/-- The recursive numerator is exactly `2^nodes * z`. -/
theorem scaledZ_eq (t : Tree) : (scaledZ t : ℚ) = (2 : ℚ) ^ t.nodes * t.z := by
  induction t with
  | tip a => simp [scaledZ, nodes, z]
  | fork l r ihl ihr =>
    cases hl : l.isNode <;> cases hr : r.isNode <;>
      simp [scaledZ, z, hl, hr, ihl, ihr, pow_nodes_fork] <;> ring

/-- The recursive numerator is exactly `2^nodes * f`. -/
theorem scaledF_eq (t : Tree) : (scaledF t : ℚ) = (2 : ℚ) ^ t.nodes * t.f := by
  induction t with
  | tip a => cases a <;> simp [scaledF, nodes, f]
  | fork l r ihl ihr =>
    cases hl : l.isNode <;> cases hr : r.isNode <;>
      simp [scaledF, f, hl, hr, ihl, ihr, scaledZ_eq, pow_nodes_fork] <;> ring

private lemma nodes_pos (t : Tree) (hn : t.isNode = true) : 0 < t.nodes := by
  cases t with
  | tip a => simp [isNode] at hn
  | fork l r => simp [nodes]

private lemma denom_even (t : Tree) (hn : t.isNode = true) : Even (2 ^ t.nodes) :=
  even_two.pow_of_ne_zero (ne_of_gt (nodes_pos t hn))

/-- Both transformed numerators are odd on mixed query trees.  This is a
scalar induction and does not assert anything about matrix norms. -/
theorem scaled_odd (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    Odd (scaledF t) ∧ Odd (scaledZ t) := by
  induction t with
  | tip a => simp [isNode] at hn
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    cases l with
    | tip a =>
      cases r with
      | tip b =>
        have hab : a ≠ b := hch rfl rfl
        cases a <;> cases b <;> simp_all [scaledF, scaledZ, nodes, isNode]
      | fork rl rr =>
        obtain ⟨hf, hz⟩ := ihr hmr rfl
        have he := denom_even (fork rl rr) rfl
        constructor
        · change Odd (2 ^ (fork rl rr).nodes * (if a then 0 else 1) +
            1 * scaledF (fork rl rr) + 0)
          simpa using (he.mul_right (if a then 0 else 1)).add_odd hf
        · change Odd (1 * scaledZ (fork rl rr))
          simpa using hz
    | fork ll lr =>
      obtain ⟨hfl, hzl⟩ := ihl hml rfl
      have hel := denom_even (fork ll lr) rfl
      cases r with
      | tip b =>
        constructor
        · change Odd (1 * scaledF (fork ll lr) +
            2 ^ (fork ll lr).nodes * (if b then 0 else 1) + 0)
          simpa using hfl.add_even (hel.mul_right (if b then 0 else 1))
        · change Odd (scaledZ (fork ll lr) * (1 + 0))
          simpa using hzl
      | fork rl rr =>
        obtain ⟨hfr, hzr⟩ := ihr hmr rfl
        have her := denom_even (fork rl rr) rfl
        constructor
        · change Odd (2 ^ (fork rl rr).nodes * scaledF (fork ll lr) +
            2 ^ (fork ll lr).nodes * scaledF (fork rl rr) +
            scaledZ (fork rl rr) * scaledF (fork ll lr))
          exact ((her.mul_right _).add (hel.mul_right _)).add_odd (hzr.mul hfl)
        · change Odd (scaledZ (fork ll lr) *
            (2 ^ (fork rl rr).nodes + scaledZ (fork rl rr)))
          exact hzl.mul (her.add_odd hzr)

private lemma two_pow_div (n h : ℕ) (hh : h ≤ n) :
    (2 : ℚ) ^ n / (2 : ℚ) ^ h = (2 : ℚ) ^ (n - h) := by
  rw [pow_sub₀ (2 : ℚ) (by norm_num) hh, div_eq_mul_inv]

private lemma two_pow_adjustment (n h u : ℕ) (hh : h ≤ n) :
    (2 : ℚ) ^ n * (2 * (u : ℚ) / (2 : ℚ) ^ h) =
      (u : ℚ) * (2 : ℚ) ^ (n + 1 - h) := by
  rw [show n + 1 - h = n - h + 1 by omega, pow_succ]
  calc
    (2 : ℚ) ^ n * (2 * (u : ℚ) / (2 : ℚ) ^ h) =
        2 * (u : ℚ) * ((2 : ℚ) ^ n / (2 : ℚ) ^ h) := by ring
    _ = (u : ℚ) * ((2 : ℚ) ^ (n - h) * 2) := by rw [two_pow_div n h hh]; ring

/-- Exact signed integral cofactor.  Its orientation agrees with the core
determinant and it does not depend on the adjustment. -/
theorem adjusted_lastTime_adjugate (t : Tree) (hm : t.Mixed) (u : ℕ) :
    (t.adjusted u).adjugate t.lastTime t.root =
      (-1 : ℤ) ^ t.nodes * 2 ^ (t.nodes - t.depth t.lastTime) := by
  have h := adjusted_lastTime_adjugate_rat t hm u
  rw [neg_pow, mul_div_assoc,
    two_pow_div t.nodes (t.depth t.lastTime) (depth_le_nodes t t.lastTime)] at h
  exact_mod_cast h

/-- The primitive cofactor's absolute value is `2^(m-1-h)`, where
`m = nodes+1` and `h` is the last-timeout depth. -/
theorem adjusted_lastTime_adjugate_natAbs (t : Tree) (hm : t.Mixed) (u : ℕ) :
    ((t.adjusted u).adjugate t.lastTime t.root).natAbs =
      2 ^ (t.nodes - t.depth t.lastTime) := by
  rw [adjusted_lastTime_adjugate t hm u, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
  norm_num

/-- Exact oriented integral determinant, using only natural scalar
numerators and a power-of-two adjustment step. -/
theorem adjusted_det (t : Tree) (hm : t.Mixed) (u : ℕ) :
    (t.adjusted u).det = (-1 : ℤ) ^ t.nodes *
      ((2 ^ t.nodes + scaledF t + u * 2 ^ (t.nodes + 1 - t.depth t.lastTime) : ℕ) : ℤ) := by
  have hs : ((2 ^ t.nodes + scaledF t +
        u * 2 ^ (t.nodes + 1 - t.depth t.lastTime) : ℕ) : ℚ) =
      (2 : ℚ) ^ t.nodes *
        (1 + t.f + 2 * (u : ℚ) / (2 : ℚ) ^ (t.depth t.lastTime)) := by
    push_cast
    rw [scaledF_eq]
    rw [← two_pow_adjustment t.nodes (t.depth t.lastTime) u (depth_le_nodes t t.lastTime)]
    ring
  have h : ((t.adjusted u).det : ℚ) = (-1 : ℚ) ^ t.nodes *
      ((2 ^ t.nodes + scaledF t + u * 2 ^ (t.nodes + 1 - t.depth t.lastTime) : ℕ) : ℚ) := by
    rw [adjusted_det_rat t hm u, neg_pow, hs]
    ring
  exact_mod_cast h

private lemma adjusted_det_natAbs_numerator (t : Tree) (hm : t.Mixed) (u : ℕ) :
    (t.adjusted u).det.natAbs =
      2 ^ t.nodes + scaledF t + u * 2 ^ (t.nodes + 1 - t.depth t.lastTime) := by
  rw [adjusted_det t hm u, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  norm_num

/-- The unadjusted cyclic period, defined as an actual determinant. -/
def period (t : Tree) : ℕ := (t.adjusted 0).det.natAbs

/-- The period is the power-of-two core denominator plus the integral
transformed timeout numerator. -/
theorem period_eq_numerator (t : Tree) (hm : t.Mixed) :
    period t = 2 ^ t.nodes + scaledF t := by
  simp [period, adjusted_det_natAbs_numerator t hm 0]

/-- The exact determinant progression has step `2^(m-h)`. -/
theorem adjusted_det_natAbs (t : Tree) (hm : t.Mixed) (u : ℕ) :
    (t.adjusted u).det.natAbs = period t + u * 2 ^ (t.nodes + 1 - t.depth t.lastTime) := by
  rw [adjusted_det_natAbs_numerator t hm u, period_eq_numerator t hm]

/-- The period is positive, with no query-tree restriction needed. -/
theorem period_pos (t : Tree) (hm : t.Mixed) : 0 < period t := by
  rw [period_eq_numerator t hm]
  exact lt_of_lt_of_le (Nat.pow_pos (by omega)) (Nat.le_add_right _ _)

/-- On a mixed query tree the determinant period is odd. -/
theorem period_odd (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) : Odd (period t) := by
  rw [period_eq_numerator t hm]
  exact (denom_even t hn).add_odd (scaled_odd t hm hn).1

/-- Every adjusted determinant still has positive absolute value. -/
theorem adjusted_det_natAbs_pos (t : Tree) (hm : t.Mixed) (u : ℕ) :
    0 < (t.adjusted u).det.natAbs := by
  rw [adjusted_det_natAbs t hm u]
  exact lt_of_lt_of_le (period_pos t hm) (Nat.le_add_right _ _)

/-- Every adjustment preserves oddness, since its step is even. -/
theorem adjusted_det_natAbs_odd (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) (u : ℕ) :
    Odd (t.adjusted u).det.natAbs := by
  rw [adjusted_det_natAbs t hm u]
  have hk : t.nodes + 1 - t.depth t.lastTime ≠ 0 := by
    have hh := depth_le_nodes t t.lastTime
    omega
  exact (period_odd t hm hn).add_even ((even_two.pow_of_ne_zero hk).mul_left u)

/-- The period formula identifying the determinant with the scalar `f`. -/
theorem period_eq (t : Tree) (hm : t.Mixed) :
    (period t : ℚ) = (2 : ℚ) ^ t.nodes * (1 + t.f) := by
  rw [period_eq_numerator t hm]
  push_cast
  rw [scaledF_eq]
  ring

/-- Normalized period formula, with `m = nodes+1`. -/
theorem period_normalized (t : Tree) (hm : t.Mixed) :
    (period t : ℚ) / (2 : ℚ) ^ (t.nodes + 1) = (1 + t.f) / 2 := by
  rw [period_eq t hm, pow_succ]
  field_simp

/-- Any scalar upper bound on `f` gives the corresponding determinant
bound, without substituting an image count for a period. -/
theorem period_bound_of_f (t : Tree) (hm : t.Mixed) {c : ℚ} (hf : t.f ≤ c) :
    (period t : ℚ) ≤ (2 : ℚ) ^ t.nodes * (1 + c) := by
  rw [period_eq t hm]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Equivalent bound using the full number of leaves `m = nodes+1`. -/
theorem period_bound (t : Tree) (hm : t.Mixed) {c : ℚ} (hf : t.f ≤ c) :
    (period t : ℚ) ≤ ((1 + c) / 2) * (2 : ℚ) ^ (t.nodes + 1) := by
  have h := period_bound_of_f t hm hf
  rw [pow_succ]
  convert h using 1
  ring

/-- The primitive cofactor is coprime to every odd adjusted period. -/
theorem adjusted_lastTime_coprime (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) (u : ℕ) :
    Nat.Coprime ((t.adjusted u).adjugate t.lastTime t.root).natAbs
      (t.adjusted u).det.natAbs := by
  rw [adjusted_lastTime_adjugate_natAbs t hm u]
  exact Nat.Coprime.pow_left _ (adjusted_det_natAbs_odd t hm hn u).coprime_two_left

/-- Integral coprimality in the exact form required by cyclic matrix
extraction. -/
theorem adjusted_primitive (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) (u : ℕ) :
    IsCoprime ((t.adjusted u).adjugate t.lastTime t.root)
      ((t.adjusted u).det.natAbs : ℤ) := by
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
  exact adjusted_lastTime_coprime t hm hn u

/-- The normalized adjustment cost is exactly `u / 2^h`. -/
theorem adjusted_period_normalized (t : Tree) (hm : t.Mixed) (u : ℕ) :
    ((t.adjusted u).det.natAbs : ℚ) / (2 : ℚ) ^ (t.nodes + 1) =
      (1 + t.f) / 2 + (u : ℚ) / (2 : ℚ) ^ (t.depth t.lastTime) := by
  rw [adjusted_det_natAbs t hm u]
  push_cast
  rw [add_div, period_normalized t hm]
  congr 1
  have hh : t.depth t.lastTime ≤ t.nodes + 1 :=
    (depth_le_nodes t t.lastTime).trans (Nat.le_add_right _ _)
  have hp : (2 : ℚ) ^ (t.nodes + 1 - t.depth t.lastTime) *
      (2 : ℚ) ^ (t.depth t.lastTime) = (2 : ℚ) ^ (t.nodes + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hh]
  rw [← hp]
  field_simp

/-- Scalar mass and normalized adjustment bounds directly bound the actual
adjusted determinant period. -/
theorem adjusted_period_bound (t : Tree) (hm : t.Mixed) (u : ℕ) {c ε : ℚ}
    (hf : t.f ≤ c) (hu : (u : ℚ) / (2 : ℚ) ^ (t.depth t.lastTime) ≤ ε) :
    ((t.adjusted u).det.natAbs : ℚ) ≤
      ((1 + c) / 2 + ε) * (2 : ℚ) ^ (t.nodes + 1) := by
  have h := adjusted_period_normalized t hm u
  have heq := (div_eq_iff (show (2 : ℚ) ^ (t.nodes + 1) ≠ 0 by positivity)).mp h
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hf' : (1 + t.f) / 2 ≤ (1 + c) / 2 := by linarith
  exact add_le_add hf' hu

/-- A timeout-mass bound of `5/12` gives the unadjusted `17/24`
efficiency bound in natural-number arithmetic. -/
theorem period_efficiency (t : Tree) (hm : t.Mixed) (hf : t.f ≤ (5 / 12 : ℚ)) :
    24 * period t ≤ 17 * 2 ^ (t.nodes + 1) := by
  have hb := period_bound t hm hf
  have hc : (24 : ℚ) * (period t : ℚ) ≤ 17 * (2 : ℚ) ^ (t.nodes + 1) := by
    linarith
  exact_mod_cast hc

/-- The standard `1/48` adjustment budget gives the required `35/48`
efficiency bound for the genuine adjusted determinant period. -/
theorem adjusted_period_efficiency (t : Tree) (hm : t.Mixed) (u : ℕ)
    (hf : t.f ≤ (5 / 12 : ℚ))
    (hu : (u : ℚ) / (2 : ℚ) ^ (t.depth t.lastTime) ≤ (1 / 48 : ℚ)) :
    48 * (t.adjusted u).det.natAbs ≤ 35 * 2 ^ (t.nodes + 1) := by
  have hb := adjusted_period_bound t hm u hf hu
  have hc : (48 : ℚ) * ((t.adjusted u).det.natAbs : ℚ) ≤
      35 * (2 : ℚ) ^ (t.nodes + 1) := by linarith
  exact_mod_cast hc

/-- The full algebra certificate in the notation `m`, `h`, and `B` used by
the finite-index transport. -/
theorem matrix_data (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    let m := t.nodes + 1
    let h := t.depth t.lastTime
    let B := (t.adjusted 0).det.natAbs
    0 < B ∧ Odd B ∧ (B : ℚ) = (2 : ℚ) ^ (m - 1) * (1 + t.f) ∧
      ∀ u : ℕ, (t.adjusted u).det.natAbs = B + u * 2 ^ (m - h) ∧
        Odd (t.adjusted u).det.natAbs ∧
        ((t.adjusted u).adjugate t.lastTime t.root).natAbs = 2 ^ (m - 1 - h) ∧
        IsCoprime ((t.adjusted u).adjugate t.lastTime t.root)
          ((t.adjusted u).det.natAbs : ℤ) := by
  dsimp only
  refine ⟨period_pos t hm, period_odd t hm hn, ?_, ?_⟩
  · simpa [period] using period_eq t hm
  · intro u
    refine ⟨adjusted_det_natAbs t hm u, adjusted_det_natAbs_odd t hm hn u, ?_,
      adjusted_primitive t hm hn u⟩
    simpa using adjusted_lastTime_adjugate_natAbs t hm u

end

end Algebra

end ErdosDSS.TreeCode
