import Submission.WalkTree
import Submission.TreeShort
import Submission.TreeAlgebra
import Submission.TreeEfficiency
import Submission.CyclicMatrix

/-! The stopped-tree construction supplies adjustable integral cyclic kernels.
This module is independent of the problem statement and its admitted theorem. -/

namespace ErdosDSS.TreeCode.Construction

open ErdosDSS ErdosDSS.TreeCode ErdosDSS.TreeCode.Tree
open scoped BigOperators

noncomputable section

theorem leaf_card (t : Tree) : Fintype.card t.Leaf = t.nodes + 1 := by
  induction t with
  | tip a => simp [Leaf, nodes]
  | fork l r hl hr =>
    simp only [Leaf, Fintype.card_sum, hl, hr, nodes]
    omega

theorem finite_index_kernel (q : ℕ) (hq : 2 ≤ q) (t : Tree)
    (hm : t.Mixed) (hn : t.isNode = true)
    (hcharge : ∀ a : t.Leaf, t.absorbed a = true →
      charge (fun i => t.path i a) = (q : ℤ) ∨
        charge (fun i => t.path i a) = -(q : ℤ)) (u : ℕ) :
    Nonempty (CyclicKernel q (t.nodes + 1)
      (Algebra.period t + u * 2 ^ (t.nodes + 1 - t.depth t.lastTime))) := by
  classical
  let m := t.nodes + 1
  let E : t.Leaf ≃ Fin m := Fintype.equivFinOfCardEq (leaf_card t)
  let M := t.adjusted u
  let G : Matrix (Fin m) (Fin m) ℤ := Matrix.reindex E E M
  let i := E t.lastTime
  let j := E t.root
  let B := Algebra.period t + u * 2 ^ (t.nodes + 1 - t.depth t.lastTime)
  have hdet : G.det = M.det := Matrix.det_reindex_self E M
  have hcof : G.adjugate i j = M.adjugate t.lastTime t.root := by
    dsimp only [G, i, j]
    rw [Matrix.adjugate_reindex]
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hB : B = G.det.natAbs := by
    rw [hdet]
    exact (Algebra.adjusted_det_natAbs t hm u).symm
  have hBpos : 0 < B := by
    rw [hB, hdet]
    exact Algebra.adjusted_det_natAbs_pos t hm u
  have hBodd : Odd B := by
    rw [hB, hdet]
    exact Algebra.adjusted_det_natAbs_odd t hm hn u
  have hcop : IsCoprime (G.adjugate i j) (B : ℤ) := by
    rw [hcof, hB, hdet]
    exact Algebra.adjusted_primitive t hm hn u
  have htern : ∀ y : Fin m → ℤ, Ternary (G.mulVec y) →
      G.mulVec y = 0 ∨ charge (G.mulVec y) = (q : ℤ) ∨
        charge (G.mulVec y) = -(q : ℤ) := by
    intro y hy
    let Y : t.Leaf → ℤ := y ∘ E
    have hv : G.mulVec y = M.mulVec Y ∘ E.symm :=
      Matrix.submatrix_mulVec_equiv M y E.symm E.symm
    have hY : Ternary (M.mulVec Y) := by
      intro a
      have hx := hy (E a)
      rw [hv] at hx
      simpa using hx
    rcases adjusted_ternary_image t hm hn q hq hcharge u Y hY with hz | hp | hminus
    · left
      rw [hv, hz]
      rfl
    · right; left
      unfold charge
      rw [hv]
      exact (E.symm.sum_comp (M.mulVec Y)).trans hp
    · right; right
      unfold charge
      rw [hv]
      exact (E.symm.sum_comp (M.mulVec Y)).trans hminus
  exact ⟨CyclicMatrix.extract G i j hq hBpos hBodd hB hcop htern⟩

theorem treeSupply : TreeSupply := by
  intro q heven hq
  obtain ⟨t, hm, hn, hcharge, hdepth, htau⟩ := Walk.exists_tree q hq heven
  refine ⟨{
    m := t.nodes + 1
    h := t.depth t.lastTime
    B := Algebra.period t
    h_le_m := (Algebra.depth_le_nodes t t.lastTime).trans (Nat.le_add_right _ _)
    height := hdepth t.lastTime (Short.mixed_lastTime_timeout t hm hn)
    data := fun u => Classical.choice (finite_index_kernel q hq t hm hn hcharge u)
    efficiency := Efficiency.period_efficiency_of_eq hm htau (Algebra.period_eq t hm)
  }⟩

end

end ErdosDSS.TreeCode.Construction
