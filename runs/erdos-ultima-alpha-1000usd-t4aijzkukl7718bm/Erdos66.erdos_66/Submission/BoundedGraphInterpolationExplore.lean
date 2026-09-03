import Submission.EvenPolynomialGraphExplore

/-! Finite interpolation with an explicit sum-fiber budget. The extra
positive even-degree term prevents cancellation of the leading sum term. -/
namespace Erdos66BoundedGraphInterpolation
open Polynomial Erdos66TranslatedGraphPartition Erdos66EvenPolynomialGraph
open scoped Classical
set_option maxHeartbeats 2400000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Any finite graph data can be interpolated by a monic, positive even-
degree polynomial, with sum fibers bounded by twice the number of prescribed
points plus two. The degree budget is explicit and is not uniform in T. -/
theorem exists_bounded_interpolant (hF : ringChar F≠2) (T : Finset F) (g : F → F) :
    ∃ P : F[X], P.Monic ∧ P.natDegree=2*(T.card+1) ∧
      (∀ x∈T, P.eval x=g x) ∧ HasBoundedSums (fun x ↦ P.eval x) (2*(T.card+1)) := by
  let I : F[X] := Lagrange.interpolate T id g
  let V : F[X] := Lagrange.nodal T id
  let Q : F[X] := (X*V)^2
  have hV : V.Monic := Lagrange.nodal_monic
  have hQ : Q.Monic := (monic_X.mul hV).pow 2
  have hQdeg : Q.natDegree=2*(T.card+1) := by
    dsimp only [Q]
    rw [natDegree_pow,natDegree_mul X_ne_zero hV.ne_zero,natDegree_X]
    dsimp only [V]
    rw [Lagrange.natDegree_nodal]
    omega
  have hIde : I.degree<(T.card:WithBot ℕ) := Lagrange.degree_interpolate_lt g (fun _ _ _ _ he ↦ he)
  have hIndeg : I.natDegree≤T.card := natDegree_le_of_degree_le hIde.le
  have hlt : I.natDegree<Q.natDegree := by rw [hQdeg]; omega
  have hIQ : I.degree<Q.degree := by
    rw [degree_eq_natDegree hQ.ne_zero,hQdeg]
    exact hIde.trans (by exact_mod_cast (show T.card<2*(T.card+1) by omega))
  refine ⟨I+Q,hQ.add_of_right hIQ,?_,?_,?_⟩
  · rw [natDegree_add_eq_right_of_natDegree_lt hlt,hQdeg]
  · intro x hx
    have hI : I.eval x=g x := Lagrange.eval_interpolate_at_node g (fun _ _ _ _ he ↦ he) hx
    have hVx : V.eval x=0 := Lagrange.eval_nodal_at_node (v := id) hx
    rw [eval_add,hI]
    simp only [Q,eval_pow,eval_mul,eval_X,hVx,mul_zero,zero_pow (by decide : 2≠0),add_zero]
  · have hdeg : (I+Q).natDegree=2*(T.card+1) := by
      rw [natDegree_add_eq_right_of_natDegree_lt hlt,hQdeg]
    have he := even_polynomial_bounded hF (I+Q) (by rw [hdeg]; omega) (by rw [hdeg]; exact even_two_mul _)
    rwa [hdeg] at he

end Erdos66BoundedGraphInterpolation
