import FormalConjecturesUtil
import Submission.ThetaGramCount
import Submission.GlobalLightPairs

/-! A uniform upper bound on distinct-pair codegrees in the fixed-Gram
construction. This is an auxiliary finite statement, not Erdos 713. -/
open Finset
namespace Erdos713ThetaGramPairBound
open Erdos713ThetaGram Erdos713GlobalLight
set_option maxHeartbeats 2000000

lemma eq_of_two_evals_and_quadratic {V : Type*} {f g : Coeffs V} {i j : ℝ}
    (hij : i ≠ j) (hi : eval f i = eval g i) (hj : eval f j = eval g j)
    (h2 : f 2 = g 2) : f = g := by
  apply eq_of_eval_eq
  intro x
  have hh := factor_of_two_equal_evals hij hi hj x
  rw [← h2, sub_self, smul_zero, add_zero] at hh
  exact hh.symm

lemma pair_codegree_le {d r N : ℕ} (g : GramCode d N)
    (x y : Columns d r N) (hxy : x ≠ y) :
    codegree (incidence g) x y ≤ N^d := by
  classical
  let S := {a : Fiber g // incidence g a x ∧ incidence g a y}
  let f : S → (Fin d → Fin N) := fun a => a.val.val 2
  have hf : Function.Injective f := by
    intro a b hab
    have htype : x.1 ≠ y.1 := by
      intro he
      apply hxy
      apply Prod.ext he
      exact a.property.1.symm.trans ((congrArg (evalFin a.val.val) he).trans a.property.2)
    have hpar : ((x.1.val : ℝ)+1) ≠ ((y.1.val : ℝ)+1) := by
      intro he
      apply htype
      apply Fin.ext
      have hh : (x.1.val : ℝ) = y.1.val := by linarith
      exact_mod_cast hh
    have hx := (incidence_real g a.property.1).trans (incidence_real g b.property.1).symm
    have hy := (incidence_real g a.property.2).trans (incidence_real g b.property.2).symm
    have h2 : toReal a.val.val 2 = toReal b.val.val 2 := by
      funext v
      exact congrArg (fun z : Fin N => (z.val : ℝ)) (congr_fun hab v)
    have he := eq_of_two_evals_and_quadratic hpar hx hy h2
    exact Subtype.ext (Subtype.ext ((toReal_injective d N) he))
  have hc := Fintype.card_le_of_injective f hf
  simpa only [S, codegree, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin] using hc

#print axioms eq_of_two_evals_and_quadratic
#print axioms pair_codegree_le
end Erdos713ThetaGramPairBound
