import Submission.QuarticDiagonalSeven
import Submission.IrreducibleCoprimeExtension

/-! The diagonal quartic obstruction persists under odd-degree base extension.
This is a construction obstruction, not a disproof of Erdős714. -/
noncomputable section
open Polynomial SimpleGraph
namespace Erdos714QuarticDiagonalOddBase
open Erdos714QuarticDiagonalSeven
variable (F : Type*) [Field F] [Algebra (ZMod 7) F] [FiniteDimensional (ZMod 7) F]

/-- The same quartic is irreducible over every odd-degree extension of F7. -/
theorem irreducible_map (hodd : Odd (Module.finrank (ZMod 7) F)) :
    Irreducible (p.map (algebraMap (ZMod 7) F)) := by
  apply Erdos714CoprimeBaseChange.irreducible_map p irreducible_p monic_p
  rw [degree_p]
  simpa using (Nat.coprime_two_left.mpr hodd).pow_left 2

/-- Uniform actual norm-graph failure, not an extrapolation from q=7. -/
theorem not_free [Fintype F] (hodd : Odd (Module.finrank (ZMod 7) F)) :
    letI : Fact (Irreducible (p.map (algebraMap (ZMod 7) F))) := ⟨irreducible_map F hodd⟩
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714QuarticDiagonal.graph (F := F)
        (E := AdjoinRoot (p.map (algebraMap (ZMod 7) F))) (4 : F)) := by
  let f := algebraMap (ZMod 7) F
  have hf4 : f (4 : ZMod 7) = (4 : F) := map_ofNat f 4
  have he0 : p.eval 0 = p.coeff 0  := (coeff_zero_eq_eval_zero p).symm
  let x : Fin 4 → ZMod 7 := ![1,2,3,4]
  have hx : Function.Injective x := by decide
  have hw : ∀ i, x i^4+(4 : ZMod 7) ≠ 0 := by decide
  have hb : p.eval 0+(4 : ZMod 7) ≠ 0 := by norm_num [p]; decide
  have he : ∀ i, p.eval (x i) = (x i^4+(4 : ZMod 7))*(p.eval 0+4) := by
    intro i
    fin_cases i <;> norm_num [x,p] <;> decide
  apply Erdos714QuarticDiagonal.irreducible_not_free
    (p.map f) (irreducible_map F hodd) (monic_p.map f)
    (by rw [natDegree_map,degree_p]) (fun i => f (x i)) (f.injective.comp hx) 4
  · intro i
    have h := (_root_.map_ne_zero f).mpr (hw i)
    simpa [hf4] using h
  · have h := (_root_.map_ne_zero f).mpr hb
    simpa [eval_map,eval₂_at_apply,hf4,he0] using h
  · intro i
    have h := congrArg f (he i)
    simpa [eval_map,eval₂_at_apply,hf4,he0] using h

#print axioms irreducible_map
#print axioms not_free
end Erdos714QuarticDiagonalOddBase
