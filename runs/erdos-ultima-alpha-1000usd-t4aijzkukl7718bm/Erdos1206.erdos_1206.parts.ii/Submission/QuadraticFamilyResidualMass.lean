import Submission.NearUnitPrimitiveMass
import Submission.QuadraticFamilyAvoidance

/-!
After excluding every specialization of any finite list of rational quadratic
families, the remaining primitive cubic collisions still have divergent
reciprocal height mass. This is not a density-zero result for independent sets.
-/
namespace Erdos1206.QuadraticFamilyResidualMass
open FermatCubicConics QuadraticFamilyAvoidance
open PrimitiveCollisionMass (Collision)

/-- Primitive collisions outside the linearized planes of all listed families. -/
def Outside {ι : Type*} (a b c d : ι → Vec) (e : Collision) : Prop :=
  ∀ i x, ¬ (linear (a i) x=(e.val.1:ℚ) ∧ linear (b i) x=(e.val.2.1:ℚ) ∧
    linear (c i) x=(e.val.2.2.1:ℚ) ∧ linear (d i) x=(e.val.2.2.2:ℚ))

lemma residual_outside {ι : Type*} (a b c d : ι → Vec) (H : ℕ)
    (hbound : ∀ i x, OrderedInstance (a i) (b i) (c i) (d i) x →
      ((H:ℚ)+1)*(linear (d i) x-linear (c i) x) ≤
        H*(linear (b i) x-linear (a i) x))
    (e : NearUnitPrimitiveMass.Residual H) : Outside a b c d e.val := by
  intro i x hx
  obtain ⟨ha,hb,hc,hd⟩ := hx
  have he := e.val.property
  have hi : OrderedInstance (a i) (b i) (c i) (d i) x := by
    simp only [OrderedInstance,ha,hb,hc,hd]
    exact ⟨by exact_mod_cast he.1,by exact_mod_cast he.2.1,
      by exact_mod_cast he.2.2.1.le,by exact_mod_cast he.2.2.2.1,
      by exact_mod_cast he.2.2.2.2.1⟩
  have hh := hbound i x hi
  rw [ha,hb,hc,hd,← Nat.cast_sub he.2.2.2.1.le,← Nat.cast_sub he.2.1.le] at hh
  have hh' : (H+1)*(e.val.val.2.2.2-e.val.val.2.2.1) ≤
      H*(e.val.val.2.1-e.val.val.1) := by exact_mod_cast hh
  exact (not_lt_of_ge hh') e.property

/-- Finite-family removal cannot make the sum of reciprocal primitive heights
converge, even when the entire coefficient plane of each family is removed. -/
theorem outside_reciprocal_heights_not_summable {ι : Type*} [Finite ι]
    (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3) :
    ¬ Summable (fun e : {e : Collision // Outside a b c d e} =>
      (1:ℝ)/e.val.val.2.2.2) := by
  intro hs
  obtain ⟨H,hH,hbound⟩ := finite_uniform_gap_bound a b c d hc
  let f : NearUnitPrimitiveMass.Residual H → {e : Collision // Outside a b c d e} :=
    fun e => ⟨e.val,residual_outside a b c d H (fun i x hx => (hbound i x hx).1) e⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh : (f x).val=(f y).val :=
      congrArg (fun e : {e : Collision // Outside a b c d e} => e.val) he
    exact Subtype.ext hh
  have hcomp := hs.comp_injective hf
  exact NearUnitPrimitiveMass.residual_reciprocal_heights_not_summable H hcomp

#print axioms outside_reciprocal_heights_not_summable
end Erdos1206.QuadraticFamilyResidualMass
