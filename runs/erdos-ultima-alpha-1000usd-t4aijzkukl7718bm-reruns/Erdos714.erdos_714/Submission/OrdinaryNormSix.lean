import Submission.FourBySix
import Submission.QuinticNormProduct
import Submission.CharThreeNorm

/-!
An actual K46 in characteristic-three cubic norm graphs WHEN -1 IS A SQUARE,
and its sharp local7/8 thinning bound. This constant loss does not settle Erdős 714.

The second triple of columns uses c,c+u,c-u with u^2=-1 and DIFFERENT weights.
Using c,c+1,c-1 with a common weight would be an invalid certificate.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Polynomial SimpleGraph Classical
open Erdos714QuinticNormProduct (element norm_plane plane_element_injective exists_cubic_power_basis)
namespace Erdos714OrdinaryNormSix
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The ordinary weighted norm graph, in the edge-transitive representation. -/
def graph : SimpleGraph ((E × Fˣ) ⊕ (E × Fˣ)) :=
  Erdos714WeightedPower.graph (Units.map (Algebra.norm F (S := E)))

lemma relation_iff [FiniteDimensional F E] (p q : E × Fˣ) :
    Erdos714WeightedPower.relation (Units.map (Algebra.norm F (S := E))) p q ↔
      Algebra.norm F (p.1+q.1) = (p.2 : F)*(q.2 : F) := by
  constructor
  · rintro ⟨z,hz,hν⟩
    have h := congrArg (fun u : Fˣ => (u : F)) hν
    change Algebra.norm F (z : E) = (p.2 : F)*(q.2 : F) at h
    rwa [hz] at h
  · intro h
    have hn : Algebra.norm F (p.1+q.1) ≠ 0 := by rw [h]; exact mul_ne_zero p.2.ne_zero q.2.ne_zero
    let z : Eˣ := Units.mk0 (p.1+q.1) (Algebra.norm_ne_zero_iff.mp hn)
    refine ⟨z,rfl,?_⟩
    apply Units.ext
    exact h

variable [CharP F 3]

private lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hz : (1 : F) = 0 := by linear_combination h3+h
  exact one_ne_zero hz

def tri : Fin 3 → F := ![0,1,-1]

lemma tri_injective : Function.Injective (tri (F := F)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [tri, neg_one_ne_one, Ne.symm neg_one_ne_one] at h ⊢

def rowPoint : Fin 4 → F × F := ![(0,0),(1,0),(-1,0),(0,1)]
def colPoint (c u : F) (j : Bool × Fin 3) : F × F :=
  if j.1 then (c+u*tri j.2,-1) else (tri j.2,1)

lemma rowPoint_injective : Function.Injective (rowPoint (F := F)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [rowPoint, neg_one_ne_one, Ne.symm neg_one_ne_one] at h ⊢

lemma colPoint_injective (c u : F) (hu : u ≠ 0) : Function.Injective (colPoint c u) := by
  rintro ⟨s,i⟩ ⟨t,j⟩ h
  cases s <;> cases t
  · have hij : i = j := tri_injective (congrArg Prod.fst h)
    subst j
    rfl
  · have h' := congrArg Prod.snd h
    simp [colPoint, Ne.symm neg_one_ne_one] at h'
  · have h' := congrArg Prod.snd h
    simp [colPoint, neg_one_ne_one] at h'
  · have he : u*tri i = u*tri j := add_left_cancel (congrArg Prod.fst h)
    have hij : i = j := tri_injective (mul_left_cancel₀ hu he)
    subst j
    rfl

/-- The second triple solves t^3+t=c^3+c, not t^3-t=c^3-c. -/
lemma shifted_cube (c u : F) (hu : u^2 = -1) (j : Fin 3) :
    (c+u*tri j)^3+(c+u*tri j) = c^3+c := by
  have hu3 : u^3 = -u := by calc
    u^3 = u*u^2 := by ring
    _ = -u := by rw [hu]; ring
  have hp : (c+u)^3 = c^3+u^3 := add_pow_char c u 3
  have hm : (c-u)^3 = c^3-u^3 := sub_pow_char c u
  fin_cases j <;> simp [tri, ← sub_eq_add_neg, hp, hm, hu3]

/-- Six columns, assuming a square root of minus one in the base field. -/
def parameterCopy (c u : F) (hu : u^2 = -1) (hd : -c^3-c ≠ 0)
    (z : E) (hz : z^3 = z+algebraMap F E (-c^3-c))
    (B : Module.Basis (Fin 3) F E) (hB : ∀ i, B i = z^(i : ℕ)) :
    Erdos714FourBySix.Block.Copy (graph (F := F) (E := E)) := by
  letI : FiniteDimensional F E := Module.Finite.of_basis B
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hcn (j : Fin 3) : c+u*tri j ≠ 0 := by
    intro h
    have he := shifted_cube c u hu j
    rw [h, zero_pow (by decide), zero_add] at he
    apply hd
    linear_combination he
  let D : Fˣ := Units.mk0 (-c^3-c) hd
  let A (j : Fin 3) : Fˣ := Units.mk0 (-(c+u*tri j)^3)
    (neg_ne_zero.mpr (pow_ne_zero 3 (hcn j)))
  let L : Fin 4 ↪ E × Fˣ := ⟨fun i =>
    (element z (rowPoint (F := F) i).1 (rowPoint (F := F) i).2 0, if i = 3 then -1 else 1), by
      intro i j hij
      exact rowPoint_injective (plane_element_injective z B hB (congrArg Prod.fst hij))⟩
  let R : (Bool × Fin 3) ↪ E × Fˣ := ⟨fun j =>
    (element z (colPoint c u j).1 (colPoint c u j).2 0, if j.1 then A j.2 else D), by
      intro i j hij
      exact colPoint_injective c u hu0 (plane_element_injective z B hB (congrArg Prod.fst hij))⟩
  have hadd (p q : F × F) : element z p.1 p.2 0+element z q.1 q.2 0 =
      element z (p.1+q.1) (p.2+q.2) 0 := by
    simp only [element, map_add, map_zero, zero_mul, add_zero]
    ring
  have hedge (i : Fin 4) (j : Bool × Fin 3) :
      Erdos714WeightedPower.relation (Units.map (Algebra.norm F (S := E))) (L i) (R j) := by
    rw [relation_iff]
    change Algebra.norm F (element z (rowPoint (F := F) i).1 (rowPoint (F := F) i).2 0+
      element z (colPoint c u j).1 (colPoint c u j).2 0) = _
    rw [hadd, norm_plane (-c^3-c) z hz B hB]
    rcases j with ⟨s,j⟩
    have hu3 : u^3 = -u := by calc
      u^3 = u*u^2 := by ring
      _ = -u := by rw [hu]; ring
    cases s <;> fin_cases i <;> fin_cases j <;>
      simp [L,R,D,A,rowPoint,colPoint,tri] <;>
      ring_nf <;> reduce_mod_char!
    all_goals try simp only [hu3]
    all_goals ring_nf
    all_goals reduce_mod_char!
    all_goals ring_nf
    all_goals reduce_mod_char!
  let C : (completeBipartiteGraph (Fin 4) (Bool × Fin 3)).Copy (graph (F := F) (E := E)) :=
    ⟨⟨L.sumMap R, by
      intro v w h
      cases v with
      | inl i =>
        cases w with
        | inl j => simp at h
        | inr j => exact hedge i j
      | inr j =>
        cases w with
        | inr i => simp at h
        | inl i => exact hedge i j⟩, (L.sumMap R).injective⟩
  let e : Fin 6 ↪ Bool × Fin 3 := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by decide))
  let K : Erdos714FourBySix.Block.Copy (completeBipartiteGraph (Fin 4) (Bool × Fin 3)) :=
    ⟨⟨(Function.Embedding.refl (Fin 4)).sumMap e, by
      intro v w h
      cases v <;> cases w <;> simp_all⟩, ((Function.Embedding.refl (Fin 4)).sumMap e).injective⟩
  exact C.comp K

/-- The field-norm copy exists when -1 is a square in the base field.
The defining Artin--Schreier cubic is proved irreducible. -/
theorem contains_four_by_six [Finite F] (u : F) (hu : u^2 = -1) (hdim : Module.finrank F E = 3) :
    Nonempty (Erdos714FourBySix.Block.Copy (graph (F := F) (E := E))) := by
  obtain ⟨c,hc⟩ := Erdos714CharThreeNorm.exists_outside_artinSchreier (F := F)
  obtain ⟨_,hd0,hirr⟩ := Erdos714CharThreeNorm.parameter_irreducible c hc
  obtain ⟨z,hz,B,hB⟩ := exists_cubic_power_basis hdim (-c^3-c) hirr
  exact ⟨parameterCopy c u hu hd0 z hz B hB⟩

/-- This is a necessary CONSTANT-fraction loss for a free thinning. It is not
a vanishing-density obstruction and does not exclude the desired construction. -/
theorem thinning_bound [Fintype F] [Fintype E] (u : F) (hu : u^2 = -1) (hdim : Module.finrank F E = 3)
    (H : SimpleGraph ((E × Fˣ) ⊕ (E × Fˣ))) (hH : H ≤ graph (F := F) (E := E))
    (hf : Erdos714FourBySix.Forbidden.Free H) :
    8*H.edgeFinset.card ≤ 7*(graph (F := F) (E := E)).edgeFinset.card := by
  obtain ⟨c⟩ := contains_four_by_six u hu hdim
  exact Erdos714FourBySix.weighted_power_bound _ c H hH hf

/-- Cardinality formulation of the square-minus-one hypothesis. -/
theorem contains_four_by_six_of_card [Fintype F]
    (hq : Fintype.card F % 4 = 1) (hdim : Module.finrank F E = 3) :
    Nonempty (Erdos714FourBySix.Block.Copy (graph (F := F) (E := E))) := by
  have hs : IsSquare (-1 : F) := FiniteField.isSquare_neg_one_iff.mpr (by omega)
  obtain ⟨u,hu⟩ := hs
  exact contains_four_by_six u (by simpa only [pow_two] using hu.symm) hdim

/-- A necessary constant loss on this family, not a vanishing-density theorem. -/
theorem thinning_bound_of_card [Fintype F] [Fintype E]
    (hq : Fintype.card F % 4 = 1) (hdim : Module.finrank F E = 3)
    (H : SimpleGraph ((E × Fˣ) ⊕ (E × Fˣ))) (hH : H ≤ graph (F := F) (E := E))
    (hf : Erdos714FourBySix.Forbidden.Free H) :
    8*H.edgeFinset.card ≤ 7*(graph (F := F) (E := E)).edgeFinset.card := by
  obtain ⟨c⟩ := contains_four_by_six_of_card hq hdim
  exact Erdos714FourBySix.weighted_power_bound _ c H hH hf

#print axioms relation_iff
#print axioms parameterCopy
#print axioms contains_four_by_six
#print axioms thinning_bound
#print axioms contains_four_by_six_of_card
#print axioms thinning_bound_of_card
end Erdos714OrdinaryNormSix
