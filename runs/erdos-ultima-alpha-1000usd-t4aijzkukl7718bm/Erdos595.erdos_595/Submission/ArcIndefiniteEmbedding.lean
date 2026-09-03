import Submission.IndefiniteUnitOrthogonality
import Submission.ArcTwoCover

/-!
The full arc graph embeds inducedly in the signature (3,1) unit-orthogonality
graph over an arbitrary ordered field. Finite-dimensional orthogonality does
not in itself imply countable proper vertex colorability. This is not a
non-coverability result.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ArcIndefinite
open Erdos595IndefiniteUnit Erdos595ArcAdjoint

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev Pair (K : Type*) [Field K] := Arc (⊤ : SimpleGraph K)

def vector (p : Pair K) : Space K 3 1 :=
  (![p.val.1 / (p.val.1 - p.val.2), p.val.2 / (p.val.1 - p.val.2),
      (p.val.1 * p.val.2 - 1/2) / (p.val.1 - p.val.2)],
    ![(p.val.1 * p.val.2 + 1/2) / (p.val.1 - p.val.2)])

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma denominator (p : Pair K) : p.val.1 - p.val.2 ≠ 0 :=
  sub_ne_zero.mpr p.property.ne

lemma inner_formula (p q : Pair K) :
    form (vector p) (vector q) =
      ((p.val.1 - q.val.2) * (q.val.1 - p.val.2)) /
        ((p.val.1 - p.val.2) * (q.val.1 - q.val.2)) := by
  simp only [form, vector, dotProduct, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero]
  field_simp [denominator p, denominator q]
  ring

lemma unit (p : Pair K) : form (vector p) (vector p) = 1 := by
  rw [inner_formula]
  exact div_self (mul_ne_zero (denominator p) (denominator p))

def point (p : Pair K) : UnitPoint K 3 1 := ⟨vector p, unit p⟩

lemma point_adj_iff (p q : Pair K) :
    (graph K 3 1).Adj (point p) (point q) ↔
      (arcGraph (⊤ : SimpleGraph K)).Adj p q := by
  change form (vector p) (vector q) = 0 ↔ _
  rw [inner_formula, div_eq_zero_iff]
  simp only [mul_eq_zero, sub_eq_zero, denominator p, denominator q,
    or_false]
  change (p.val.1 = q.val.2 ∨ q.val.1 = p.val.2) ↔
    (p.val.2 = q.val.1 ∨ q.val.2 = p.val.1)
  tauto

lemma point_injective : Function.Injective (point (K := K)) := by
  intro p q he
  have hv : vector p = vector q := congrArg Subtype.val he
  have h₀ := congrArg (fun x : Space K 3 1 => x.1 0) hv
  have h₁ := congrArg (fun x : Space K 3 1 => x.1 1) hv
  have h₂ := congrArg (fun x : Space K 3 1 => x.1 2 - x.2 0) hv
  have hd : p.val.1 - p.val.2 = q.val.1 - q.val.2 := by
    have h : -(1 / (p.val.1 - p.val.2)) = -(1 / (q.val.1 - q.val.2)) := by
      change ((p.val.1 * p.val.2 - 1/2) / (p.val.1 - p.val.2) -
        (p.val.1 * p.val.2 + 1/2) / (p.val.1 - p.val.2)) =
        ((q.val.1 * q.val.2 - 1/2) / (q.val.1 - q.val.2) -
        (q.val.1 * q.val.2 + 1/2) / (q.val.1 - q.val.2)) at h₂
      convert h₂ using 1 <;> ring
    have hh := neg_injective h
    simpa only [one_div, inv_inj] using hh
  apply Subtype.ext
  apply Prod.ext
  · change p.val.1 / (p.val.1 - p.val.2) = q.val.1 / (q.val.1 - q.val.2) at h₀
    rw [hd] at h₀
    exact (div_left_inj' (denominator q)).mp h₀
  · change p.val.2 / (p.val.1 - p.val.2) = q.val.2 / (q.val.1 - q.val.2) at h₁
    rw [hd] at h₁
    exact (div_left_inj' (denominator q)).mp h₁

def embedding : arcGraph (⊤ : SimpleGraph K) ↪g graph K 3 1 where
  toFun := point
  inj' := point_injective
  map_rel_iff' := point_adj_iff _ _

/-- A proper coloring of the orthogonality graph encodes every field element
by a distinct set of colors. This is a vertex-coloring bound, not an
edge-covering obstruction. -/
theorem color_sets {C : Type*} (c : (graph K 3 1).Coloring C) :
    ∃ f : K → Set C, Function.Injective f := by
  classical
  let a : (arcGraph (⊤ : SimpleGraph K)).Coloring C := c.comp embedding.toHom
  let f : K → Set C := fun x => {k | ∃ p : Pair K, p.val.1 = x ∧ a p = k}
  refine ⟨f,?_⟩
  intro x y he
  by_contra hxy
  let p : Pair K := ⟨(x,y),hxy⟩
  have hp : a p ∈ f x := ⟨p,rfl,rfl⟩
  rw [he] at hp
  obtain ⟨q,hq,ha⟩ := hp
  have hadj : (arcGraph (⊤ : SimpleGraph K)).Adj p q := Or.inl hq.symm
  exact a.valid hadj ha.symm

/-- A countable proper coloring would force the field to have cardinality
at most continuum, even though this four-dimensional graph does have a
countable triangle-free EDGE cover. -/
theorem cardinal_bound {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hc : Nonempty ((graph K 3 1).Coloring ℕ)) : Cardinal.mk K ≤ Cardinal.continuum := by
  obtain ⟨c⟩ := hc
  obtain ⟨f,hf⟩ := color_sets c
  have h := Cardinal.mk_le_of_injective hf
  simpa only [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.two_power_aleph0] using h

#print axioms color_sets
#print axioms cardinal_bound
#print axioms inner_formula
#print axioms embedding
end Erdos595ArcIndefinite
