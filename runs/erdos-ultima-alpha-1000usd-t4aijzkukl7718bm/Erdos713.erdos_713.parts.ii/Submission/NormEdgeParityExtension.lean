import FormalConjecturesUtil
import Submission.NormEdgeParityObstruction

/-! The finite K44 certificates survive scalar extension to every field of
characteristic seven. Thus these polynomial edge restrictions do not merely
have a small-field exception. Other characteristics are not addressed. -/
namespace Erdos713NormEdgeExtension
open SimpleGraph
open Erdos713NormEdgeParity

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

variable {F : Type*} [Field F]

abbrev Coord (F : Type*) := Fin 4 → F

def normF (a b c : F) : F := a^3+2*b^3+4*c^3-6*a*b*c

def valueF (left right : Bool) (x y : Coord F) : F :=
  (2*(x 1+y 1)^3+3*(x 2+y 2)^3) *
    (if left then x 3 else 1) * (if right then y 3 else 1)

def RelF (left right : Bool) (x y : Coord F) : Prop :=
  x 3 ≠ 0 ∧ y 3 ≠ 0 ∧ normF (x 0+y 0) (x 1+y 1) (x 2+y 2) = x 3*y 3 ∧
    valueF left right x y ≠ 0 ∧ IsSquare (valueF left right x y)

def graphF (left right : Bool) : SimpleGraph (Coord F ⊕ Coord F) where
  Adj x y := match x,y with
    | .inl a,.inr b => RelF left right a b
    | .inr b,.inl a => RelF left right a b
    | _,_ => False
  symm x y := by cases x <;> cases y <;> exact id
  loopless x := by cases x <;> exact id

lemma nonzeroSquare_sound {a : ZMod 7} (ha : NonzeroSquare a) : a ≠ 0 ∧ IsSquare a := by
  rcases ha with rfl | rfl | rfl
  · exact ⟨by decide,1,by decide⟩
  · exact ⟨by decide,3,by decide⟩
  · exact ⟨by decide,2,by decide⟩

def mapCoord (φ : ZMod 7 →+* F) (x : Vertex) : Coord F := fun i => φ (x i)

lemma mapCoord_injective (φ : ZMod 7 →+* F) : Function.Injective (mapCoord φ) := by
  intro x y h
  funext i
  exact φ.injective (congrFun h i)

lemma value_map (φ : ZMod 7 →+* F) (left right : Bool) (x y : Vertex) :
    valueF left right (mapCoord φ x) (mapCoord φ y) =
      φ (vandermonde (x 1+y 1) (x 2+y 2) *
        (if left then x 3 else 1) * (if right then y 3 else 1)) := by
  cases left <;> cases right <;> norm_num [valueF,mapCoord,vandermonde,map_ofNat φ 2,map_ofNat φ 3]

lemma rel_map (φ : ZMod 7 →+* F) {left right : Bool} {x y : Vertex}
    (h : Rel left right x y) : RelF left right (mapCoord φ x) (mapCoord φ y) := by
  obtain ⟨hx,hy,hn,hgood⟩ := h
  refine ⟨(map_ne_zero φ).mpr hx,(map_ne_zero φ).mpr hy,?_,?_⟩
  · have hh := congrArg φ hn
    norm_num [Erdos713NormEdgeParity.norm,normF,mapCoord,
      map_ofNat φ 2,map_ofNat φ 4,map_ofNat φ 6] at hh ⊢
    exact hh
  · obtain ⟨hne,hsq⟩ := nonzeroSquare_sound hgood
    rw [value_map]
    exact ⟨(map_ne_zero φ).mpr hne,hsq.map φ⟩

def scalarCopy (φ : ZMod 7 →+* F) (left right : Bool) :
    (graph left right).Copy (graphF (F := F) left right) := by
  refine ⟨⟨Sum.map (mapCoord φ) (mapCoord φ),?_⟩,
    Sum.map_injective.mpr ⟨mapCoord_injective φ,mapCoord_injective φ⟩⟩
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hxy.elim
    | inr y => exact rel_map φ hxy
  | inr x =>
    cases y with
    | inl y => exact rel_map φ hxy
    | inr y => exact hxy.elim

lemma contains_K44_of_hom (φ : ZMod 7 →+* F) (left right : Bool) :
    completeBipartiteGraph (Fin 4) (Fin 4) ⊑ graphF (F := F) left right :=
  (Erdos713NormEdgeParity.contains_K44 left right).trans ⟨scalarCopy φ left right⟩

/-- Every characteristic-seven field has the obstruction, in each of the
four binary scalar twists. The vertex restrictions use actual nonzero squares. -/
lemma contains_K44 [CharP F 7] (left right : Bool) :
    completeBipartiteGraph (Fin 4) (Fin 4) ⊑ graphF (F := F) left right :=
  contains_K44_of_hom (ZMod.castHom (dvd_refl 7) F) left right

lemma not_free [CharP F 7] (left right : Bool) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graphF (F := F) left right) :=
  fun h => h (contains_K44 left right)

/-- The polynomial ansatz fails on arbitrarily large finite fields, even
along extension degrees congruent to one modulo six. -/
lemma arbitrarily_large_fields (N : ℕ) :
    ∃ d : ℕ, 0 < d ∧ d % 6 = 1 ∧ N < Nat.card (GaloisField 7 d) ∧
      ∀ left right : Bool,
        ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
          (graphF (F := GaloisField 7 d) left right) := by
  refine ⟨6*N+1,by omega,by omega,?_,fun left right => not_free left right⟩
  rw [GaloisField.card 7 (6*N+1) (by omega)]
  exact (show N ≤ 6*N+1 by omega).trans_lt (Nat.lt_pow_self (by decide : 1 < 7))

#print axioms scalarCopy
#print axioms contains_K44
#print axioms not_free
#print axioms arbitrarily_large_fields
end Erdos713NormEdgeExtension
