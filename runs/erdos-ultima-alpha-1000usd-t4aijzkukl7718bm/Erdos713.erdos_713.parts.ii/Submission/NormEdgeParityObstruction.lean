import FormalConjecturesUtil

/-! Explicit K44 certificates for cubic-Vandermonde EDGE restrictions.
These reject auxiliary constructions, not the original rationality conjecture. -/
namespace Erdos713NormEdgeParity
open SimpleGraph

abbrev Vertex := Fin 4 → ZMod 7

def norm (a b c : ZMod 7) : ZMod 7 := a^3+2*b^3+4*c^3-6*a*b*c

def vandermonde (a b : ZMod 7) : ZMod 7 := 2*a^3+3*b^3

def NonzeroSquare (a : ZMod 7) : Prop := a = 1 ∨ a = 2 ∨ a = 4

/-- All four possible choices of left/right scalar factors are tested. -/
def Rel (left right : Bool) (x y : Vertex) : Prop :=
  x 3 ≠ 0 ∧ y 3 ≠ 0 ∧ norm (x 0+y 0) (x 1+y 1) (x 2+y 2) = x 3*y 3 ∧
    NonzeroSquare (vandermonde (x 1+y 1) (x 2+y 2) *
      (if left then x 3 else 1) * (if right then y 3 else 1))

def graph (left right : Bool) : SimpleGraph (Vertex ⊕ Vertex) where
  Adj x y := match x,y with
    | .inl a,.inr b => Rel left right a b
    | .inr b,.inl a => Rel left right a b
    | _,_ => False
  symm x y := by cases x <;> cases y <;> exact id
  loopless x := by cases x <;> exact id

def plainRows : Fin 4 → Vertex :=
  ![![4,2,4,1], ![1,3,1,3], ![5,2,4,5], ![5,0,4,5]]

def plainCols : Fin 4 → Vertex :=
  ![![0,2,3,3], ![2,3,1,3], ![3,2,3,2], ![5,2,3,3]]

def leftRows : Fin 4 → Vertex :=
  ![![2,4,4,5], ![2,5,6,5], ![3,6,5,1], ![4,1,4,4]]

def leftCols : Fin 4 → Vertex :=
  ![![2,4,6,5], ![5,4,5,4], ![5,4,6,1], ![6,4,6,6]]

def bothRows : Fin 4 → Vertex :=
  ![![4,3,6,1], ![1,0,4,3], ![4,3,1,1], ![6,3,1,1]]

def bothCols : Fin 4 → Vertex :=
  ![![3,3,3,2], ![5,4,3,5], ![6,4,3,3], ![6,4,4,2]]

def rows (left right : Bool) : Fin 4 → Vertex :=
  match left,right with
  | false,false => plainRows
  | true,false => leftRows
  | false,true => leftCols
  | true,true => bothRows

def cols (left right : Bool) : Fin 4 → Vertex :=
  match left,right with
  | false,false => plainCols
  | true,false => leftCols
  | false,true => leftRows
  | true,true => bothCols

set_option maxRecDepth 4096 in
lemma rows_injective (left right : Bool) : Function.Injective (rows left right) := by
  cases left <;> cases right <;>
    unfold rows plainRows leftRows leftCols bothRows Function.Injective <;> decide

set_option maxRecDepth 4096 in
lemma cols_injective (left right : Bool) : Function.Injective (cols left right) := by
  cases left <;> cases right <;>
    unfold cols plainCols leftRows leftCols bothCols Function.Injective <;> decide

set_option maxRecDepth 4096 in
lemma all_incidences (left right : Bool) : ∀ i j, Rel left right (rows left right i) (cols left right j) := by
  cases left <;> cases right <;>
    unfold rows cols plainRows plainCols leftRows leftCols bothRows bothCols Rel norm vandermonde NonzeroSquare <;>
    decide

/-- Every tested edge refinement contains a tagged K44. -/
lemma contains_K44 (left right : Bool) :
    completeBipartiteGraph (Fin 4) (Fin 4) ⊑ graph left right := by
  let f : Fin 4 ⊕ Fin 4 → Vertex ⊕ Vertex := Sum.map (rows left right) (cols left right)
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => simp [completeBipartiteGraph] at hxy
      | inr j => exact all_incidences left right i j
    | inr j =>
      cases y with
      | inl i => exact all_incidences left right i j
      | inr i => simp [completeBipartiteGraph] at hxy
  · exact Sum.map_injective.mpr ⟨rows_injective left right,cols_injective left right⟩

lemma not_free (left right : Bool) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph left right) :=
  fun h => h (contains_K44 left right)

#print axioms all_incidences
#print axioms contains_K44
#print axioms not_free
end Erdos713NormEdgeParity
