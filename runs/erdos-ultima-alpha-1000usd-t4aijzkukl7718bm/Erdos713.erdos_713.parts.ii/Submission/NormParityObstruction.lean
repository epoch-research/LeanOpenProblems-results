import FormalConjecturesUtil

/-! Explicit obstructions to two Vandermonde-parity refinements of a cubic
norm-graph construction. This is NOT a disproof of Erdős 713. -/
namespace Erdos713NormParity

abbrev Vertex := Fin 4 → ZMod 7

/-- Norm in F_7[t]/(t^3-2), in its coefficient coordinates. -/
def norm (x₀ x₁ x₂ : ZMod 7) : ZMod 7 :=
  x₀^3+2*x₁^3+4*x₂^3-6*x₀*x₁*x₂

/-- Cyclic Vandermonde of x,x^7,x^49. -/
def vandermonde (x : Vertex) : ZMod 7 := 2*(x 1)^3+3*(x 2)^3

def Good (twist : Bool) (x : Vertex) : Prop :=
  x 3 ≠ 0 ∧
    let v := vandermonde x * (if twist then x 3 else 1)
    v = 1 ∨ v = 2 ∨ v = 4

def Rel (x y : Vertex) : Prop :=
  norm (x 0+y 0) (x 1+y 1) (x 2+y 2) = x 3*y 3

def ContainsK44 (twist : Bool) : Prop :=
  ∃ r c : Fin 4 → Vertex,
    Function.Injective r ∧ Function.Injective c ∧
    (∀ i, Good twist (r i)) ∧ (∀ j, Good twist (c j)) ∧
    ∀ i j, Rel (r i) (c j)

def rows : Fin 4 → Vertex :=
  ![![6,3,4,3], ![3,5,3,6], ![3,6,4,5], ![4,0,6,5]]

def cols : Fin 4 → Vertex :=
  ![![0,3,1,4], ![1,3,1,5], ![3,0,6,2], ![3,5,4,3]]

def twistedRows : Fin 4 → Vertex :=
  ![![1,6,3,1], ![3,6,3,2], ![6,1,4,3], ![6,5,5,4]]

def twistedCols : Fin 4 → Vertex :=
  ![![0,1,1,5], ![0,4,3,6], ![4,2,3,6], ![4,3,4,1]]

set_option maxRecDepth 4096 in
lemma untwisted_contains : ContainsK44 false := by
  refine ⟨rows,cols,?_,?_,?_,?_,?_⟩
  · unfold rows Function.Injective
    decide
  · unfold cols Function.Injective
    decide
  · unfold Good vandermonde rows
    decide
  · unfold Good vandermonde cols
    decide
  · unfold Rel norm rows cols
    decide

set_option maxRecDepth 4096 in
lemma twisted_contains : ContainsK44 true := by
  refine ⟨twistedRows,twistedCols,?_,?_,?_,?_,?_⟩
  · unfold twistedRows Function.Injective
    decide
  · unfold twistedCols Function.Injective
    decide
  · unfold Good vandermonde twistedRows
    decide
  · unfold Good vandermonde twistedCols
    decide
  · unfold Rel norm twistedRows twistedCols
    decide

#print axioms untwisted_contains
#print axioms twisted_contains
end Erdos713NormParity
