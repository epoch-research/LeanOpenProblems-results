import FormalConjecturesUtil

/-! Kernel certificates for four explicit binary-polynomial graph models.
This file does not identify the model with an abstract algebraic norm graph,
and does not assert a counterexample to the rational-exponent conjecture. -/
namespace Erdos713CharTwoOrientation
open SimpleGraph

/-- Nine binary coefficients, reduced modulo X^9+X^4+1 (bit mask 529). -/
abbrev E := Fin 512

private def mulLoop : ℕ → ℕ → ℕ → ℕ
  | 0,_,_ => 0
  | k+1,a,b => Nat.xor (if b%2=1 then a else 0)
      (mulLoop k (if a<256 then 2*a else Nat.xor (2*a) 529) (b/2))

def plus (a b : E) : E := ⟨Nat.xor a.val b.val % 512,Nat.mod_lt _ (by decide)⟩
def times (a b : E) : E := ⟨mulLoop 9 a.val b.val % 512,Nat.mod_lt _ (by decide)⟩

private def powerLoop : ℕ → E → ℕ → E
  | 0,_,_ => 1
  | k+1,a,b => times (if b%2=1 then a else 1) (powerLoop k (times a a) (b/2))

def power (a : E) (b : ℕ) : E := powerLoop 9 a b

def inverse (a : E) : E := power a 510

def norm (z : E) : E := times (times z (power z 8)) (power z 64)

def trace (z : E) : E := plus (plus z (power z 2)) (power z 4)

def orientation (z : E) : E :=
  plus (plus (times z (inverse (plus z (power z 8))))
    (times (power z 8) (inverse (plus (power z 8) (power z 64)))))
    (times (power z 64) (inverse (plus (power z 64) z)))

abbrev Vertex := E × E

def Rel (left right : Bool) (x y : Vertex) : Prop :=
  x.2 ≠ 0 ∧ y.2 ≠ 0 ∧ power x.2 8 = x.2 ∧ power y.2 8 = y.2 ∧
  norm (plus x.1 y.1) = times x.2 y.2 ∧
  plus (plus x.1 y.1) (power (plus x.1 y.1) 8) ≠ 0 ∧
  plus (power (plus x.1 y.1) 8) (power (plus x.1 y.1) 64) ≠ 0 ∧
  plus (power (plus x.1 y.1) 64) (plus x.1 y.1) ≠ 0 ∧
  plus (plus (trace (orientation (plus x.1 y.1))) (if left then trace x.2 else 0))
    (if right then trace y.2 else 0) = 0

def graph (left right : Bool) : SimpleGraph (Vertex ⊕ Vertex) where
  Adj x y := match x,y with
    | .inl a,.inr b => Rel left right a b
    | .inr b,.inl a => Rel left right a b
    | _,_ => False
  symm x y := by cases x <;> cases y <;> exact id
  loopless x := by cases x <;> exact id

def rows (left right : Bool) : Fin 4 → Vertex :=
  match left,right with
  | false,false => ![(70,333),(429,1),(258,332),(338,333)]
  | true,false => ![(65,336),(315,337),(380,333),(129,336)]
  | false,true => ![(28,336),(386,1),(384,337),(416,28)]
  | true,true => ![(422,337),(82,28),(388,337),(235,28)]

def cols (left right : Bool) : Fin 4 → Vertex :=
  match left,right with
  | false,false => ![(101,1),(297,29),(309,336),(491,1)]
  | true,false => ![(66,337),(132,1),(332,332),(438,29)]
  | false,true => ![(122,333),(268,29),(403,332),(507,336)]
  | true,true => ![(190,333),(251,1),(270,333),(387,1)]

lemma rows_injective (left right : Bool) : Function.Injective (rows left right) := by
  cases left <;> cases right <;> unfold rows Function.Injective <;> decide

lemma cols_injective (left right : Bool) : Function.Injective (cols left right) := by
  cases left <;> cases right <;> unfold cols Function.Injective <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
lemma all_incidences (left right : Bool) : ∀ i j, Rel left right (rows left right i) (cols left right j) := by
  intro i j
  cases left <;> cases right <;> fin_cases i <;> fin_cases j <;>
    unfold rows cols Rel <;> decide

lemma contains_K44 (left right : Bool) :
    completeBipartiteGraph (Fin 4) (Fin 4) ⊑ graph left right := by
  refine ⟨⟨⟨Sum.map (rows left right) (cols left right),?_⟩,
    Sum.map_injective.mpr ⟨rows_injective left right,cols_injective left right⟩⟩⟩
  rintro (i|j) (i'|j') h
  · simp [completeBipartiteGraph] at h
  · exact all_incidences left right i j'
  · exact all_incidences left right i' j
  · simp [completeBipartiteGraph] at h

lemma not_free (left right : Bool) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph left right) :=
  fun h => h (contains_K44 left right)

#print axioms all_incidences
#print axioms contains_K44
#print axioms not_free
end Erdos713CharTwoOrientation
