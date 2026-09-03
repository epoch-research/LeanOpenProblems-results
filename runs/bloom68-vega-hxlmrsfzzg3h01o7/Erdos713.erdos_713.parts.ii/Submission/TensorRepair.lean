import FormalConjecturesUtil

/-!
# Exact finite bounds for tensor-product subgraphs

The categorical (tensor) product used here requires adjacency in both coordinates;
it is not the box product. For an `H`-free subgraph, the rectangles centered at the
pairs of host vertices give an exact double count of the edges and hence a bound
by the sum of the extremal numbers at the sums of the two host degrees.

All statements are finite, with arbitrary forbidden graph `H`. No asymptotic
claim or resolution of Erdős problem 713 is asserted. This file is standalone
and does not import `Submission.Spec` or any other submission helper.
-/

open SimpleGraph
open scoped Classical

namespace Erdos713TensorRepair

universe u v w

variable {V : Type u} {V' : Type v} {W : Type w}

/-- The categorical/tensor product, with adjacency in both coordinates. -/
def tensor (G : SimpleGraph V) (G' : SimpleGraph V') : SimpleGraph (V × V') where
  Adj x y := G.Adj x.1 y.1 ∧ G'.Adj x.2 y.2
  symm := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  loopless := fun x h => G.loopless x.1 h.1

@[simp]
lemma tensor_adj (G : SimpleGraph V) (G' : SimpleGraph V') (x y : V × V') :
    (tensor G G').Adj x y ↔ G.Adj x.1 y.1 ∧ G'.Adj x.2 y.2 := Iff.rfl

/-- A tensor dart is exactly a pair of darts, one in each factor. -/
def tensorDartEquiv (G : SimpleGraph V) (G' : SimpleGraph V') :
    (tensor G G').Dart ≃ G.Dart × G'.Dart where
  toFun d := (⟨(d.fst.1, d.snd.1), d.adj.1⟩, ⟨(d.fst.2, d.snd.2), d.adj.2⟩)
  invFun p := ⟨((p.1.fst, p.2.fst), (p.1.snd, p.2.snd)), ⟨p.1.adj, p.2.adj⟩⟩
  left_inv := by
    rintro ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, h⟩
    rfl
  right_inv := by
    rintro ⟨⟨⟨a, c⟩, h⟩, ⟨⟨b, d⟩, h'⟩⟩
    rfl

/-- The tensor product has exactly twice the product of the edge counts. -/
theorem card_edges_tensor [Fintype V] [Fintype V']
    (G : SimpleGraph V) (G' : SimpleGraph V') :
    (tensor G G').edgeFinset.card = 2 * G.edgeFinset.card * G'.edgeFinset.card := by
  have h := Fintype.card_congr (tensorDartEquiv G G')
  rw [Fintype.card_prod] at h
  simp only [SimpleGraph.dart_card_eq_twice_card_edges] at h
  nlinarith

/-- A bipartite graph specified by its left-to-right cross relation. -/
def crossGraph {A : Type u} {B : Type v} (r : A → B → Prop) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inr b => r a b
    | .inr b, .inl a => r a b
    | _, _ => False
  symm := by
    intro x y h
    cases x <;> cases y <;> exact h
  loopless := by
    intro x
    cases x <;> exact not_false

/-- The left-to-right cross edges of a relation. -/
abbrev CrossEdges {A : Type u} {B : Type v} (r : A → B → Prop) :=
  {p : A × B // r p.1 p.2}

/-- Every dart of a bipartite cross graph has one of its two orientations. -/
def crossDartEquiv {A : Type u} {B : Type v} (r : A → B → Prop) :
    (crossGraph r).Dart ≃ CrossEdges r ⊕ CrossEdges r where
  toFun d := match d with
    | ⟨(.inl a, .inr b), h⟩ => .inl ⟨(a, b), h⟩
    | ⟨(.inr b, .inl a), h⟩ => .inr ⟨(a, b), h⟩
    | ⟨(.inl _, .inl _), h⟩ => False.elim h
    | ⟨(.inr _, .inr _), h⟩ => False.elim h
  invFun
    | .inl p => ⟨(.inl p.1.1, .inr p.1.2), p.2⟩
    | .inr p => ⟨(.inr p.1.2, .inl p.1.1), p.2⟩
  left_inv := by
    rintro ⟨⟨a | b, c | d⟩, h⟩ <;> first | contradiction | rfl
  right_inv := by
    rintro (⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) <;> rfl

/-- A bipartite cross graph has one undirected edge per related pair. -/
lemma card_edges_crossGraph {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (r : A → B → Prop) :
    (crossGraph r).edgeFinset.card = Fintype.card (CrossEdges r) := by
  have h := Fintype.card_congr (crossDartEquiv r)
  rw [SimpleGraph.dart_card_eq_twice_card_edges, Fintype.card_sum] at h
  omega

/-- The `F`-edges crossing the rectangle centered at `(u,v)`. The two vertex
parts are `N_G(u)` and `N_G'(v)`, mapped to `(x,v)` and `(u,y)` respectively. -/
def rectangle (G : SimpleGraph V) (G' : SimpleGraph V')
    (F : SimpleGraph (V × V')) (u : V) (v : V') :
    SimpleGraph (G.neighborSet u ⊕ G'.neighborSet v) :=
  crossGraph fun x y => F.Adj (x.1, v) (u, y.1)

/-- The two sides of a rectangle embed disjointly into the product vertex set.
Looplessness prevents `(x,v) = (u,y)` when `x` is a neighbor of `u`. -/
def rectangleCopy (G : SimpleGraph V) (G' : SimpleGraph V')
    (F : SimpleGraph (V × V')) (u : V) (v : V') :
    (rectangle G G' F u v).Copy F where
  toHom := {
    toFun := Sum.elim (fun x => (x.1, v)) (fun y => (u, y.1))
    map_rel' := by
      rintro (a | a) (b | b) h
      · exact False.elim h
      · exact h
      · exact F.symm h
      · exact False.elim h }
  injective' := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (Subtype.ext (congrArg Prod.fst h))
    · exact False.elim (G.ne_of_adj a.2 (congrArg Prod.fst h).symm)
    · exact False.elim (G.ne_of_adj b.2 (congrArg Prod.fst h))
    · exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd h))

/-- Ordinary injective `H`-freeness passes to each rectangle. -/
lemma rectangle_free (G : SimpleGraph V) (G' : SimpleGraph V')
    {F : SimpleGraph (V × V')} {H : SimpleGraph W} (hfree : H.Free F)
    (u : V) (v : V') : H.Free (rectangle G G' F u v) :=
  fun h => hfree (h.trans ⟨rectangleCopy G G' F u v⟩)

/-- A rectangle has at most `ex(d_G(u) + d_G'(v), H)` edges. Both neighbor-set
cardinalities use the same classical adjacency decisions as the host degrees. -/
lemma card_edges_rectangle_le [Fintype V] [Fintype V']
    (G : SimpleGraph V) (G' : SimpleGraph V')
    {F : SimpleGraph (V × V')} {H : SimpleGraph W} (hfree : H.Free F)
    (u : V) (v : V') :
    (rectangle G G' F u v).edgeFinset.card ≤
      extremalNumber (G.degree u + G'.degree v) H := by
  have h := card_edgeFinset_le_extremalNumber (rectangle_free G G' hfree u v)
  simpa only [Fintype.card_sum, card_neighborSet_eq_degree] using h

/-- A dart `(a,b) → (c,d)` of a tensor subgraph specifies the cross edge
`(a,b)--(c,d)` in the rectangle centered at `(c,b)`. Reversal gives the other
rectangle, centered at `(a,d)`. This equivalence is the exact double count. -/
def dartRectangleEquiv (G : SimpleGraph V) (G' : SimpleGraph V')
    {F : SimpleGraph (V × V')} (hF : F ≤ tensor G G') :
    F.Dart ≃ Σ u : V, Σ v : V',
      CrossEdges (fun (x : G.neighborSet u) (y : G'.neighborSet v) =>
        F.Adj (x.1, v) (u, y.1)) where
  toFun d := ⟨d.snd.1, d.fst.2,
    ⟨(⟨d.fst.1, (hF d.adj).1.symm⟩, ⟨d.snd.2, (hF d.adj).2⟩), d.adj⟩⟩
  invFun p := ⟨((p.2.2.1.1.1, p.2.1), (p.1, p.2.2.1.2.1)), p.2.2.2⟩
  left_inv := by
    rintro ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, h⟩
    rfl
  right_inv := by
    rintro ⟨u, v, ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩⟩
    rfl

/-- Every edge of a tensor subgraph is counted in exactly two rectangles. -/
lemma sum_card_edges_rectangle [Fintype V] [Fintype V']
    (G : SimpleGraph V) (G' : SimpleGraph V')
    {F : SimpleGraph (V × V')} (hF : F ≤ tensor G G') :
    (∑ u : V, ∑ v : V', (rectangle G G' F u v).edgeFinset.card) =
      2 * F.edgeFinset.card := by
  have h := Fintype.card_congr (dartRectangleEquiv G G' hF)
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at h
  simp only [Fintype.card_sigma] at h
  simpa only [rectangle, card_edges_crossGraph] using h.symm

/-- The exact finite tensor rectangle bound. No finiteness, bipartiteness,
nonemptiness, or other hypothesis is imposed on the forbidden graph `H`. -/
theorem two_mul_card_edges_le_sum_extremalNumber [Fintype V] [Fintype V']
    (G : SimpleGraph V) (G' : SimpleGraph V')
    {F : SimpleGraph (V × V')} {H : SimpleGraph W}
    (hF : F ≤ tensor G G') (hfree : H.Free F) :
    2 * F.edgeFinset.card ≤
      ∑ u : V, ∑ v : V', extremalNumber (G.degree u + G'.degree v) H := by
  rw [← sum_card_edges_rectangle G G' hF]
  exact Finset.sum_le_sum fun u _ =>
    Finset.sum_le_sum fun v _ => card_edges_rectangle_le G G' hfree u v

/-- A uniform local bound gives a uniform finite global bound. -/
theorem two_mul_card_edges_le_card_mul_card_mul [Fintype V] [Fintype V']
    (G : SimpleGraph V) (G' : SimpleGraph V')
    {F : SimpleGraph (V × V')} {H : SimpleGraph W} {B : ℕ}
    (hF : F ≤ tensor G G') (hfree : H.Free F)
    (hB : ∀ u : V, ∀ v : V', extremalNumber (G.degree u + G'.degree v) H ≤ B) :
    2 * F.edgeFinset.card ≤ Fintype.card V * Fintype.card V' * B := by
  calc
    2 * F.edgeFinset.card ≤
        ∑ u : V, ∑ v : V', extremalNumber (G.degree u + G'.degree v) H :=
      two_mul_card_edges_le_sum_extremalNumber G G' hF hfree
    _ ≤ ∑ _u : V, ∑ _v : V', B :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hB u v
    _ = Fintype.card V * Fintype.card V' * B := by simp [mul_assoc]

end Erdos713TensorRepair

-- Audit all explicitly declared theorems, together with the constructions they use.
#print axioms Erdos713TensorRepair.tensor
#print axioms Erdos713TensorRepair.tensor_adj
#print axioms Erdos713TensorRepair.tensorDartEquiv
#print axioms Erdos713TensorRepair.card_edges_tensor
#print axioms Erdos713TensorRepair.crossGraph
#print axioms Erdos713TensorRepair.CrossEdges
#print axioms Erdos713TensorRepair.crossDartEquiv
#print axioms Erdos713TensorRepair.card_edges_crossGraph
#print axioms Erdos713TensorRepair.rectangle
#print axioms Erdos713TensorRepair.rectangleCopy
#print axioms Erdos713TensorRepair.rectangle_free
#print axioms Erdos713TensorRepair.card_edges_rectangle_le
#print axioms Erdos713TensorRepair.dartRectangleEquiv
#print axioms Erdos713TensorRepair.sum_card_edges_rectangle
#print axioms Erdos713TensorRepair.two_mul_card_edges_le_sum_extremalNumber
#print axioms Erdos713TensorRepair.two_mul_card_edges_le_card_mul_card_mul
