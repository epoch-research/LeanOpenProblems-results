import Submission.MiddleCornerObstruction

/-!
A positive sufficient condition for Erdős 595, with a genuine missing
hypothesis: an asymmetric ordered-triangle Ramsey graph for an infinite
shift-square target and a finite odd wheel. Existence of a K4-free Ramsey
graph with this property is NOT proved here.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595TriangleArrow

variable {U V : Type*}

def OrderedTriangle [LinearOrder V] (G : SimpleGraph V) (a b c : V) : Prop :=
  a < b ∧ b < c ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c

def MiddleDifferent [LinearOrder V] (G : SimpleGraph V)
    (c : Sym2 V → ℕ) : Prop :=
  ∀ a b d, OrderedTriangle G a b d → c s(a,b) ≠ c s(b,d)

/-- An odd wheel with its apex between the two sides of a path around the rim.
The rim is 0--4--1--5--2--0 and the apex is 3. -/
def wheelAdj (a b : Fin 6) : Prop :=
  (a,b) ∈ ([(0,3),(1,3),(2,3),(3,4),(3,5),(0,4),(1,4),(1,5),(2,5),(0,2),
    (3,0),(3,1),(3,2),(4,3),(5,3),(4,0),(4,1),(5,1),(5,2),(2,0)] : List (Fin 6 × Fin 6))

instance : DecidableRel wheelAdj := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List _)))

private theorem wheel_symm : ∀ a b, wheelAdj a b → wheelAdj b a := by decide +kernel
private theorem wheel_irrefl : ∀ a, ¬wheelAdj a a := by decide +kernel

def W : SimpleGraph (Fin 6) where
  Adj := wheelAdj
  symm := wheel_symm
  loopless := wheel_irrefl

instance : DecidableRel W.Adj := inferInstanceAs (DecidableRel wheelAdj)
instance (a b c : Fin 6) : Decidable (OrderedTriangle W a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

private theorem wheel_no_four : ∀ a b c d : Fin 6,
    ¬(wheelAdj a b ∧ wheelAdj a c ∧ wheelAdj a d ∧
      wheelAdj b c ∧ wheelAdj b d ∧ wheelAdj c d) := by decide +kernel

theorem W_cliqueFree : W.CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  apply wheel_no_four (e 0) (e 1) (e 2) (e 3)
  exact ⟨e.map_rel_iff.mpr (by decide),e.map_rel_iff.mpr (by decide),
    e.map_rel_iff.mpr (by decide),e.map_rel_iff.mpr (by decide),
    e.map_rel_iff.mpr (by decide),e.map_rel_iff.mpr (by decide)⟩

/-- In the five ordered triangles of this wheel, equality of consecutive
edge colours forces a monochromatic triangle. The palette is arbitrary. -/
theorem wheel_forces_mono {C : Type*} (col : Sym2 (Fin 6) → C)
    (h : ∀ a b c, OrderedTriangle W a b c → col s(a,b) = col s(b,c)) :
    col s(0,2) = col s(0,3) ∧ col s(0,2) = col s(2,3) := by
  have h023 := h 0 2 3 (by decide)
  have h034 := h 0 3 4 (by decide)
  have h134 := h 1 3 4 (by decide)
  have h135 := h 1 3 5 (by decide)
  have h235 := h 2 3 5 (by decide)
  exact ⟨h023.trans (h235.trans (h135.symm.trans (h134.trans h034.symm))),h023⟩

/-- An increasing graph copy whose ordered triangles all have the given colour. -/
def MonoCopy [LinearOrder U] [LinearOrder V]
    (R : SimpleGraph U) (G : SimpleGraph V) (col : V → V → V → Bool) (k : Bool) : Prop :=
  ∃ f : U → V, StrictMono f ∧
    (∀ a b, R.Adj a b → G.Adj (f a) (f b)) ∧
    ∀ a b c, OrderedTriangle R a b c → col (f a) (f b) (f c) = k

/-- This hypothesis concerns only two colours, but its red target can be
infinite. A finite-target Ramsey theorem does not supply it. -/
def TriangleArrow [LinearOrder U] [LinearOrder V]
    (R : SimpleGraph U) (G : SimpleGraph V) : Prop :=
  ∀ col : V → V → V → Bool,
    MonoCopy R G col false ∨ MonoCopy W G col true

lemma monoCopy_triangle [LinearOrder U] [LinearOrder V]
    {R : SimpleGraph U} {G : SimpleGraph V} {f : U → V}
    (hmono : StrictMono f) (hadj : ∀ a b, R.Adj a b → G.Adj (f a) (f b))
    {a b c : U} (h : OrderedTriangle R a b c) :
    OrderedTriangle G (f a) (f b) (f c) :=
  ⟨hmono h.1,hmono h.2.1,hadj _ _ h.2.2.1,hadj _ _ h.2.2.2.1,hadj _ _ h.2.2.2.2⟩

/-- A Ramsey graph for these two targets would be genuinely non-coverable.
No non-coverability premise is hidden in the red-target assumption: the
next theorem supplies red targets that have a two-piece cover. -/
theorem no_cover_of_triangleArrow [LinearOrder U] [LinearOrder V]
    (R : SimpleGraph U) (G : SimpleGraph V)
    (hR : ¬∃ col : Sym2 U → ℕ, MiddleDifferent R col)
    (hG : TriangleArrow R G) :
    ¬Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  intro hcov
  obtain ⟨c,hc⟩ := (Erdos595Work.countable_union_iff_edge_coloring G).mp hcov
  let col : V → V → V → Bool := fun a b d => decide (c s(a,b) = c s(b,d))
  rcases hG col with ⟨f,hf,hfadj,hfm⟩ | ⟨f,hf,hfadj,hfm⟩
  · apply hR
    refine ⟨fun e => c (e.map f),?_⟩
    intro a b d ht he
    have hfalse := hfm a b d ht
    change decide (c s(f a,f b) = c s(f b,f d)) = false at hfalse
    exact (of_decide_eq_false hfalse) he
  · let cW : Sym2 (Fin 6) → ℕ := fun e => c (e.map f)
    have hW : ∀ a b d, OrderedTriangle W a b d → cW s(a,b) = cW s(b,d) := by
      intro a b d ht
      have htrue := hfm a b d ht
      exact of_decide_eq_true htrue
    have hm := wheel_forces_mono cW hW
    exact hc (f 0) (f 2) (f 3) (hfadj _ _ (by decide))
      (hfadj _ _ (by decide)) (hfadj _ _ (by decide)) hm

/-- The required red target exists and is itself countably coverable.
Only the existence of a suitable K4-free Ramsey extension remains missing. -/
theorem exists_red_target :
    ∃ (U : Type) (_ : LinearOrder U) (R : SimpleGraph U),
      R.CliqueFree 4 ∧ Erdos595Work.IsCountableUnionOfTriangleFree R ∧
      ¬∃ col : Sym2 U → ℕ, MiddleDifferent R col := by
  classical
  obtain ⟨A,oA,hA,hcov,hbad⟩ :=
    Erdos595MiddleCorner.no_ordered_middle_coloring ℕ
  letI : LinearOrder A := oA
  letI : LinearOrder (Erdos595MiddleCorner.Triple A) :=
    IsWellOrder.linearOrder WellOrderingRel
  refine ⟨Erdos595MiddleCorner.Triple A, inferInstance,
    Erdos595MiddleCorner.graph A,hA,hcov,?_⟩
  rintro ⟨col,hcol⟩
  apply hbad inferInstance ⟨col,?_⟩
  intro x y z hxy hyz hxy' hxz' hyz'
  exact hcol x y z ⟨hxy,hyz,hxy',hxz',hyz'⟩

#print axioms W_cliqueFree
#print axioms wheel_forces_mono
#print axioms no_cover_of_triangleArrow
#print axioms exists_red_target
end Erdos595TriangleArrow
