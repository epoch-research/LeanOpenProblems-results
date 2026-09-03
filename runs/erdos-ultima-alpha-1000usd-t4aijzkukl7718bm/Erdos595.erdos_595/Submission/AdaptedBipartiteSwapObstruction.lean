import Submission.AdaptedLimitObstruction
import Submission.CountableCodegreeColoring

/-!
An adapted-labeling obstruction with bipartite color classes, and an obstruction
to assembling cone copies by exchanging their apices along labeled triangles.
These results test a proposed construction; they do not settle Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595AdaptedBipartiteSwap
open Erdos595Work Erdos595FiniteAdapted
open Erdos595AdaptedLimit (X d d_symm d_spec)

variable {V W : Type*}

def graph (B : SimpleGraph V) : SimpleGraph (V × X) where
  Adj a b := B.Adj a.1 b.1 ∧ a.2 ≠ b.2
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.2 rfl

noncomputable def color : Sym2 (V × X) → ℕ :=
  Sym2.lift ⟨fun a b => d a.2 b.2,fun _ _ => d_symm _ _⟩

def piece (B : SimpleGraph V) (n : ℕ) : SimpleGraph (V × X) where
  Adj a b := (graph B).Adj a b ∧ color s(a,b) = n
  symm := fun _ _ h => ⟨h.1.symm,by simpa only [color,Sym2.lift_mk,d_symm] using h.2⟩
  loopless := fun a h => (graph B).loopless a h.1

lemma graph_triangleFree (B : SimpleGraph V) (hB : B.CliqueFree 3) :
    (graph B).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab.1,hac.1,hbc.1⟩)

def properColoring (B : SimpleGraph V) : (graph B).Coloring X :=
  SimpleGraph.Coloring.mk Prod.snd (fun h => h.2)

noncomputable def pieceColoring (B : SimpleGraph V) (n : ℕ) :
    (piece B n).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun a => a.2 n) (by
    intro a b hab he
    have hh := d_spec hab.1.2
    have hc : d a.2 b.2 = n := hab.2
    exact hh (hc ▸ he))

lemma no_adapted (B : SimpleGraph V) (hB : IsEmpty (B.Coloring (X → ℕ))) :
    ¬∃ f : V × X → ℕ, Adapted (graph B) color f := by
  rintro ⟨f,hf⟩
  apply hB.false
  refine SimpleGraph.Coloring.mk (fun v (x : X) => f (v,x)) ?_
  intro v w hvw he
  obtain ⟨x,y,hxy,hx,hy⟩ := firstDifference_no_adapted (fun x => f (v,x))
  apply hf (v,x) (w,y) ⟨hvw,hxy⟩
  exact ⟨hx,(congrFun he y).symm.trans hy⟩

/-- Even the canonical first-difference coloring of a triangle-free graph
with a proper continuum-sized vertex coloring need not admit an adapted labeling.
Every single edge-color class has a two-color proper vertex coloring. -/
theorem exists_bipartite_pieces_no_adapted :
    ∃ (V : Type) (G : SimpleGraph V) (c : Sym2 V → ℕ),
      G.CliqueFree 3 ∧ Nonempty (G.Coloring X) ∧
      (∀ n, ∃ f : V → Fin 2, ∀ a b, G.Adj a b → c s(a,b) = n → f a ≠ f b) ∧
      ¬∃ f : V → ℕ, Adapted G c f := by
  classical
  obtain ⟨V,B,hB,hχ⟩ := exists_triangleFree_not_colorable (X → ℕ)
  refine ⟨V × X,graph B,color,graph_triangleFree B hB,⟨properColoring B⟩,?_,no_adapted B hχ⟩
  intro n
  exact ⟨pieceColoring B n,fun _ _ h hc => (pieceColoring B n).valid ⟨h,hc⟩⟩

/-- Two triangle copies are identified with their first two vertices exchanged. -/
def SwapOn (f g : V → W) (a b c : V) : Prop :=
  f a = g b ∧ f b = g a ∧ f c = g c

/-- A four-cycle of two overlapping apex swaps identifies adjacent vertices.
Thus this diagram cannot be realized even in an arbitrary simple graph. -/
theorem square_swap_impossible (R : SimpleGraph V) (H : SimpleGraph W)
    (f : Fin 4 → R →g H) {a b c d : V} (hab : R.Adj a b)
    (h01 : SwapOn (f 0) (f 1) a b c)
    (h12 : SwapOn (f 1) (f 2) a c d)
    (h23 : SwapOn (f 2) (f 3) a b c)
    (h30 : SwapOn (f 3) (f 0) a c d) : False := by
  have he : f 0 b = f 0 a :=
    h01.2.1.trans (h12.1.trans (h23.2.2.trans h30.2.1))
  exact ((f 0).map_adj hab).ne he.symm

private def bits (a b : Fin 2) : X := fun n => if n = 0 then a else if n = 1 then b else 0

private lemma d_bits_zero (a b c e : Fin 2) (h : a ≠ c) :
    d (bits a b) (bits c e) = 0 := by
  classical
  have hne : bits a b ≠ bits c e := fun he => h (by simpa [bits] using congrFun he 0)
  have hex : ∃ n, bits a b n ≠ bits c e n := Function.ne_iff.mp hne
  rw [Erdos595AdaptedLimit.d_find hne hex]
  apply (Nat.find_eq_iff hex).mpr
  exact ⟨by simpa [bits] using h,by intro n hn; omega⟩

private lemma d_bits_one (a b c : Fin 2) (h : b ≠ c) :
    d (bits a b) (bits a c) = 1 := by
  classical
  have hne : bits a b ≠ bits a c := fun he => h (by simpa [bits] using congrFun he 1)
  have hex : ∃ n, bits a b n ≠ bits a c n := Function.ne_iff.mp hne
  rw [Erdos595AdaptedLimit.d_find hne hex]
  apply (Nat.find_eq_iff hex).mpr
  refine ⟨by simpa [bits] using h,?_⟩
  intro n hn
  have he : n = 0 := by omega
  subst n
  simp [bits]

/-- Every square in the base gives the dangerous alternating pair of labels
in the first-difference index graph. -/
theorem alternating_square (B : SimpleGraph V) (v : Fin 4 → V)
    (h01 : B.Adj (v 0) (v 1)) (h12 : B.Adj (v 1) (v 2))
    (h23 : B.Adj (v 2) (v 3)) (h30 : B.Adj (v 3) (v 0)) :
    ∃ w : Fin 4 → V × X,
      (graph B).Adj (w 0) (w 1) ∧ (graph B).Adj (w 1) (w 2) ∧
      (graph B).Adj (w 2) (w 3) ∧ (graph B).Adj (w 3) (w 0) ∧
      color s(w 0,w 1) = 0 ∧ color s(w 1,w 2) = 1 ∧
      color s(w 2,w 3) = 0 ∧ color s(w 3,w 0) = 1 := by
  let w : Fin 4 → V × X := ![(v 0,bits 0 0),(v 1,bits 1 0),
    (v 2,bits 1 1),(v 3,bits 0 1)]
  have hne0 (a b c e : Fin 2) (h : a ≠ c) : bits a b ≠ bits c e :=
    fun he => h (by simpa [bits] using congrFun he 0)
  have hne1 (a b c : Fin 2) (h : b ≠ c) : bits a b ≠ bits a c :=
    fun he => h (by simpa [bits] using congrFun he 1)
  refine ⟨w,⟨h01,hne0 _ _ _ _ (by decide)⟩,⟨h12,hne1 _ _ _ (by decide)⟩,
    ⟨h23,hne0 _ _ _ _ (by decide)⟩,⟨h30,hne1 _ _ _ (by decide)⟩,?_,?_,?_,?_⟩
  · exact d_bits_zero _ _ _ _ (by decide)
  · exact d_bits_one _ _ _ (by decide)
  · exact d_bits_zero _ _ _ _ (by decide)
  · exact d_bits_one _ _ _ (by decide)

/-- Uncountable chromatic number precludes escaping the square obstruction
by choosing a base with no four-cycles. -/
theorem square_of_no_countable_coloring (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) :
    ∃ v : Fin 4 → V, B.Adj (v 0) (v 1) ∧ B.Adj (v 1) (v 2) ∧
      B.Adj (v 2) (v 3) ∧ B.Adj (v 3) (v 0) ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 3 := by
  classical
  by_contra hn
  have hc : ∀ a b, a ≠ b → (B.commonNeighbors a b).Countable := by
    intro a b hab
    have hs : (B.commonNeighbors a b).Subsingleton := by
      intro x hx y hy
      by_contra hxy
      apply hn
      exact ⟨![a,x,b,y],hx.1,hx.2.symm,hy.2,hy.1.symm,hab,hxy⟩
    exact hs.countable
  exact hB.false (Erdos595CountableCodegree.coloring_nat_of_countable_common_neighbors B hc).some

/-- The first-difference index construction cannot support these simultaneous
triangle identifications. This fails before one even asks the target to be K4-free. -/
theorem no_simultaneous_swap_realization (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) {A : Type*} (R : SimpleGraph A)
    (H : SimpleGraph W) {a b c e : A} (hab : R.Adj a b)
    (f : V × X → R →g H)
    (hzero : ∀ u v, (graph B).Adj u v → color s(u,v) = 0 →
      SwapOn (f u) (f v) a b c)
    (hone : ∀ u v, (graph B).Adj u v → color s(u,v) = 1 →
      SwapOn (f u) (f v) a c e) : False := by
  obtain ⟨v,h01,h12,h23,h30,_,_⟩ := square_of_no_countable_coloring B hB
  obtain ⟨w,hw01,hw12,hw23,hw30,hc01,hc12,hc23,hc30⟩ :=
    alternating_square B v h01 h12 h23 h30
  exact square_swap_impossible R H (fun i => f (w i)) hab
    (hzero _ _ hw01 hc01) (hone _ _ hw12 hc12)
    (hzero _ _ hw23 hc23) (hone _ _ hw30 hc30)

#print axioms exists_bipartite_pieces_no_adapted
#print axioms square_swap_impossible
#print axioms alternating_square
#print axioms square_of_no_countable_coloring
#print axioms no_simultaneous_swap_realization
end Erdos595AdaptedBipartiteSwap
