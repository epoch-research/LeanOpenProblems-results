import Submission.DirectedRightTower
import Submission.BoundedIncreasingPath
import Submission.CountableBadEdgeFilter
import Submission.SecondShiftExponential

/-!
Backtracking labels in the directed second arc graph. A map to a countable
K4-free target gives a countable bipartite edge cover of the source graph.
In particular the mutual graph of TWO DIRECTED right adjoints is covered
when the original countable target is K4-free, without assuming the full
right-adjoint graph is itself K4-free. This does not settle Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595SecondArcBacktracking
open Erdos595DirectedRight Erdos595BoundedPath

variable {V W : Type*}

abbrev Walk₂ (G : SimpleGraph V) := Arc (arc G.Adj)

def walk (G : SimpleGraph V) (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) :
    Walk₂ G := ⟨(⟨(a,b),hab⟩,⟨(b,c),hbc⟩),rfl⟩

lemma walk_step (G : SimpleGraph V) (a b c d : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    arc (arc G.Adj) (walk G a b c hab hbc) (walk G b c d hbc hcd) := rfl

noncomputable def tag (G : SimpleGraph V) (f : Walk₂ G → W) (a b : V) : Option (W × W) := by
  classical
  exact if h : G.Adj a b then
    some (f (walk G a b a h h.symm),f (walk G b a b h.symm h)) else none

/-- Equal ordered backtracking labels on three consecutive edges force a
four-clique in the target. No ordering or distinctness premise is needed. -/
theorem no_three (G : SimpleGraph V) (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (f : Walk₂ G → W)
    (hf : ∀ e d, arc (arc G.Adj) e d → H.Adj (f e) (f d))
    (a b c d : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (h₁ : tag G f a b = tag G f b c) (h₂ : tag G f b c = tag G f c d) : False := by
  classical
  simp only [tag,dif_pos hab,dif_pos hbc,dif_pos hcd,Option.some.injEq] at h₁ h₂
  have hy := congrArg Prod.snd h₁
  have hx := congrArg Prod.fst h₂
  have hxy := hf _ _ (walk_step G b c b c hbc hbc.symm hbc)
  have hxz := (hf _ _ (walk_step G a b c b hab hbc hbc.symm)).symm
  have hyz := hf _ _ (walk_step G b a b c hab.symm hab hbc)
  have hxt := (hf _ _ (walk_step G b c d c hbc hcd hcd.symm)).symm
  have hyt := hf _ _ (walk_step G c b c d hbc.symm hbc hcd)
  have hzt := hf _ _ (walk_step G a b c d hab hbc hcd)
  dsimp only at hy hx
  rw [hy] at hyz
  rw [← hx] at hxt
  exact Erdos595Work.no_adj_common_neighbors hH hxy hxz hyz hxt hyt hzt

/-- Each directed label class has a finite height. -/
theorem heights (G : SimpleGraph V) (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (f : Walk₂ G → W)
    (hf : ∀ e d, arc (arc G.Adj) e d → H.Adj (f e) (f d)) :
    ∃ h : Option (W × W) → V → Fin 4,
      ∀ a b, G.Adj a b → h (tag G f a b) a < h (tag G f a b) b := by
  classical
  let R : Option (W × W) → V → V → Prop := fun k a b =>
    G.Adj a b ∧ tag G f a b = k
  have hn (k : Option (W × W)) (a d : V) : ¬Chain (R k) 3 a d := by
    intro hc
    obtain ⟨c,hac,hcd⟩ := hc.split_last
    obtain ⟨b,hab,hbc⟩ := hac.split_last
    obtain ⟨a',ha',hab⟩ := hab.split_last
    cases ha'
    exact no_three G H hH f hf a b c d hab.1 hbc.1 hcd.1
      (hab.2.trans hbc.2.symm) (hbc.2.trans hcd.2.symm)
  choose h hh using fun k => finite_rank (R k) 3 (hn k)
  exact ⟨h,fun a b hab => hh _ a b ⟨hab,rfl⟩⟩

/-- In fact the source has a proper vertex coloring by sequences in a
fixed finite palette, hence by a palette of cardinality continuum. -/
theorem coloring_sequences [Countable W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (f : Walk₂ G → W)
    (hf : ∀ e d, arc (arc G.Adj) e d → H.Adj (f e) (f d)) :
    Nonempty (G.Coloring (ℕ → Fin 4)) := by
  classical
  obtain ⟨h,hh⟩ := heights G H hH f hf
  obtain ⟨s,hs⟩ := exists_surjective_nat (Option (W × W))
  refine ⟨SimpleGraph.Coloring.mk (fun v n => h (s n) v) ?_⟩
  intro a b hab he
  obtain ⟨n,hn⟩ := hs (tag G f a b)
  have he' := congrFun he n
  change h (s n) a = h (s n) b at he'
  rw [hn] at he'
  exact (hh a b hab).ne he'

/-- The entire source has a countable bipartite edge cover. In particular,
K4-freeness of the SOURCE is not an assumption. -/
theorem countable_cover [Countable W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (f : Walk₂ G → W)
    (hf : ∀ e d, arc (arc G.Adj) e d → H.Adj (f e) (f d)) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨h,hh⟩ := heights G H hH f hf
  let C := Option (W × W) × Fin 4
  let K : C → SimpleGraph V := fun p =>
    G ⊓ (⊤ : SimpleGraph Bool).comap (fun v => decide (h p.1 v = p.2))
  apply Erdos595CountableBadEdge.cover_of_countable_family G K
  · intro p
    have hc : (K p).Colorable 2 :=
      (SimpleGraph.Coloring.mk (G := K p) (fun v => decide (h p.1 v = p.2))
        (fun hab => hab.2)).colorable
    exact hc.cliqueFree (by decide)
  · intro a b hab
    refine ⟨(tag G f a b,h (tag G f a b) a),hab,?_⟩
    change decide (h (tag G f a b) a = h (tag G f a b) a) ≠
      decide (h (tag G f a b) b = h (tag G f a b) a)
    have hn : h (tag G f a b) b ≠ h (tag G f a b) a := (hh a b hab).ne.symm
    simp [hn]

/-- Directed uncurrying chooses a witness in the required intersection. -/
noncomputable def uncurry {S : V → V → Prop} {R : W → W → Prop}
    (p : V → Biclique R) (hp : ∀ a b, S a b → right R (p a) (p b)) : Arc S → W :=
  fun e => (hp e.val.1 e.val.2 e.property).choose

lemma uncurry_rel {S : V → V → Prop} {R : W → W → Prop}
    (p : V → Biclique R) (hp : ∀ a b, S a b → right R (p a) (p b))
    (e d : Arc S) (hed : arc S e d) : R (uncurry p hp e) (uncurry p hp d) := by
  have he := (hp e.val.1 e.val.2 e.property).choose_spec
  have hd := (hp d.val.1 d.val.2 d.property).choose_spec
  have he' : uncurry p hp e ∈ (p d.val.1).val.1 := by
    change e.val.2 = d.val.1 at hed
    simpa only [uncurry,hed] using he.2
  exact (p d.val.1).property _ he' _ hd.1

/-- Uncurrying twice provides the labels used by the preceding theorem. -/
noncomputable def twiceLabel (H : SimpleGraph W) : Walk₂ (twice H) → W :=
  uncurry (uncurry id (fun _ _ h => h.1))
    (uncurry_rel id (fun _ _ h => h.1))

lemma twiceLabel_rel (H : SimpleGraph W) (e d : Walk₂ (twice H))
    (hed : arc (arc (twice H).Adj) e d) : H.Adj (twiceLabel H e) (twiceLabel H d) :=
  uncurry_rel _ _ e d hed

/-- A countable K4-free original target suffices, even though its full
second directed right-adjoint graph can contain K4. -/
theorem twice_countable_cover [Countable W] (H : SimpleGraph W) (hH : H.CliqueFree 4) :
    Erdos595Work.IsCountableUnionOfTriangleFree (twice H) :=
  countable_cover (twice H) H hH (twiceLabel H) (twiceLabel_rel H)

/-- This removes the triangle-free target restriction from the EDGE-cover
conclusion for cofinally repeated second-shift profiles. -/
theorem secondShift_cover_of_cofinal {A : Type*} [LinearOrder A] [Nonempty A]
    [Countable W] (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (hB : IsEmpty ((Erdos595MiddleCorner.oneGraph A).Coloring ℕ))
    (hA : Erdos595SecondShiftExponential.CofinalRepeats A (Biclique (right H.Adj))) :
    Erdos595Work.IsCountableUnionOfTriangleFree
      (Erdos595SecondShiftExponential.F H hB) :=
  Erdos595Work.countable_union_of_hom
    (Erdos595SecondShiftExponential.profileHom H hB hA) (twice_countable_cover H hH)

/-- All canonical second-shift exponentials with countable K4-free targets
are countably coverable, without increasing the canonical domain size. -/
theorem canonical_secondShift_cover {W : Type} [Countable W]
    (H : SimpleGraph W) (hH : H.CliqueFree 4) :
    Erdos595Work.IsCountableUnionOfTriangleFree
      (Erdos595SecondShiftExponential.F H
        (Erdos595SecondShiftExponential.canonical_not_colorable H)) :=
  secondShift_cover_of_cofinal H hH
    (Erdos595SecondShiftExponential.canonical_not_colorable H)
    (Erdos595SecondShiftExponential.canonical_cofinal H)

#print axioms no_three
#print axioms coloring_sequences
#print axioms countable_cover
#print axioms twice_countable_cover
#print axioms canonical_secondShift_cover
end Erdos595SecondArcBacktracking
