import Submission.Work

/-!
A free-corner version of the asymmetric triangle-Ramsey reduction.
Its finite forcing target is a FOUR-wheel, not the odd wheel needed for
ordered middle corners. The missing infinite Ramsey host is an explicit
hypothesis; this file does not settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FreeCorner
open Erdos595Work
universe u

variable {U V C : Type*}

/-- The first vertex is the selected corner; the other two are interchangeable. -/
structure Marking (G : SimpleGraph V) where
  selected : V → V → V → Prop
  adj : ∀ {a b c}, selected a b c → G.Adj a b ∧ G.Adj a c ∧ G.Adj b c
  swap : ∀ {a b c}, selected a b c → selected a c b
  total : ∀ {a b c}, G.Adj a b → G.Adj a c → G.Adj b c →
    selected a b c ∨ selected b a c ∨ selected c a b
  unique : ∀ {a b c}, selected a b c → ¬selected b a c ∧ ¬selected c a b

def Different {G : SimpleGraph V} (M : Marking G) (col : Sym2 V → C) : Prop :=
  ∀ a b c, M.selected a b c → col s(a,b) ≠ col s(a,c)

/-- A cone selects its apex on every triangle. -/
def coneMarking (B : SimpleGraph U) (hB : B.CliqueFree 3) : Marking (coneGraph B) where
  selected a b c := a = none ∧ (coneGraph B).Adj a b ∧
    (coneGraph B).Adj a c ∧ (coneGraph B).Adj b c
  adj h := h.2
  swap h := ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.symm⟩
  total := by
    classical
    intro a b c hab hac hbc
    cases a with
    | none => exact Or.inl ⟨rfl,hab,hac,hbc⟩
    | some a =>
      cases b with
      | none => exact Or.inr (Or.inl ⟨rfl,hab.symm,hbc,hac⟩)
      | some b =>
        cases c with
        | none => exact Or.inr (Or.inr ⟨rfl,hac.symm,hbc.symm,hab⟩)
        | some c =>
          exact (hB _ (SimpleGraph.is3Clique_triple_iff.mpr
            (show B.Adj a b ∧ B.Adj a c ∧ B.Adj b c from ⟨hab,hac,hbc⟩))).elim
  unique := by
    intro a b c h
    constructor
    · intro k
      exact h.2.1.ne (h.1.trans k.1.symm)
    · intro k
      exact h.2.2.1.ne (h.1.trans k.1.symm)

theorem cone_different_gives_coloring (B : SimpleGraph U) (hB : B.CliqueFree 3)
    (col : Sym2 (Option U) → C) (hc : Different (coneMarking B hB) col) :
    Nonempty (B.Coloring C) := by
  refine ⟨SimpleGraph.Coloring.mk (fun a => col s(none,some a)) ?_⟩
  intro a b hab
  exact hc none (some a) (some b) ⟨rfl,trivial,trivial,hab⟩

/-- The red obstruction is already a two-piece edge-coverable graph. -/
theorem exists_red_target (C : Type u) :
    ∃ (U : Type u) (R : SimpleGraph U) (M : Marking R),
      R.CliqueFree 4 ∧ IsCountableUnionOfTriangleFree R ∧
      ¬∃ col : Sym2 U → C, Different M col := by
  obtain ⟨U,B,hB,hχ⟩ := exists_triangleFree_not_colorable C
  refine ⟨Option U,coneGraph B,coneMarking B hB,coneGraph_cliqueFree B hB,
    countable_union_coneGraph B hB,?_⟩
  rintro ⟨col,hcol⟩
  exact hχ.false (cone_different_gives_coloring B hB col hcol).some

/-- Apex 0, rim 1--3--2--4--1. -/
def wheelAdj (a b : Fin 5) : Prop :=
  (a,b) ∈ ([(0,1),(0,2),(0,3),(0,4),(1,3),(1,4),(2,3),(2,4),
    (1,0),(2,0),(3,0),(4,0),(3,1),(4,1),(3,2),(4,2)] : List (Fin 5 × Fin 5))

instance : DecidableRel wheelAdj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ (_ : List _)))

private theorem wheel_symm : ∀ a b, wheelAdj a b → wheelAdj b a := by decide +kernel
private theorem wheel_irrefl : ∀ a, ¬wheelAdj a a := by decide +kernel

def W : SimpleGraph (Fin 5) where
  Adj := wheelAdj
  symm := wheel_symm
  loopless := wheel_irrefl

instance : DecidableRel W.Adj := inferInstanceAs (DecidableRel wheelAdj)

/-- Three triangles select the apex, while (0,2,4) selects 2. -/
def wheelSelected (a b c : Fin 5) : Prop :=
  (a,b,c) ∈ ([(0,1,3),(0,3,1),(0,1,4),(0,4,1),
    (0,2,3),(0,3,2),(2,0,4),(2,4,0)] : List (Fin 5 × Fin 5 × Fin 5))

instance (a b c : Fin 5) : Decidable (wheelSelected a b c) :=
  inferInstanceAs (Decidable (_ ∈ (_ : List _)))

def wheelMarking : Marking W where
  selected := wheelSelected
  adj := by decide +kernel
  swap := by decide +kernel
  total := by decide +kernel
  unique := by decide +kernel

instance (a b c : Fin 5) : Decidable (wheelMarking.selected a b c) :=
  inferInstanceAs (Decidable (wheelSelected a b c))

/-- The finite target is properly three-colorable. -/
def wheelColoring : W.Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (fun v => if v = 0 then 0 else if v ≤ 2 then 1 else 2)
    (by decide +kernel)

theorem wheel_cliqueFree : W.CliqueFree 4 :=
  wheelColoring.colorable.cliqueFree (by decide)

/-- Selected-corner equalities force a monochromatic triangle for ANY palette. -/
theorem wheel_forces_mono (col : Sym2 (Fin 5) → C)
    (h : ∀ a b c, wheelMarking.selected a b c → col s(a,b) = col s(a,c)) :
    col s(0,2) = col s(0,4) ∧ col s(0,2) = col s(2,4) := by
  have h013 := h 0 1 3 (by decide)
  have h014 := h 0 1 4 (by decide)
  have h023 := h 0 2 3 (by decide)
  have h204 := h 2 0 4 (by decide)
  exact ⟨h023.trans (h013.symm.trans h014),by simpa only [Sym2.eq_swap] using h204⟩

/-- An induced graph copy that preserves selected corners and their colors. -/
def MonoCopy {R : SimpleGraph U} {G : SimpleGraph V}
    (M : Marking R) (N : Marking G) (col : V → V → V → Bool) (k : Bool) : Prop :=
  ∃ f : R ↪g G, ∀ a b c, M.selected a b c →
    N.selected (f a) (f b) (f c) ∧ col (f a) (f b) (f c) = k

/-- The infinite red / finite blue Ramsey hypothesis remains unproved. -/
def Arrow {R : SimpleGraph U} {G : SimpleGraph V}
    (M : Marking R) (N : Marking G) : Prop :=
  ∀ col : V → V → V → Bool, (∀ a b c, col a b c = col a c b) →
    MonoCopy M N col false ∨ MonoCopy wheelMarking N col true

theorem no_cover_of_arrow {R : SimpleGraph U} {G : SimpleGraph V}
    (M : Marking R) (N : Marking G)
    (hR : ¬∃ col : Sym2 U → ℕ, Different M col) (hG : Arrow M N) :
    ¬IsCountableUnionOfTriangleFree G := by
  classical
  intro hcov
  obtain ⟨c,hc⟩ := (countable_union_iff_edge_coloring G).mp hcov
  let col : V → V → V → Bool := fun a b d => decide (c s(a,b) = c s(a,d))
  have hswap : ∀ a b d, col a b d = col a d b := by
    intro a b d
    simp only [col,eq_comm]
  rcases hG col hswap with ⟨f,hf⟩ | ⟨f,hf⟩
  · apply hR
    refine ⟨fun e => c (e.map f),?_⟩
    intro a b d ht he
    have hfalse := (hf a b d ht).2
    exact (of_decide_eq_false hfalse) he
  · let cW : Sym2 (Fin 5) → ℕ := fun e => c (e.map f)
    have hW : ∀ a b d, wheelMarking.selected a b d → cW s(a,b) = cW s(a,d) := by
      intro a b d ht
      exact of_decide_eq_true (hf a b d ht).2
    have hm := wheel_forces_mono cW hW
    exact hc (f 0) (f 2) (f 4) (f.map_rel_iff.mpr (by decide))
      (f.map_rel_iff.mpr (by decide)) (f.map_rel_iff.mpr (by decide)) hm

#print axioms exists_red_target
#print axioms wheel_cliqueFree
#print axioms wheel_forces_mono
#print axioms no_cover_of_arrow
end Erdos595FreeCorner
