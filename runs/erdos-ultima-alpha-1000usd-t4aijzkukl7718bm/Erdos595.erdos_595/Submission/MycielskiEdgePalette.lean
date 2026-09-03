import Submission.MycielskiMargin

/-!
The ordinary Mycielski operation preserves every nonempty triangle-free edge
palette, including finite palettes. This is an exclusion of an amplification
method, not a settlement of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595MycielskiEdgePalette
open Erdos595MycielskiMargin (Vertex graph)

variable {V C : Type*}

def Valid (G : SimpleGraph V) (c : Sym2 V → C) : Prop :=
  ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
    ¬(c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d))

def old (v : V) : Vertex V := some (v,false)

def oldEmbedding (G : SimpleGraph V) : G ↪g graph G where
  toFun := old
  inj' := by intro a b h; simpa only [old,Option.some.injEq,Prod.mk.injEq,and_true] using h
  map_rel_iff' := by intro a b; simp [old,graph]

def extendPair (c : Sym2 V → C) (z : C) : Vertex V → Vertex V → C
  | some a, some b => c s(a.1,b.1)
  | _, _ => z

lemma extendPair_symm (c : Sym2 V → C) (z : C) (a b : Vertex V) :
    extendPair c z a b = extendPair c z b a := by
  cases a <;> cases b <;> simp [extendPair,Sym2.eq_swap]

def extend (c : Sym2 V → C) (z : C) : Sym2 (Vertex V) → C :=
  Sym2.lift ⟨extendPair c z,extendPair_symm c z⟩

@[simp] lemma extend_old (c : Sym2 V → C) (z : C) (a b : V) :
    extend c z s(old a,old b) = c s(a,b) := rfl

lemma triangle_no_apex (G : SimpleGraph V) (a b : Vertex V)
    (ha : (graph G).Adj none a) (hb : (graph G).Adj none b)
    (hab : (graph G).Adj a b) : False := by
  cases a with
  | none => exact ha
  | some a =>
    cases b with
    | none => exact hb
    | some b =>
      change a.2 = true at ha
      change b.2 = true at hb
      change G.Adj a.1 b.1 ∧ (a.2 = false ∨ b.2 = false) at hab
      rcases hab.2 with h | h
      · exact Bool.noConfusion (ha.symm.trans h)
      · exact Bool.noConfusion (hb.symm.trans h)

/-- No color is added, and the old coloring is preserved literally. -/
theorem extend_valid (G : SimpleGraph V) (c : Sym2 V → C) (z : C)
    (hc : Valid G c) : Valid (graph G) (extend c z) := by
  intro a b d hab had hbd hm
  cases a with
  | none => exact triangle_no_apex G b d hab had hbd
  | some a =>
    cases b with
    | none => exact triangle_no_apex G (some a) d hab.symm hbd had
    | some b =>
      cases d with
      | none => exact triangle_no_apex G (some a) (some b) had.symm hbd.symm hab
      | some d => exact hc a.1 b.1 d.1 hab.1 had.1 hbd.1 hm

/-- The statement is valid for arbitrary nonempty palettes, not just finite ones. -/
theorem palette_iff [Nonempty C] (G : SimpleGraph V) :
    (∃ c : Sym2 (Vertex V) → C, Valid (graph G) c) ↔
      ∃ c : Sym2 V → C, Valid G c := by
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨fun e => c (e.map old),?_⟩
    intro a b d hab had hbd hm
    exact hc (old a) (old b) (old d)
      ((oldEmbedding G).map_rel_iff.mpr hab)
      ((oldEmbedding G).map_rel_iff.mpr had)
      ((oldEmbedding G).map_rel_iff.mpr hbd) hm
  · rintro ⟨c,hc⟩
    exact ⟨extend c (Classical.arbitrary C),extend_valid G c _ hc⟩

theorem countable_cover_iff (G : SimpleGraph V) :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph G) ↔
      Erdos595Work.IsCountableUnionOfTriangleFree G := by
  rw [Erdos595Work.countable_union_iff_edge_coloring,
    Erdos595Work.countable_union_iff_edge_coloring]
  exact palette_iff (C := ℕ) G

#print axioms extend_valid
#print axioms palette_iff
#print axioms countable_cover_iff
end Erdos595MycielskiEdgePalette
