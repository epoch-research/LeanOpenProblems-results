import Submission.FiniteAdaptedExtension

/-!
A profile-omission lemma for an independent family of cone points.
This is a local color constraint, NOT a proof of Erdős 595: the graph in
this file has a two-piece triangle-free edge cover.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595ConeProfileOmission
open Erdos595Work

variable {R B C : Type*}

/-- An independent set of roots, each joined to the whole base. -/
def graph (H : SimpleGraph B) : SimpleGraph (R ⊕ B) where
  Adj
    | .inl _, .inl _ => False
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr a, .inr b => H.Adj a b
  symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · trivial
    · trivial
    · exact h.symm
  loopless := by
    intro a h
    cases a
    · exact h
    · exact H.loopless _ h

def Valid (G : SimpleGraph (R ⊕ B)) (c : Sym2 (R ⊕ B) → C) : Prop :=
  ∀ a b d, G.Adj a b → G.Adj a d → G.Adj b d →
    ¬(c s(a,b) = c s(a,d) ∧ c s(a,b) = c s(b,d))

/-- The profile remembers the actual color at every root, not just its range. -/
def profile (c : Sym2 (R ⊕ B) → C) (b : B) : R → C :=
  fun r => c s(Sum.inl r, Sum.inr b)

/-- Equal profiles along a base edge omit that edge's color. -/
theorem edge_color_omitted (H : SimpleGraph B) (c : Sym2 (R ⊕ B) → C)
    (hc : Valid (graph H) c) {a b : B} (hab : H.Adj a b)
    (hp : profile c a = profile c b) :
    c s(Sum.inr a,Sum.inr b) ∉ Set.range (profile c a) := by
  rintro ⟨r,hr⟩
  exact hc (Sum.inl r) (Sum.inr a) (Sum.inr b) trivial trivial hab
    ⟨congrFun hp r,hr⟩

/-- If the base cannot be properly colored by profiles, one such omission
is forced by every valid edge coloring. The palette C is arbitrary. -/
theorem exists_omission (H : SimpleGraph B)
    (hH : IsEmpty (H.Coloring (R → C))) (c : Sym2 (R ⊕ B) → C)
    (hc : Valid (graph H) c) :
    ∃ a b : B, H.Adj a b ∧ profile c a = profile c b ∧
      c s(Sum.inr a,Sum.inr b) ∉ Set.range (profile c a) := by
  classical
  have hex : ∃ a b : B, H.Adj a b ∧ profile c a = profile c b := by
    by_contra hn
    push_neg at hn
    exact hH.false (SimpleGraph.Coloring.mk (profile c) (fun h => hn _ _ h))
  obtain ⟨a,b,hab,hp⟩ := hex
  exact ⟨a,b,hab,hp,edge_color_omitted H c hc hab hp⟩

/-- The graph is nevertheless covered by two triangle-free pieces whenever
the base is triangle-free. This explicitly prevents confusing the local
omission with a palette-exhaustion argument. -/
theorem two_cover (H : SimpleGraph B) (hH : H.CliqueFree 3) :
    ∃ K L : SimpleGraph (R ⊕ B), K.CliqueFree 3 ∧ L.CliqueFree 3 ∧
      graph H = K ⊔ L := by
  classical
  let K : SimpleGraph (R ⊕ B) :=
    { Adj a b := (graph H).Adj a b ∧ a.isLeft ≠ b.isLeft
      symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
      loopless := fun _ h => h.2 rfl }
  let L : SimpleGraph (R ⊕ B) :=
    { Adj a b := (graph H).Adj a b ∧ a.isLeft = b.isLeft
      symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
      loopless := fun _ h => (graph H).loopless _ h.1 }
  have hK : K.CliqueFree 3 :=
    (SimpleGraph.Coloring.mk (G := K) Sum.isLeft (fun h => h.2)).colorable.cliqueFree
      (by decide)
  have hL : L.CliqueFree 3 := by
    intro s hs
    obtain ⟨a,b,d,hab,had,hbd,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    cases a with
    | inl a =>
      cases b with
      | inl b => exact hab.1
      | inr b => exact (by decide : true ≠ false) hab.2
    | inr a =>
      cases b with
      | inl b => exact Bool.false_ne_true hab.2
      | inr b =>
        cases d with
        | inl d => exact Bool.false_ne_true had.2
        | inr d =>
          exact hH _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab.1,had.1,hbd.1⟩)
  refine ⟨K,L,hK,hL,?_⟩
  ext a b
  change (graph H).Adj a b ↔
    ((graph H).Adj a b ∧ a.isLeft ≠ b.isLeft) ∨
      ((graph H).Adj a b ∧ a.isLeft = b.isLeft)
  by_cases h : a.isLeft = b.isLeft <;> simp [h]

/-- Collapsing the independent root family to one cone point preserves
adjacency; hence no K4 is introduced over a triangle-free base. -/
def toCone (H : SimpleGraph B) : (graph H : SimpleGraph (R ⊕ B)) →g coneGraph H where
  toFun := Sum.elim (fun _ => none) some
  map_rel' := by
    intro a b h
    cases a <;> cases b <;> exact h

theorem cliqueFree (H : SimpleGraph B) (hH : H.CliqueFree 3) :
    (graph H : SimpleGraph (R ⊕ B)).CliqueFree 4 := by
  classical
  have hC := coneGraph_cliqueFree H hH
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  let f := (toCone H).comp e.toHom
  exact no_adj_common_neighbors hC
    (f.map_adj (show (0 : Fin 4) ≠ 1 by decide))
    (f.map_adj (show (0 : Fin 4) ≠ 2 by decide))
    (f.map_adj (show (1 : Fin 4) ≠ 2 by decide))
    (f.map_adj (show (0 : Fin 4) ≠ 3 by decide))
    (f.map_adj (show (1 : Fin 4) ≠ 3 by decide))
    (f.map_adj (show (2 : Fin 4) ≠ 3 by decide))

#print axioms exists_omission
#print axioms two_cover
#print axioms cliqueFree

/-- In particular it is impossible for every base vertex to have a
surjective spoke profile. This does not say that the whole coloring omits
any color. -/
theorem not_all_profiles_surjective (H : SimpleGraph B)
    (hH : IsEmpty (H.Coloring (R → C))) (c : Sym2 (R ⊕ B) → C)
    (hc : Valid (graph H) c) :
    ¬∀ b : B, Function.Surjective (profile c b) := by
  intro hs
  obtain ⟨a,b,_,_,hm⟩ := exists_omission H hH c hc
  exact hm (hs a _)

universe u

/-- Bases with the required profile-chromatic obstruction do exist, for
any root set and any palette. Their cone-family graphs are nevertheless
K4-free AND two-piece coverable. -/
theorem exists_base (R C : Type u) :
    ∃ (B : Type u) (H : SimpleGraph B),
      H.CliqueFree 3 ∧ IsEmpty (H.Coloring (R → C)) ∧
      (graph H : SimpleGraph (R ⊕ B)).CliqueFree 4 ∧
      (∃ K L : SimpleGraph (R ⊕ B), K.CliqueFree 3 ∧ L.CliqueFree 3 ∧
        graph H = K ⊔ L) ∧
      (∀ c : Sym2 (R ⊕ B) → C, Valid (graph H) c →
        ∃ a b : B, H.Adj a b ∧ profile c a = profile c b ∧
          c s(Sum.inr a,Sum.inr b) ∉ Set.range (profile c a)) := by
  obtain ⟨B,H,hH,hχ⟩ := exists_triangleFree_not_colorable (R → C)
  exact ⟨B,H,hH,hχ,cliqueFree H hH,two_cover H hH,
    fun c hc => exists_omission H hχ c hc⟩

#print axioms not_all_profiles_surjective
#print axioms exists_base

end Erdos595ConeProfileOmission
