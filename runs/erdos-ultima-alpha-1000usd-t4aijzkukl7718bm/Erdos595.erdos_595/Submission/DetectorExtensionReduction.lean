import Submission.CommonNeighborDetector
import Submission.ExtensionObstruction

/-!
Countable common-neighbor detectors do not by themselves simplify the first
mutual-ultrafilter covering question. A countably colored K4-free graph has
an extension with a countable detector for ALL pairs; this uses three families
of new vertices, not a transfinite iteration. Applying this to levelGraph
recovers arbitrary K4-free graphs in the first ultrafilter extension.
This is a reduction, not a settlement of Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595DetectorExtension
open Erdos595Work Erdos595Extension

variable {V : Type*} (H : SimpleGraph V) (c : H.Coloring ℕ)

private lemma pair_triangleFree (n m : ℕ) :
    (H.induce {v | c v = n ∨ c v = m}).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,d,hab,had,hbd,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  have h₁ := c.valid hab
  have h₂ := c.valid had
  have h₃ := c.valid hbd
  rcases a.property with ha | ha <;>
    rcases b.property with hb | hb <;>
    rcases d.property with hd | hd <;> simp_all

private def pairAdmissible (p : ℕ × ℕ) : Admissible H :=
  ⟨{v | c v = p.1 ∨ c v = p.2},pair_triangleFree H c p.1 p.2⟩

abbrev V₁ := V ⊕ (ℕ × ℕ)

def G₁ : SimpleGraph (V₁ (V := V)) :=
  (apexFamilyGraph H).comap (Sum.map id (pairAdmissible H c))

private lemma family_cliqueFree {A I : Type*} (K : SimpleGraph A)
    (hK : K.CliqueFree 4) (a : I → Admissible K) :
    ((apexFamilyGraph K).comap (Sum.map id a)).CliqueFree 4 := by
  classical
  have hh := apexFamilyGraph_cliqueFree K hK
  by_contra hn
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he : ∀ i j : Fin 4, i ≠ j →
      (apexFamilyGraph K).Adj (Sum.map id a (f i)) (Sum.map id a (f j)) :=
    fun i j h => f.map_rel_iff.mpr h
  exact no_adj_common_neighbors hh (he 0 1 (by decide)) (he 0 2 (by decide))
    (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

lemma G₁_cliqueFree (hH : H.CliqueFree 4) : (G₁ H c).CliqueFree 4 :=
  family_cliqueFree H hH (pairAdmissible H c)

private def singleSet (n : ℕ) : Set (V₁ (V := V)) :=
  {x | match x with | .inl v => c v = n | .inr _ => True}

private lemma singleSet_triangleFree (n : ℕ) :
    ((G₁ H c).induce (singleSet H c n)).CliqueFree 3 := by
  let f : singleSet H c n → Fin 2 := fun x => match x.val with
    | .inl _ => 0 | .inr _ => 1
  have hf : ((G₁ H c).induce (singleSet H c n)).Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk f (by
      rintro ⟨a,ha⟩ ⟨b,hb⟩ hab he
      cases a with
      | inl a =>
        cases b with
        | inl b => exact c.valid hab (ha.trans hb.symm)
        | inr b => exact (by decide : (0 : Fin 2) ≠ 1) he
      | inr a =>
        cases b with
        | inl b => exact (by decide : (1 : Fin 2) ≠ 0) he
        | inr b => exact hab)
  exact hf.colorable.cliqueFree (by decide)

private def singleAdmissible (n : ℕ) : Admissible (G₁ H c) :=
  ⟨singleSet H c n,singleSet_triangleFree H c n⟩

abbrev V₂ := (V₁ (V := V)) ⊕ ℕ

def G₂ : SimpleGraph (V₂ (V := V)) :=
  (apexFamilyGraph (G₁ H c)).comap (Sum.map id (singleAdmissible H c))

lemma G₂_cliqueFree (hH : H.CliqueFree 4) : (G₂ H c).CliqueFree 4 :=
  family_cliqueFree (G₁ H c) (G₁_cliqueFree H c hH) (singleAdmissible H c)

private def lastSet : Set (V₂ (V := V)) :=
  {x | match x with | .inl (.inl _) => False | _ => True}

private lemma lastSet_triangleFree :
    ((G₂ H c).induce (lastSet (V := V))).CliqueFree 3 := by
  let f : lastSet (V := V) → Fin 2 := fun x => match x.val with
    | .inl _ => 0 | .inr _ => 1
  have hf : ((G₂ H c).induce (lastSet (V := V))).Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk f (by
      rintro ⟨a,ha⟩ ⟨b,hb⟩ hab he
      cases a with
      | inl a =>
        cases a with
        | inl a => exact ha.elim
        | inr a =>
          cases b with
          | inl b =>
            cases b with
            | inl b => exact hb.elim
            | inr b => exact hab
          | inr b => exact (by decide : (0 : Fin 2) ≠ 1) he
      | inr a =>
        cases b with
        | inl b => exact (by decide : (1 : Fin 2) ≠ 0) he
        | inr b => exact hab)
  exact hf.colorable.cliqueFree (by decide)

private def lastAdmissible (_ : Unit) : Admissible (G₂ H c) :=
  ⟨lastSet,lastSet_triangleFree H c⟩

abbrev Vertex := (V₂ (V := V)) ⊕ Unit

def completed : SimpleGraph (Vertex (V := V)) :=
  (apexFamilyGraph (G₂ H c)).comap (Sum.map id (lastAdmissible H c))

theorem completed_cliqueFree (hH : H.CliqueFree 4) : (completed H c).CliqueFree 4 :=
  family_cliqueFree (G₂ H c) (G₂_cliqueFree H c hH) (lastAdmissible H c)

def old (v : V) : Vertex (V := V) := .inl (.inl (.inl v))
def pair (n m : ℕ) : Vertex (V := V) := .inl (.inl (.inr (n,m)))
def single (n : ℕ) : Vertex (V := V) := .inl (.inr n)
def top : Vertex (V := V) := .inr ()

def oldEmbedding : H ↪g completed H c where
  toFun := old
  inj' := fun _ _ h => Sum.inl_injective (Sum.inl_injective (Sum.inl_injective h))
  map_rel_iff' := Iff.rfl

abbrev New := ((ℕ × ℕ) ⊕ ℕ) ⊕ Unit

def newVertex : New → Vertex (V := V)
  | .inl (.inl (n,m)) => pair n m
  | .inl (.inr n) => single n
  | .inr _ => top

private lemma old_pair (v : V) (n m : ℕ) (hv : c v = n ∨ c v = m) :
    (completed H c).Adj (old v) (pair n m) := hv
private lemma old_single (v : V) :
    (completed H c).Adj (old v) (single (c v)) := rfl
private lemma pair_single (n m k : ℕ) :
    (completed H c).Adj (pair n m) (single k) := trivial
private lemma pair_top (n m : ℕ) :
    (completed H c).Adj (pair n m) top := trivial
private lemma single_top (n : ℕ) :
    (completed H c).Adj (single n) top := trivial

/-- New vertices already contain a common neighbor of ANY two vertices,
including equal vertices. The detector does not depend on existing adjacency. -/
theorem new_common_neighbor (a b : Vertex (V := V)) :
    ∃ d : New, (completed H c).Adj a (newVertex d) ∧
      (completed H c).Adj b (newVertex d) := by
  have hop (v : V) (n m : ℕ) (hv : c v = n ∨ c v = m) := old_pair H c v n m hv
  have hos := old_single H c
  have hps := pair_single H c
  have hpt := pair_top H c
  have hst := single_top H c
  rcases a with ((a | ⟨n,m⟩) | k) | ⟨⟩ <;>
    rcases b with ((b | ⟨n',m'⟩) | k') | ⟨⟩
  · exact ⟨.inl (.inl (c a,c b)),hop a _ _ (Or.inl rfl),hop b _ _ (Or.inr rfl)⟩
  · exact ⟨.inl (.inr (c a)),hos a,hps n' m' (c a)⟩
  · exact ⟨.inl (.inl (c a,c a)),hop a _ _ (Or.inl rfl),(hps _ _ k').symm⟩
  · exact ⟨.inl (.inl (c a,c a)),hop a _ _ (Or.inl rfl),(hpt _ _).symm⟩
  · exact ⟨.inl (.inr (c b)),hps n m (c b),hos b⟩
  · exact ⟨.inr (),hpt n m,hpt n' m'⟩
  · exact ⟨.inr (),hpt n m,hst k'⟩
  · exact ⟨.inl (.inr 0),hps n m 0,(hst 0).symm⟩
  · exact ⟨.inl (.inl (c b,c b)),(hps _ _ k).symm,hop b _ _ (Or.inl rfl)⟩
  · exact ⟨.inr (),hst k,hpt n' m'⟩
  · exact ⟨.inr (),hst k,hst k'⟩
  · exact ⟨.inl (.inl (0,0)),(hps 0 0 k).symm,(hpt 0 0).symm⟩
  · exact ⟨.inl (.inl (c b,c b)),(hpt _ _).symm,hop b _ _ (Or.inl rfl)⟩
  · exact ⟨.inl (.inr 0),(hst 0).symm,hps n' m' 0⟩
  · exact ⟨.inl (.inl (0,0)),(hpt 0 0).symm,(hps 0 0 k').symm⟩
  · exact ⟨.inl (.inl (0,0)),(hpt 0 0).symm,(hpt 0 0).symm⟩

theorem universal_detector :
    ∃ d : ℕ → Vertex (V := V), ∀ a b,
      ∃ n, (completed H c).Adj a (d n) ∧ (completed H c).Adj b (d n) := by
  obtain ⟨e,he⟩ := exists_surjective_nat New
  refine ⟨fun n => newVertex (e n),?_⟩
  intro a b
  obtain ⟨d,hd⟩ := new_common_neighbor H c a b
  obtain ⟨n,rfl⟩ := he d
  exact ⟨n,hd⟩

theorem completed_countable_coloring (hH : H.CliqueFree 4) :
    Nonempty ((completed H c).Coloring ℕ) := by
  obtain ⟨d,hd⟩ := universal_detector H c
  exact Erdos595CommonNeighborDetector.countable_coloring _ d
    (completed_cliqueFree H c hH) (fun a b _ => hd a b)

#print axioms completed_cliqueFree
#print axioms universal_detector
#print axioms completed_countable_coloring

/-- A countable family supplies a common neighbor for every pair, even if
that pair had no common neighbor in a previously given subgraph. -/
def HasUniversalDetector {A : Type*} (K : SimpleGraph A) : Prop :=
  ∃ d : ℕ → A, ∀ a b, ∃ n, K.Adj a (d n) ∧ K.Adj b (d n)

universe u
variable {A : Type u}

def detectorBase (G : SimpleGraph A) : SimpleGraph (Vertex (V := A × ℕ)) :=
  completed (levelGraph G) (levelGraph_coloring G)

theorem detectorBase_cliqueFree (G : SimpleGraph A) (hG : G.CliqueFree 4) :
    (detectorBase G).CliqueFree 4 :=
  completed_cliqueFree _ _ (levelGraph_cliqueFree G hG)

theorem detectorBase_detector (G : SimpleGraph A) : HasUniversalDetector (detectorBase G) :=
  universal_detector _ _

theorem detectorBase_coloring (G : SimpleGraph A) (hG : G.CliqueFree 4) :
    Nonempty ((detectorBase G).Coloring ℕ) :=
  completed_countable_coloring _ _ (levelGraph_cliqueFree G hG)

/-- Arbitrary K4-free graphs map into first extensions of bases with the
strong countable detector property. The base vertex TYPE need not be countable. -/
noncomputable def intoFirst (G : SimpleGraph A) (hG : G.CliqueFree 4) :
    G →g ultrafilterGraph (detectorBase G) (detectorBase_cliqueFree G hG) :=
  (ultrafilterGraphHom (levelGraph_cliqueFree G hG) (detectorBase_cliqueFree G hG)
    (oldEmbedding (levelGraph G) (levelGraph_coloring G)).toHom).comp
    (fiberUltrafilterHom G hG)

/-- Proving the first-ultrafilter covering theorem from a countable universal
detector would already prove coverability for EVERY K4-free graph. -/
theorem all_cover_iff_detector_ultrafilter_cover :
    (∀ (A : Type u) (G : SimpleGraph A), G.CliqueFree 4 → IsCountableUnionOfTriangleFree G) ↔
    (∀ (A : Type u) (G : SimpleGraph A) (hG : G.CliqueFree 4),
      HasUniversalDetector G → IsCountableUnionOfTriangleFree (ultrafilterGraph G hG)) := by
  constructor
  · intro h A G hG _
    exact h _ _ (ultrafilterGraph_cliqueFree G hG)
  · intro h A G hG
    exact countable_union_of_hom (intoFirst G hG)
      (h _ _ (detectorBase_cliqueFree G hG) (detectorBase_detector G))

/-- In contrast with the unresolved edge-cover question, proper vertex
colorability definitely is not preserved, even with the strongest detector. -/
theorem no_vertex_palette_preservation (C : Type u) :
    ∃ (A : Type u) (K : SimpleGraph A) (hK : K.CliqueFree 4),
      Nonempty (K.Coloring ℕ) ∧ HasUniversalDetector K ∧
        IsEmpty ((ultrafilterGraph K hK).Coloring C) := by
  obtain ⟨A,G,hG,hχ⟩ := exists_triangleFree_not_colorable C
  have hG₄ : G.CliqueFree 4 := hG.mono (by decide)
  refine ⟨_,detectorBase G,detectorBase_cliqueFree G hG₄,
    detectorBase_coloring G hG₄,detectorBase_detector G,⟨?_⟩⟩
  intro c
  exact hχ.false (c.comp (intoFirst G hG₄))

#print axioms intoFirst
#print axioms all_cover_iff_detector_ultrafilter_cover
#print axioms no_vertex_palette_preservation
end Erdos595DetectorExtension

