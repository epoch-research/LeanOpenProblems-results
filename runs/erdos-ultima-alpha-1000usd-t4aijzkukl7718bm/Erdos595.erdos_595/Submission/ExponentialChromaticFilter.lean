import Submission.ExponentialCandidate
import Submission.LocalChromaticProduct
import Submission.TriangleComponentProduct

/-!
The filter dual to countably vertex-colorable subsets of the domain turns
an exponential into a subgraph of a countably complete reduced power.
This is a transfer theorem and a restriction on candidates, not a settlement
of Erdős 595. No countably complete ultrafilter is asserted to exist.
-/

open SimpleGraph Set Filter
namespace Erdos595ExponentialChromaticFilter
open Erdos595Exponential

variable {V W : Type*}

def generators (B : SimpleGraph V) : Set (Set V) :=
  {S | ∀ a ∉ S, ∀ b ∉ S, ¬B.Adj a b}

def chromaticFilter (B : SimpleGraph V) : Filter V :=
  Filter.countableGenerate (generators B)

instance (B : SimpleGraph V) : CountableInterFilter (chromaticFilter B) :=
  inferInstanceAs (CountableInterFilter (Filter.countableGenerate _))

/-- A set with a proper countable labeling is negligible for this filter. -/
theorem avoids_labeled {C : Type*} [Countable C] (B : SimpleGraph V)
    (S : Set V) (c : V → C)
    (hc : ∀ a ∈ S, ∀ b ∈ S, B.Adj a b → c a ≠ c b) :
    ∀ᶠ v in chromaticFilter B, v ∉ S := by
  have h (k : C) : ∀ᶠ v in chromaticFilter B, ¬(v ∈ S ∧ c v = k) := by
    apply Filter.CountableGenerateSets.basic
    intro a ha b hb hab
    have ha' : a ∈ S ∧ c a = k := not_not.mp ha
    have hb' : b ∈ S ∧ c b = k := not_not.mp hb
    exact hc a ha'.1 b hb'.1 hab (ha'.2.trans hb'.2.symm)
  exact (eventually_countable_forall.mpr h).mono (fun v hv hs => hv (c v) ⟨hs,rfl⟩)

theorem avoids_colorable (B : SimpleGraph V) (S : Set V)
    (hS : Nonempty ((B.induce S).Coloring ℕ)) :
    ∀ᶠ v in chromaticFilter B, v ∉ S := by
  classical
  obtain ⟨c⟩ := hS
  let d : V → ℕ := fun v => if hv : v ∈ S then c ⟨v,hv⟩ else 0
  apply avoids_labeled B S d
  intro a ha b hb hab
  simpa only [d,dif_pos ha,dif_pos hb] using
    c.valid (show (B.induce S).Adj ⟨a,ha⟩ ⟨b,hb⟩ from hab)

/-- The filter is exactly the dual of the countable vertex-chromatic ideal. -/
theorem mem_iff (B : SimpleGraph V) (S : Set V) :
    S ∈ chromaticFilter B ↔ Nonempty ((B.induce Sᶜ).Coloring ℕ) := by
  classical
  constructor
  · intro hS
    obtain ⟨T,hT,hTc,hsub⟩ := Filter.mem_countableGenerate_iff.mp hS
    letI : Countable T := hTc.to_subtype
    obtain ⟨enc,henc⟩ := exists_injective_nat T
    have hex : ∀ v : (Sᶜ : Set V), ∃ t : T, v.val ∉ t.val := by
      intro v
      by_contra hn
      push_neg at hn
      exact v.property (hsub (Set.mem_sInter.mpr (fun t ht => hn ⟨t,ht⟩)))
    choose t ht using hex
    refine ⟨SimpleGraph.Coloring.mk (fun v => enc (t v)) ?_⟩
    intro a b hab he
    have he' : t a = t b := henc he
    exact hT (t a).property a.val (ht a) b.val (he' ▸ ht b) hab
  · intro hS
    simpa only [Set.notMem_compl_iff] using avoids_colorable B Sᶜ hS

/-- Properness uses uncountable domain chromatic number, not an ultrafilter
extension or a saturation assertion about external colorings. -/
theorem filter_neBot (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ)) :
    (chromaticFilter B).NeBot := by
  constructor
  intro he
  have hm : (∅ : Set V) ∈ chromaticFilter B := by rw [he]; simp
  obtain ⟨c⟩ := (mem_iff B ∅).mp hm
  apply hB.false
  exact c.comp ⟨fun v => ⟨v,by simp⟩,fun h => h⟩

/-- Exponential adjacency can fail pointwise only on a countably
vertex-colorable subset of the domain. -/
theorem eventually_adj [Countable W] (H : SimpleGraph W) (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (f g : V → W)
    (hfg : (exponential H B hB).Adj f g) :
    ∀ᶠ x in chromaticFilter B, H.Adj (f x) (g x) := by
  have he := avoids_labeled B {x | ¬H.Adj (f x) (g x)}
    (fun x => (f x,g x)) (by
      intro a ha b _ hab hp
      have hg : g a = g b := congrArg Prod.snd hp
      exact ha (by simpa only [← hg] using hfg a b hab))
  exact he.mono (fun _ h => not_not.mp h)

/-- The underlying map is the identity on functions. It is a homomorphism,
not an induced embedding: the converse adjacency implication is not asserted. -/
def toPower [Countable W] (H : SimpleGraph W) (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) :
    letI := filter_neBot B hB
    exponential H B hB →g
      Erdos595CompleteFilterProduct.graph (chromaticFilter B) (fun _ => H) := by
  letI := filter_neBot B hB
  exact ⟨id,fun h => eventually_adj H B hB _ _ h⟩

/-- Local finite VERTEX-chromatic bounds on the target suffice for EVERY
uncountably vertex-chromatic domain. The target need not have a finite
triangle-free edge palette. No clique hypothesis is used. -/
theorem cover_of_finite_neighborhood_colorings [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (hH : ∀ w, ∃ n, (H.induce (H.neighborSet w)).Colorable n) :
    Erdos595Work.IsCountableUnionOfTriangleFree (exponential H B hB) := by
  letI := filter_neBot B hB
  exact Erdos595Work.countable_union_of_hom (toPower H B hB)
    (Erdos595LocalChromaticProduct.countable_cover (chromaticFilter B)
      (fun _ => H) (fun _ => hH))

theorem locally_finite_target [Countable W] (H : SimpleGraph W) [H.LocallyFinite]
    (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ)) :
    Erdos595Work.IsCountableUnionOfTriangleFree (exponential H B hB) := by
  apply cover_of_finite_neighborhood_colorings H B hB
  intro w
  exact ⟨Fintype.card (H.neighborSet w),SimpleGraph.colorable_of_fintype _⟩

/-- The finite-per-triangle-component product criterion also transfers.
These are components under triangles sharing edges, not graph components. -/
theorem cover_of_finite_triangle_components [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (hH : ∀ q : Erdos595TriangleComponentProduct.Component H,
      Erdos595BadEdge.FiniteCover (Erdos595TriangleComponentProduct.piece H q)) :
    Erdos595Work.IsCountableUnionOfTriangleFree (exponential H B hB) := by
  letI := filter_neBot B hB
  exact Erdos595Work.countable_union_of_hom (toPower H B hB)
    (Erdos595TriangleComponentProduct.countable_cover (chromaticFilter B)
      (fun _ => H) (fun _ => hH))

#print axioms mem_iff
#print axioms filter_neBot
#print axioms toPower
#print axioms cover_of_finite_neighborhood_colorings
#print axioms locally_finite_target
#print axioms cover_of_finite_triangle_components
end Erdos595ExponentialChromaticFilter
