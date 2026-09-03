import Submission.InfiniteShiftRamsey
import Submission.FiniteBipartiteInfinitePalette

/-!
The incidence graph of all pairs of an arbitrary well-ordered set embeds
inducedly in a shift graph. Consequently it has a triangle-free induced
edge-Ramsey host for every palette. The host is NOT claimed bipartite, and
this does not give compatible choices at infinitely many amalgamation stages.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595IncidenceShiftRamsey
open Erdos595Work Erdos595InfiniteShiftRamsey
open Erdos595InfiniteBipartite (Double low high)
universe u
variable {A B : Type u} [LinearOrder A] [LinearOrder B]

abbrev IncVertex (A : Type u) [LinearOrder A] := A ⊕ Pair A

def incidence (A : Type u) [LinearOrder A] : SimpleGraph (IncVertex A) :=
  Erdos595FiniteBipartiteInfinitePalette.graph (fun a p => a = p.val.1 ∨ a = p.val.2)

lemma high_low_iff (a b : A) : high a < low b ↔ a < b := by
  rw [Prod.Lex.lt_iff]
  change (a < b ∨ a = b ∧ (1 : Fin 2) < 0) ↔ a < b
  simp

omit [LinearOrder A] in
lemma low_eq_low (a b : A) : low a = low b ↔ a = b := by
  constructor
  · exact fun h => congrArg (fun x : Double A => (ofLex x).1) h
  · exact congrArg low

omit [LinearOrder A] in
lemma high_eq_high (a b : A) : high a = high b ↔ a = b := by
  constructor
  · exact fun h => congrArg (fun x : Double A => (ofLex x).1) h
  · exact congrArg high

omit [LinearOrder A] in
lemma low_ne_high (a b : A) : low a ≠ high b := by
  intro h
  have hh := congrArg (fun x : Double A => (ofLex x).2) h
  exact (by decide : (0 : Fin 2) ≠ 1) hh

omit [LinearOrder A] in
lemma high_ne_low (a b : A) : high a ≠ low b := Ne.symm (low_ne_high b a)

def originalArc (a : A) : Pair (Double A) :=
  ⟨(low a,high a), (Erdos595InfiniteBipartite.low_high_iff a a).mpr le_rfl⟩

def pairArc (p : Pair A) : Pair (Double A) :=
  ⟨(high p.val.1,low p.val.2),(high_low_iff _ _).mpr p.property⟩

def map : IncVertex A → Pair (Double A) := Sum.elim originalArc pairArc

lemma map_injective : Function.Injective (map (A := A)) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact congrArg Sum.inl ((low_eq_low a b).mp (congrArg (fun p => p.val.1) h))
    | inr p =>
      exact (low_ne_high a p.val.1 (congrArg (fun p => p.val.1) h)).elim
  | inr p =>
    cases y with
    | inl a =>
      exact (high_ne_low p.val.1 a (congrArg (fun p => p.val.1) h)).elim
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext ((high_eq_high _ _).mp (congrArg (fun p => p.val.1) h))
        ((low_eq_low _ _).mp (congrArg (fun p => p.val.2) h))

lemma map_adj (x y : IncVertex A) :
    (orderedShiftGraph (Double A)).Adj (map x) (map y) ↔ (incidence A).Adj x y := by
  cases x <;> cases y <;>
    simp only [map,Sum.elim_inl,Sum.elim_inr,originalArc,pairArc,orderedShiftGraph,
      incidence,Erdos595FiniteBipartiteInfinitePalette.graph,high_eq_high,low_eq_low,
      low_ne_high,high_ne_low,false_or]
  all_goals simp only [eq_comm,or_comm]

def incidenceEmbedding (A : Type u) [LinearOrder A] :
    incidence A ↪g orderedShiftGraph (Double A) where
  toFun := map
  inj' := map_injective
  map_rel_iff' := map_adj _ _

def incidenceColoring (A : Type u) [LinearOrder A] : (incidence A).Coloring ℕ :=
  SimpleGraph.Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) (by
    intro a b hab
    cases a <;> cases b <;>
      simp_all [incidence,Erdos595FiniteBipartiteInfinitePalette.graph])

/-- This is a Ramsey host for the WHOLE incidence graph, not only each finite
subgraph separately. The host is triangle-free but may be non-bipartite. -/
theorem ramsey (A C : Type u) [LinearOrder A] [WellFoundedLT A] [Nonempty C] :
    ∃ (V : Type u) (K : SimpleGraph V), K.CliqueFree 3 ∧
      ∀ c : Sym2 V → C, ∃ (e : incidence A ↪g K) (k : C),
        ∀ a b, (incidence A).Adj a b → c s(e a,e b) = k :=
  Erdos595InfiniteShiftRamsey.ramsey_of_embedding (Double A) C
    (incidence A) (incidenceEmbedding A)

/-- The target includes the subdivision of the complete graph of any
cardinality; no finiteness or countability restriction on that target. -/
theorem step (A C : Type u) [LinearOrder A] [WellFoundedLT A] [Nonempty C]
    {V : Type u} (H : SimpleGraph V) (hH : H.CliqueFree 4) (D : Set V)
    (f : incidence A ≃g H.induce D) :
    ∃ (W : Type u) (G : SimpleGraph W), G.CliqueFree 4 ∧
      ∀ c : Sym2 W → C, ∃ (e : H ↪g G) (k : C),
        ∀ a b : D, H.Adj a.val b.val → c s(e a.val,e b.val) = k := by
  obtain ⟨W,K,hK,hRam⟩ := ramsey A C
  exact Erdos595InfiniteBipartite.step_of_ramsey (incidence A) K
    (hK.mono (by decide)) hRam H hH D f

#print axioms incidenceEmbedding
#print axioms ramsey
#print axioms step
end Erdos595IncidenceShiftRamsey
