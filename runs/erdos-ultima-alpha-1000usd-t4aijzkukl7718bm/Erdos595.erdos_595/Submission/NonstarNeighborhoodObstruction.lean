import Submission.SecondArcNonstarReduction

/-!
The exact second-arc nonstar targets do not have uniformly small proper
neighborhood palettes. This holds even for targets already known to be
countably triangle-free edge-covered. It is not a settlement of Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595NonstarNeighborhoodObstruction
open Erdos595Work Erdos595ArcAdjoint Erdos595MatchingBundle
open Erdos595SecondArcNonstarReduction

variable {V : Type*} (H : SimpleGraph V)

/-- Two distinct neighbors make both sides of the canonical unit biclique
nonsingletons. -/
lemma unit_nonstar {v a b : V} (ha : H.Adj v a) (hb : H.Adj v b) (hab : a ≠ b) :
    ¬Star (arcGraph H) (unit H v) := by
  let ea : Arc H := ⟨(a,v),ha.symm⟩
  let eb : Arc H := ⟨(b,v),hb.symm⟩
  let fa : Arc H := ⟨(v,a),ha⟩
  let fb : Arc H := ⟨(v,b),hb⟩
  have hea : ea ∈ Left (arcGraph H) (unit H v) := ⟨ea,rfl,rfl⟩
  have heb : eb ∈ Left (arcGraph H) (unit H v) := ⟨eb,rfl,rfl⟩
  have hfa : fa ∈ Right (arcGraph H) (unit H v) := ⟨fa,rfl,rfl⟩
  have hfb : fb ∈ Right (arcGraph H) (unit H v) := ⟨fb,rfl,rfl⟩
  rintro (⟨x,hx⟩ | ⟨x,hx⟩)
  · rw [hx] at hea heb
    have he : ea = eb := hea.trans heb.symm
    exact hab (congrArg (fun e : Arc H => e.val.1) he)
  · rw [hx] at hfa hfb
    have he : fa = fb := hfa.trans hfb.symm
    exact hab (congrArg (fun e : Arc H => e.val.2) he)

variable (G : SimpleGraph V)

/-- Under this degree condition the ordinary first unit lands in the
nonstar core, without using any edge coloring. -/
def arcUnitNonstar
    (h : ∀ e : Arc G, ∃ a b : Arc G,
      (arcGraph G).Adj e a ∧ (arcGraph G).Adj e b ∧ a ≠ b) :
    arcGraph G →g core G where
  toFun e := ⟨unit (arcGraph G) e,by
    obtain ⟨a,b,ha,hb,hab⟩ := h e
    exact unit_nonstar (arcGraph G) ha hb hab⟩
  map_rel' := fun h => (unit (arcGraph G)).map_adj h

def reducedUnit
    (h : ∀ e : Arc G, ∃ a b : Arc G,
      (arcGraph G).Adj e a ∧ (arcGraph G).Adj e b ∧ a ≠ b) :
    G →g target G := toRight (arcUnitNonstar G h)

/-- A cone on at least two vertices meets the degree condition on its arc
graph, including arcs incident with isolated vertices of the base. -/
lemma cone_arc_neighbors [Nontrivial V] (e : Arc (coneGraph H)) :
    ∃ a b : Arc (coneGraph H),
      (arcGraph (coneGraph H)).Adj e a ∧
      (arcGraph (coneGraph H)).Adj e b ∧ a ≠ b := by
  rcases e with ⟨⟨u,v⟩,huv⟩
  cases u with
  | none =>
    cases v with
    | none => exact huv.elim
    | some v =>
      obtain ⟨w,hw⟩ := exists_ne v
      refine ⟨⟨(some v,none),trivial⟩,⟨(some w,none),trivial⟩,
        Or.inr rfl,Or.inr rfl,?_⟩
      intro he
      exact hw (Option.some.inj (congrArg (fun e : Arc (coneGraph H) => e.val.1) he)).symm
  | some u =>
    cases v with
    | none =>
      obtain ⟨w,hw⟩ := exists_ne u
      refine ⟨⟨(none,some u),trivial⟩,⟨(none,some w),trivial⟩,
        Or.inl rfl,Or.inl rfl,?_⟩
      intro he
      exact hw (Option.some.inj (congrArg (fun e : Arc (coneGraph H) => e.val.2) he)).symm
    | some v =>
      refine ⟨⟨(some v,some u),huv.symm⟩,⟨(none,some u),trivial⟩,
        Or.inr rfl,Or.inr rfl,?_⟩
      intro he
      exact Option.some_ne_none v (congrArg (fun e : Arc (coneGraph H) => e.val.1) he)

/-- A large neighborhood of the cone survives in its nonstar target. -/
def coneUnit [Nontrivial V] : coneGraph H →g target (coneGraph H) :=
  reducedUnit (coneGraph H) (cone_arc_neighbors H)

def neighborhoodHom [Nontrivial V] :
    H →g (target (coneGraph H)).induce
      ((target (coneGraph H)).neighborSet (coneUnit H none)) where
  toFun v := ⟨coneUnit H (some v),(coneUnit H).map_adj (show (coneGraph H).Adj none (some v) from trivial)⟩
  map_rel' := fun h => (coneUnit H).map_adj h

universe u
/-- The desired local compression is false for every prescribed nonempty
palette, even within the covered K4-free nonstar targets. -/
theorem arbitrarily_large_neighborhoods (C : Type u) [Nonempty C] :
    ∃ (V : Type u) (H : SimpleGraph V) (p : _),
      (target (coneGraph H)).CliqueFree 4 ∧
      IsCountableUnionOfTriangleFree (target (coneGraph H)) ∧
      IsEmpty (((target (coneGraph H)).induce
        ((target (coneGraph H)).neighborSet p)).Coloring C) := by
  classical
  obtain ⟨V,H,hH,hχ⟩ := exists_triangleFree_not_colorable C
  have hedge : ∃ a b, H.Adj a b := by
    by_contra hn
    push_neg at hn
    exact hχ.false (SimpleGraph.Coloring.mk (fun _ => Classical.arbitrary C)
      (fun {a b} h => (hn a b h).elim))
  obtain ⟨a,b,hab⟩ := hedge
  letI : Nontrivial V := ⟨⟨a,b,hab.ne⟩⟩
  refine ⟨V,H,coneUnit H none,
    Erdos595SecondArcNonstarReduction.cliqueFree (coneGraph H) (coneGraph_cliqueFree H hH),
    (cover_iff (coneGraph H)).mp (countable_union_coneGraph H hH),?_⟩
  exact ⟨fun c => hχ.false (c.comp (neighborhoodHom H))⟩

#print axioms unit_nonstar
#print axioms reducedUnit
#print axioms cone_arc_neighbors
#print axioms arbitrarily_large_neighborhoods
end Erdos595NonstarNeighborhoodObstruction
