import Submission.AllSecondShiftCover
import Submission.ExtensionObstruction

/-!
If deleting a countably properly vertex-colorable set makes a base graph
triangle-free, its biclique right adjoint has a countable triangle-free edge
cover. An independent triangle transversal gives TWO edge pieces. In
particular, one right adjoint of an arbitrary independent-apex extension of
a triangle-free graph is not a witness to Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595RightProperTransversal
open Erdos595ArcAdjoint Erdos595Work
variable {V C : Type*} (H : SimpleGraph V) (S : Set V)

/-- Record colors of old transversal vertices on the incoming side. -/
def code (c : (H.induce S).Coloring C) (p : Biclique H) : Set C :=
  c '' {x : S | x.val ∈ p.val.1}

lemma witness_outside (c : (H.induce S).Coloring C) (p q : Biclique H)
    (he : code H S c p = code H S c q) (x : V)
    (hxB : x ∈ p.val.2) (hxA : x ∈ q.val.1) : x ∉ S := by
  intro hxS
  have hx : c ⟨x,hxS⟩ ∈ code H S c q := ⟨⟨x,hxS⟩,hxA,rfl⟩
  rw [← he] at hx
  obtain ⟨y,hy,heq⟩ := hx
  exact c.valid (v := y) (w := ⟨x,hxS⟩) (p.property y.val hy x hxB) heq

/-- A monochromatic profile triangle would lie entirely outside the
transversal at the three cyclic intersection witnesses. -/
lemma no_triangle (hT : (H.induce Sᶜ).CliqueFree 3)
    (c : (H.induce S).Coloring C) (p q r : Biclique H)
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r) (hqr : (right H).Adj q r)
    (he₁ : code H S c p = code H S c q) (he₂ : code H S c p = code H S c r) : False := by
  classical
  obtain ⟨x,hxP,hxQ⟩ := hpq.1
  obtain ⟨y,hyQ,hyR⟩ := hqr.1
  obtain ⟨z,hzR,hzP⟩ := hpr.2
  have hx := witness_outside H S c p q he₁ x hxP hxQ
  have hy := witness_outside H S c q r (he₁.symm.trans he₂) y hyQ hyR
  have hz := witness_outside H S c r p he₂.symm z hzR hzP
  exact hT _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (H.induce Sᶜ).Adj ⟨x,hx⟩ ⟨y,hy⟩ ∧
      (H.induce Sᶜ).Adj ⟨x,hx⟩ ⟨z,hz⟩ ∧ (H.induce Sᶜ).Adj ⟨y,hy⟩ ⟨z,hz⟩ from
      ⟨q.property x hxQ y hyQ,(p.property z hzP x hxP).symm,r.property y hyR z hzR⟩))

/-- The transversal itself may be arbitrarily large; its proper palette,
not its cardinality, must be countable. -/
theorem countable_cover [Countable C] (hT : (H.induce Sᶜ).CliqueFree 3)
    (c : (H.induce S).Coloring C) : IsCountableUnionOfTriangleFree (right H) := by
  classical
  obtain ⟨e,he⟩ := exists_injective_nat C
  let enc : Set C ↪ (ℕ → Fin 2) :=
    (⟨fun T => e '' T,Set.image_injective.mpr he⟩ : Set C ↪ Set ℕ).trans Erdos595AllSecondShift.bits
  apply countable_union_of_triangle_free_fibers (right H) (fun p => enc (code H S c p))
  intro p q r hpq hpr hqr hh
  exact no_triangle H S hT c p q r hpq hpr hqr
    (enc.injective hh.1) (enc.injective hh.2)

/-- Any Boolean vertex partition with triangle-free fibers gives TWO edge
pieces: the cut and the union of the two internal graphs. -/
theorem two_cover_of_bool {X : Type*} (G : SimpleGraph X) (c : X → Bool)
    (hc : ∀ x y z, G.Adj x y → G.Adj x z → G.Adj y z →
      ¬(c x = c y ∧ c x = c z)) :
    ∃ K L : SimpleGraph X, K.CliqueFree 3 ∧ L.CliqueFree 3 ∧ G = K ⊔ L := by
  classical
  let K := G ⊓ (⊤ : SimpleGraph Bool).comap c
  let L : SimpleGraph X :=
    { Adj x y := G.Adj x y ∧ c x = c y
      symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
      loopless := fun x h => G.loopless x h.1 }
  refine ⟨K,L,?_,?_,?_⟩
  · have hcol : K.Coloring Bool := SimpleGraph.Coloring.mk c (fun h => h.2)
    exact hcol.colorable.cliqueFree (by decide)
  · intro t ht
    obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hc x y z hxy.1 hxz.1 hyz.1 ⟨hxy.2,hxz.2⟩
  · ext x y
    change G.Adj x y ↔ (G.Adj x y ∧ c x ≠ c y) ∨ (G.Adj x y ∧ c x = c y)
    by_cases h : c x = c y <;> simp [h]

/-- An INDEPENDENT triangle transversal yields two pieces even when neither
its cardinality nor the remaining graph's proper chromatic number is bounded. -/
theorem independent_two_cover (hT : (H.induce Sᶜ).CliqueFree 3)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬H.Adj x y) :
    ∃ K L : SimpleGraph (Biclique H), K.CliqueFree 3 ∧ L.CliqueFree 3 ∧ right H = K ⊔ L := by
  classical
  let c : (H.induce S).Coloring (Fin 1) :=
    SimpleGraph.Coloring.mk (fun _ => 0) (fun h _ => hS _ (Subtype.property _) _ (Subtype.property _) h)
  let col : Biclique H → Bool := fun p => decide ((0 : Fin 1) ∈ code H S c p)
  have eq_code (p q : Biclique H) (h : col p = col q) : code H S c p = code H S c q := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact decide_eq_decide.mp h
  apply two_cover_of_bool (right H) col
  intro p q r hpq hpr hqr hh
  exact no_triangle H S hT c p q r hpq hpr hqr (eq_code p q hh.1) (eq_code p r hh.2)

/-- In particular, all independently adjoined apices over a triangle-free
base are excluded at their FIRST biclique right adjoint. -/
theorem apexFamily_two_cover (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    ∃ K L : SimpleGraph (Biclique (Erdos595Extension.apexFamilyGraph G)),
      K.CliqueFree 3 ∧ L.CliqueFree 3 ∧ right (Erdos595Extension.apexFamilyGraph G) = K ⊔ L := by
  classical
  let S : Set (V ⊕ Erdos595Extension.Admissible G) := {x | ∃ a, x = Sum.inr a}
  apply independent_two_cover (Erdos595Extension.apexFamilyGraph G) S
  · intro t ht
    obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    have old (x : {x // x ∉ S}) : ∃ a : V, x.val = Sum.inl a := by
      rcases hx : x.val with a | a
      · exact ⟨a,rfl⟩
      · exact False.elim (x.property ⟨a,hx⟩)
    obtain ⟨a,ha⟩ := old x
    obtain ⟨b,hb⟩ := old y
    obtain ⟨d,hd⟩ := old z
    change (Erdos595Extension.apexFamilyGraph G).Adj x.val y.val at hxy
    change (Erdos595Extension.apexFamilyGraph G).Adj x.val z.val at hxz
    change (Erdos595Extension.apexFamilyGraph G).Adj y.val z.val at hyz
    rw [ha,hb] at hxy
    rw [ha,hd] at hxz
    rw [hb,hd] at hyz
    exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)
  · rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩ h
    exact h

#print axioms countable_cover
#print axioms independent_two_cover
#print axioms apexFamily_two_cover
end Erdos595RightProperTransversal
