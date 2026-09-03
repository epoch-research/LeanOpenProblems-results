import Submission.AdaptedLimitObstruction

/-!
Failure of adapted labeling need not reflect to a triangle-free induced
subgraph, even for a valid natural-number edge coloring of a K4-free graph.
The example is a cone over a triangle-free graph and has a two-piece edge
cover. It is NOT a counterexample to the covering conjecture.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595AdaptedReflection
open Erdos595Work Erdos595FiniteAdapted
open Erdos595AdaptedLimit (X zero d d_symm d_spec)

abbrev Y := {x : X // x ≠ zero}

variable {B : Type*} (R : SimpleGraph B)

def base : SimpleGraph (B × Y) where
  Adj a b := R.Adj a.1 b.1 ∧ a.2.val ≠ b.2.val
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.2 rfl

lemma base_triangleFree (hR : R.CliqueFree 3) : (base R).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,t,hab,hat,hbt,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact hR _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab.1,hat.1,hbt.1⟩)

abbrev graph := coneGraph (base R)

def code : Option (B × Y) → X
  | none => zero
  | some a => a.2.val

noncomputable def color : Sym2 (Option (B × Y)) → ℕ :=
  Sym2.lift ⟨fun a b => d (code a) (code b),fun _ _ => d_symm _ _⟩

lemma code_ne_of_adj {a b : Option (B × Y)} (h : (graph R).Adj a b) : code a ≠ code b := by
  cases a with
  | none =>
    cases b with
    | none => exact h.elim
    | some b => exact b.2.property.symm
  | some a =>
    cases b with
    | none => exact a.2.property
    | some b => exact h.2

lemma color_valid : Valid (graph R) color := by
  intro a b t hab hat hbt he
  have h₁ := d_spec (code_ne_of_adj R hab)
  have h₂ := d_spec (code_ne_of_adj R hat)
  have h₃ := d_spec (code_ne_of_adj R hbt)
  change d (code a) (code b) = d (code a) (code t) ∧
    d (code a) (code b) = d (code b) (code t) at he
  rw [← he.1] at h₂
  rw [← he.2] at h₃
  have h₁' : (code a (d (code a) (code b))).val ≠ (code b (d (code a) (code b))).val :=
    fun h => h₁ (Fin.ext h)
  have h₂' : (code a (d (code a) (code b))).val ≠ (code t (d (code a) (code b))).val :=
    fun h => h₂ (Fin.ext h)
  have h₃' : (code b (d (code a) (code b))).val ≠ (code t (d (code a) (code b))).val :=
    fun h => h₃ (Fin.ext h)
  have ha := (code a (d (code a) (code b))).isLt
  have hb := (code b (d (code a) (code b))).isLt
  have ht := (code t (d (code a) (code b))).isLt
  omega

noncomputable def profile (f : Option (B × Y) → ℕ) (v : B) (x : X) : ℕ := by
  classical
  exact if h : x = zero then f none else f (some (v,⟨x,h⟩))

lemma profile_separates (f : Option (B × Y) → ℕ) (hf : Adapted (graph R) color f)
    {v w : B} (hvw : R.Adj v w) : profile f v ≠ profile f w := by
  classical
  intro he
  obtain ⟨x,y,hxy,hx,hy⟩ := firstDifference_no_adapted (profile f v)
  change profile f v x = d x y at hx
  change profile f v y = d x y at hy
  by_cases hx0 : x = zero
  · subst x
    have hy0 : y ≠ zero := hxy.symm
    simp only [profile,dif_neg hy0] at hx hy
    apply hf none (some (v,⟨y,hy0⟩)) trivial
    exact ⟨hx,hy⟩
  by_cases hy0 : y = zero
  · subst y
    simp only [profile,dif_neg hx0] at hx hy
    apply hf (some (v,⟨x,hx0⟩)) none trivial
    exact ⟨hx,hy⟩
  have hw : profile f w y = d x y := (congrFun he y).symm.trans hy
  simp only [profile,dif_neg hx0,dif_neg hy0] at hx hw
  apply hf (some (v,⟨x,hx0⟩)) (some (w,⟨y,hy0⟩)) ⟨hvw,hxy⟩
  exact ⟨hx,hw⟩

theorem no_adapted (hR : IsEmpty (R.Coloring (X → ℕ))) :
    ¬∃ f : Option (B × Y) → ℕ, Adapted (graph R) color f := by
  rintro ⟨f,hf⟩
  exact hR.false (SimpleGraph.Coloring.mk (profile f) (fun h => profile_separates R f hf h))

/-- The apex-star coloring already adapts to every subset that omits the apex. -/
lemma adapted_without_apex (S : Set (Option (B × Y))) (hS : none ∉ S) :
    ∃ f : S → ℕ, Adapted ((graph R).induce S) (fun e => color (e.map Subtype.val)) f := by
  refine ⟨fun v => color s(none,v.val),?_⟩
  intro a b hab he
  have ha : (graph R).Adj none a.val := by
    cases h : a.val with
    | none => exact (hS (h ▸ a.property)).elim
    | some a => trivial
  have hb : (graph R).Adj none b.val := by
    cases h : b.val with
    | none => exact (hS (h ▸ b.property)).elim
    | some b => trivial
  apply color_valid R none a.val b.val ha hb hab
  exact ⟨he.1.trans he.2.symm,he.1⟩

/-- With the apex present, a triangle-free induced subgraph is bipartite. -/
lemma adapted_with_apex (S : Set (Option (B × Y))) (hp : none ∈ S)
    (hS : ((graph R).induce S).CliqueFree 3) :
    ∃ f : S → ℕ, Adapted ((graph R).induce S) (fun e => color (e.map Subtype.val)) f := by
  classical
  let f : S → ℕ := fun v => if v.val = none then 0 else 1
  have hf : ∀ a b : S, ((graph R).induce S).Adj a b → f a ≠ f b := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ hab
    cases a with
    | none =>
      cases b with
      | none => exact hab.elim
      | some b => simp only [f,if_pos rfl,Option.some_ne_none,if_false]; omega
    | some a =>
      cases b with
      | none => simp only [f,if_pos rfl,Option.some_ne_none,if_false]; omega
      | some b =>
        apply False.elim
        apply hS _
        exact SimpleGraph.is3Clique_triple_iff.mpr
          (show ((graph R).induce S).Adj ⟨none,hp⟩ ⟨some a,ha⟩ ∧
            ((graph R).induce S).Adj ⟨none,hp⟩ ⟨some b,hb⟩ ∧
            ((graph R).induce S).Adj ⟨some a,ha⟩ ⟨some b,hb⟩ from
              ⟨trivial,trivial,hab⟩)
  exact ⟨f,fun a b hab he => hf a b hab (he.1.trans he.2.symm)⟩

theorem every_triangleFree_adapted (S : Set (Option (B × Y)))
    (hS : ((graph R).induce S).CliqueFree 3) :
    ∃ f : S → ℕ, Adapted ((graph R).induce S) (fun e => color (e.map Subtype.val)) f := by
  classical
  by_cases hp : none ∈ S
  · exact adapted_with_apex R S hp hS
  · exact adapted_without_apex R S hp

/-- The local-to-global assertion fails with the actual countable palette. -/
theorem exists_reflection_failure :
    ∃ (V : Type) (G : SimpleGraph V) (c : Sym2 V → ℕ),
      G.CliqueFree 4 ∧ IsCountableUnionOfTriangleFree G ∧ Valid G c ∧
      (∀ S : Set V, (G.induce S).CliqueFree 3 →
        ∃ f : S → ℕ, Adapted (G.induce S) (fun e => c (e.map Subtype.val)) f) ∧
      ¬∃ f : V → ℕ, Adapted G c f := by
  obtain ⟨B,R,hR,hχ⟩ := exists_triangleFree_not_colorable (X → ℕ)
  exact ⟨_,graph R,color,coneGraph_cliqueFree _ (base_triangleFree R hR),
    countable_union_coneGraph _ (base_triangleFree R hR),color_valid R,
    every_triangleFree_adapted R,no_adapted R hχ⟩

#print axioms exists_reflection_failure
end Erdos595AdaptedReflection
