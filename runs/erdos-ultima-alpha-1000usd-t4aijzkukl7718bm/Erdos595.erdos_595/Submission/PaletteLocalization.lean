import Submission.PrescribedCountableProperExtension

/-!
A countable old graph with infinitely many edges can be made to use EVERY
natural-number color inside any covered supergraph, without changing a valid
prescribed bijective coloring of its edges. Thus palette-exhaustion or
fresh-color arguments alone do not produce an obstruction. This does not
settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595PaletteLocalization
open Erdos595Work Erdos595FiniteAdapted

variable {V W : Type*}

/-- A countably infinite edge set admits a valid coloring using every natural
number exactly once on actual edges. Values on nonedges are irrelevant. -/
theorem bijective_edge_coloring (H : SimpleGraph V) [Countable H.edgeSet]
    (hH : H.edgeSet.Infinite) :
    ∃ c : Sym2 V → ℕ, Valid H c ∧ Function.Bijective (fun e : H.edgeSet => c e.val) := by
  classical
  haveI : Infinite H.edgeSet := hH.to_subtype
  let e : H.edgeSet ≃ ℕ := Classical.choice (inferInstance : Nonempty (H.edgeSet ≃ ℕ))
  let c : Sym2 V → ℕ := fun a => if ha : a ∈ H.edgeSet then e ⟨a,ha⟩ else 0
  have he (a : H.edgeSet) : c a.val = e a := by simp [c]
  have hi : Function.Injective (fun a : H.edgeSet => c a.val) := by
    intro a b h
    exact e.injective ((he a).symm.trans (h.trans (he b)))
  refine ⟨c,?_,hi,?_⟩
  · intro a b d hab had hbd hm
    have hh : (⟨s(a,b),hab⟩ : H.edgeSet) = ⟨s(a,d),had⟩ := hi hm.1
    have hpair : s(a,b) = s(a,d) := congrArg Subtype.val hh
    rcases Sym2.eq_iff.mp hpair with ⟨_,hbd'⟩ | ⟨had',hba⟩
    · exact hbd.ne hbd'
    · exact hab.ne hba.symm
  · intro n
    exact ⟨e.symm n,(he _).trans (e.apply_symm_apply n)⟩

/-- A fixed countable induced subgraph can exhaust the palette of a valid
coloring of the entire covered graph. The old bijective coloring is preserved. -/
theorem in_supergraph [Countable V] (H : SimpleGraph V) (G : SimpleGraph W)
    (f : H ↪g G) (hH : H.edgeSet.Infinite) (hG : IsCountableUnionOfTriangleFree G) :
    ∃ c : Sym2 W → ℕ, Valid G c ∧
      ∀ n : ℕ, ∃ a b : V, H.Adj a b ∧ c s(f a,f b) = n := by
  obtain ⟨d,hd,hbij⟩ := bijective_edge_coloring H hH
  obtain ⟨c,hc,hc_old⟩ := Erdos595PrescribedCountableProper.from_countable H G f d hd hG
  refine ⟨c,hc,?_⟩
  intro n
  obtain ⟨e,he⟩ := hbij.2 n
  obtain ⟨⟨a,b⟩,hpair⟩ := Sym2.mk_surjective e.val
  have hab : H.Adj a b := by
    change s(a,b) ∈ H.edgeSet
    rw [hpair]
    exact e.property
  exact ⟨a,b,hab,(hc_old a b).trans (by simpa only [hpair] using he)⟩

/-- Requiring every valid coloring to use a fresh color beyond one fixed
countable old graph is already a non-coverability assumption, not a consequence
of the old graph having no finite palette. -/
theorem no_fresh_color_principle [Countable V] (H : SimpleGraph V) (G : SimpleGraph W)
    (f : H ↪g G) (hH : H.edgeSet.Infinite) (hG : IsCountableUnionOfTriangleFree G) :
    ¬(∀ c : Sym2 W → ℕ, Valid G c →
      ∃ n : ℕ, ∀ a b : V, H.Adj a b → c s(f a,f b) ≠ n) := by
  intro h
  obtain ⟨c,hc,hex⟩ := in_supergraph H G f hH hG
  obtain ⟨n,hn⟩ := h c hc
  obtain ⟨a,b,hab,he⟩ := hex n
  exact hn a b hab he

#print axioms bijective_edge_coloring
#print axioms in_supergraph
#print axioms no_fresh_color_principle
end Erdos595PaletteLocalization
