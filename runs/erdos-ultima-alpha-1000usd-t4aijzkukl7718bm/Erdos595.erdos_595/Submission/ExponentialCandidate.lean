import Submission.Work

/-!
Exponential graphs with countable targets: a candidate family only.
No non-coverability assertion for this family is established in this file.
-/

set_option autoImplicit false

open SimpleGraph Set

namespace Erdos595Exponential

private theorem monochromatic_edge {V C : Type*} [Countable C]
    (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ)) (f : V → C) :
    ∃ a b, B.Adj a b ∧ f a = f b := by
  classical
  obtain ⟨enc, henc⟩ := exists_injective_nat C
  by_contra h
  apply hB.false
  refine SimpleGraph.Coloring.mk (enc ∘ f) ?_
  intro a b hab he
  exact h ⟨a, b, hab, henc he⟩

/-- The usual exponential relation is loopless when the domain has no
countable coloring and the target is countable. -/
def exponential {V W : Type*} [Countable W] (H : SimpleGraph W)
    (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ)) : SimpleGraph (V → W) where
  Adj f g := ∀ a b, B.Adj a b → H.Adj (f a) (g b)
  symm := fun _ _ h a b hab => (h b a hab.symm).symm
  loopless := by
    intro f h
    obtain ⟨a, b, hab, hf⟩ := monochromatic_edge B hB f
    exact (h a b hab).ne hf

/-- Any finite clique in the exponential yields a clique of the same size
in the countable target. -/
theorem exponential_cliqueFree {V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (n : ℕ) (hH : H.CliqueFree n) : (exponential H B hB).CliqueFree n := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  obtain ⟨a, b, hab, heq⟩ := monochromatic_edge B hB (fun x => fun i : Fin n => e i x)
  have hf : ∀ i j : Fin n, i ≠ j → H.Adj (e i a) (e j a) := by
    intro i j hij
    have h := ((e.map_rel_iff).mpr hij) a b hab
    have he : e j a = e j b := congrFun heq j
    exact he ▸ h
  let f : (⊤ : SimpleGraph (Fin n)) ↪g H :=
    { toFun := fun i => e i a
      inj' := fun i j he => by
        by_contra hij
        exact (hf i j hij).ne he
      map_rel_iff' := by
        intro i j
        change H.Adj (e i a) (e j a) ↔ i ≠ j
        constructor
        · intro h he
          subst j
          exact H.loopless _ h
        · exact hf i j }
  exact (SimpleGraph.not_cliqueFree_of_top_embedding f) hH

/-- Constant functions embed the target as a subgraph of the exponential. -/
def constantHom {V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ)) :
    H →g exponential H B hB where
  toFun w := fun _ => w
  map_rel' := fun h _ _ _ => h

/-- Given a graph product map to H, currying gives a map to the exponential.
This supplies a sufficient route to transferring a genuine obstruction,
not a construction of one. -/
def curryHom {U V W : Type*} [Countable W]
    (F : SimpleGraph U) (B : SimpleGraph V) (H : SimpleGraph W)
    (hB : IsEmpty (B.Coloring ℕ)) (f : U → V → W)
    (hf : ∀ u u' v v', F.Adj u u' → B.Adj v v' → H.Adj (f u v) (f u' v')) :
    F →g exponential H B hB where
  toFun := f
  map_rel' := fun h v v' hv => hf _ _ _ _ h hv

theorem no_cover_of_product_map {U V W : Type*} [Countable W]
    (F : SimpleGraph U) (B : SimpleGraph V) (H : SimpleGraph W)
    (hB : IsEmpty (B.Coloring ℕ))
    (hF : ¬Erdos595Work.IsCountableUnionOfTriangleFree F)
    (f : U → V → W)
    (hf : ∀ u u' v v', F.Adj u u' → B.Adj v v' → H.Adj (f u v) (f u' v')) :
    ¬Erdos595Work.IsCountableUnionOfTriangleFree (exponential H B hB) := by
  intro h
  exact hF (Erdos595Work.countable_union_of_hom (curryHom F B H hB f hf) h)

#print axioms exponential_cliqueFree
#print axioms no_cover_of_product_map


/-- If every two domain edges have a cross-edge, monochromatic-edge
witnesses give a homomorphism back to the countable target. -/
noncomputable def crossingEdgesHom {V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (hc : ∀ a b c d, B.Adj a b → B.Adj c d →
      B.Adj a c ∨ B.Adj a d ∨ B.Adj b c ∨ B.Adj b d) :
    exponential H B hB →g H := by
  classical
  choose a b hab heq using fun f : V → W => monochromatic_edge B hB f
  refine ⟨fun f => f (a f), ?_⟩
  intro f g hfg
  rcases hc (a f) (b f) (a g) (b g) (hab f) (hab g) with h | h | h | h
  · exact hfg _ _ h
  · simpa only [← heq g] using hfg _ _ h
  · simpa only [← heq f] using hfg _ _ h
  · simpa only [← heq f, ← heq g] using hfg _ _ h

theorem coloring_nat_of_crossing_edges {V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (hc : ∀ a b c d, B.Adj a b → B.Adj c d →
      B.Adj a c ∨ B.Adj a d ∨ B.Adj b c ∨ B.Adj b d) :
    Nonempty ((exponential H B hB).Coloring ℕ) := by
  classical
  obtain ⟨enc, henc⟩ := exists_injective_nat W
  let f := crossingEdgesHom H B hB hc
  exact ⟨SimpleGraph.Coloring.mk (enc ∘ f) (fun h he => (f.map_adj h).ne (henc he))⟩

/-- In particular, complete domains cannot provide a witness. -/
theorem coloring_nat_complete_domain {V W : Type*} [Countable W]
    (H : SimpleGraph W) (hB : IsEmpty ((⊤ : SimpleGraph V).Coloring ℕ)) :
    Nonempty ((exponential H (⊤ : SimpleGraph V) hB).Coloring ℕ) := by
  apply coloring_nat_of_crossing_edges H _ hB
  intro a b c d hab _
  by_cases he : a = c
  · exact Or.inr (Or.inr (Or.inl (by
      change b ≠ c
      subst c
      exact hab.symm)))
  · exact Or.inl he

/-- For an exponential edge, pointwise failure of target adjacency can
occur only on a countably vertex-colorable part of the domain. This is
not a bound on the chromatic number of the whole domain. -/
theorem badSet_coloring_nat {V W : Type*} [Countable W]
    (H : SimpleGraph W) (B : SimpleGraph V) (hB : IsEmpty (B.Coloring ℕ))
    (f g : V → W) (hfg : (exponential H B hB).Adj f g) :
    Nonempty ((B.induce {x | ¬H.Adj (f x) (g x)}).Coloring ℕ) := by
  classical
  obtain ⟨enc, henc⟩ := exists_injective_nat (W × W)
  refine ⟨SimpleGraph.Coloring.mk (fun x => enc (f x.val, g x.val)) ?_⟩
  intro x y hxy he
  have hp := henc he
  have hg : g x.val = g y.val := congrArg Prod.snd hp
  exact x.property (by simpa only [← hg] using hfg x.val y.val hxy)

#print axioms crossingEdgesHom
#print axioms coloring_nat_complete_domain
#print axioms badSet_coloring_nat

/-- A finite domain subgraph that cannot map to H gives a countable
proper coloring of the exponential by finite restriction. Thus candidate
domains must avoid all such finite homomorphism obstructions. -/
theorem coloring_nat_of_finite_obstruction {U V W : Type*}
    [Finite U] [Countable W]
    (F : SimpleGraph U) (H : SimpleGraph W) (B : SimpleGraph V)
    (hB : IsEmpty (B.Coloring ℕ)) (ι : F →g B) (hF : IsEmpty (F →g H)) :
    Nonempty ((exponential H B hB).Coloring ℕ) := by
  classical
  obtain ⟨enc, henc⟩ := exists_injective_nat (U → W)
  refine ⟨SimpleGraph.Coloring.mk (fun f => enc (f ∘ ι)) ?_⟩
  intro f g hfg he
  have heq := henc he
  apply hF.false
  refine ⟨f ∘ ι, ?_⟩
  intro a b hab
  have h := hfg (ι a) (ι b) (ι.map_adj hab)
  have hb : f (ι b) = g (ι b) := congrFun heq b
  simpa only [Function.comp_apply, ← hb] using h

#print axioms coloring_nat_of_finite_obstruction


end Erdos595Exponential
