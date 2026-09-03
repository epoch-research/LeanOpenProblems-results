import Submission.LocallyFiniteFolkmanTarget
import Submission.FiniteCliqueUltrafilterColoring
import Submission.FiniteExceptionUltrafilterTarget

/-!
One-sided Fubini extensions fold into a locally finite target. In particular,
even full OR iteration does not turn the countable locally finite Folkman
target's unbounded finite palettes into a countable-color obstruction.
This is auxiliary work, not a settlement of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595LocallyFiniteOrFold
open Erdos595Work Erdos595FiniteExceptionUltrafilterTarget
open Erdos595FiniteCliqueUltrafilter

variable {A V : Type*} (H : SimpleGraph A) [H.LocallyFinite]

/-- For a locally finite target, one Fubini direction already forces both
endpoints to be principal. -/
lemma principal_pair {p q : Ultrafilter A} (h : fubiniAdj H p q) :
    ∃ a b : A, p = pure a ∧ q = pure b ∧ H.Adj a b := by
  obtain ⟨a,ha⟩ := Ultrafilter.nonempty_of_mem h
  obtain ⟨b,hb,hq⟩ := q.eq_pure_of_finite_mem (Set.toFinite (H.neighborSet a)) ha
  subst q
  have hp : H.neighborSet b ∈ p := by
    simpa only [fubiniAdj,Ultrafilter.mem_pure,SimpleGraph.mem_neighborSet,H.adj_comm] using h
  obtain ⟨c,hc,hp⟩ := p.eq_pure_of_finite_mem (Set.toFinite (H.neighborSet b)) hp
  exact ⟨c,b,hp,rfl,hc.symm⟩

lemma collapse_adj_one (d : A) {p q : Ultrafilter A} (h : fubiniAdj H p q) :
    H.Adj (collapse d p) (collapse d q) := by
  obtain ⟨a,b,rfl,rfl,hab⟩ := principal_pair H h
  simpa only [collapse_pure] using hab

/-- Any graph mapping to the locally finite target can undergo a full OR
extension and still map to that same target. -/
noncomputable def nextGraph (d : A) (G : SimpleGraph V) (f : G →g H) :
    SimpleGraph (Ultrafilter V) where
  Adj p q := fubiniAdj G p q ∨ fubiniAdj G q p
  symm := fun _ _ h => h.symm
  loopless := by
    intro p h
    have hh := collapse_adj_one H d (fubiniAdj_map_hom f (h.elim id id))
    exact hh.ne rfl

noncomputable def nextHom (d : A) (G : SimpleGraph V) (f : G →g H) :
    nextGraph H d G f →g H where
  toFun p := collapse d (p.map f)
  map_rel' := by
    intro p q h
    rcases h with h | h
    · exact collapse_adj_one H d (fubiniAdj_map_hom f h)
    · exact (collapse_adj_one H d (fubiniAdj_map_hom f h)).symm

noncomputable def pureHom (d : A) (G : SimpleGraph V) (f : G →g H) :
    G →g nextGraph H d G f where
  toFun := pure
  map_rel' := by
    intro a b h
    apply Or.inl
    simpa only [fubiniAdj,Ultrafilter.mem_pure,Set.mem_setOf_eq,
      SimpleGraph.mem_neighborSet] using h

abbrev Carrier (A : Type*) := Erdos595GenericUltrafilterUniversality.Carrier A

/-- The folding homomorphism is included in the recursively defined stage. -/
noncomputable def stage (d : A) : (n : ℕ) →
    Σ G : SimpleGraph (Carrier A n), G →g H
  | 0 => ⟨H,SimpleGraph.Hom.id⟩
  | n+1 => ⟨nextGraph H d (stage d n).1 (stage d n).2,
    nextHom H d (stage d n).1 (stage d n).2⟩

noncomputable def intoStage (d : A) : (n : ℕ) → H →g (stage H d n).1
  | 0 => SimpleGraph.Hom.id
  | n+1 => (pureHom H d (stage H d n).1 (stage H d n).2).comp (intoStage d n)

lemma retract (d : A) (n : ℕ) (v : A) :
    (stage H d n).2 (intoStage H d n v) = v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change collapse d (Ultrafilter.map (stage H d n).2 (pure (intoStage H d n v))) = v
    rw [Ultrafilter.map_pure,collapse_pure,ih]

lemma stage_cliqueFree (d : A) (hH : H.CliqueFree 4) (n : ℕ) :
    (stage H d n).1.CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  let f := (stage H d n).2.comp e.toHom
  exact no_adj_common_neighbors hH
    (f.map_adj (show (0 : Fin 4) ≠ 1 by decide))
    (f.map_adj (show (0 : Fin 4) ≠ 2 by decide))
    (f.map_adj (show (1 : Fin 4) ≠ 2 by decide))
    (f.map_adj (show (0 : Fin 4) ≠ 3 by decide))
    (f.map_adj (show (1 : Fin 4) ≠ 3 by decide))
    (f.map_adj (show (2 : Fin 4) ≠ 3 by decide))

/-- No finite-palette or countable-palette amplification occurs at any stage. -/
theorem palette_iff (d : A) (n : ℕ) (C : Type*) :
    Erdos595FinitePalette.HasColoring (stage H d n).1 C ↔
      Erdos595FinitePalette.HasColoring H C :=
  ⟨fun h => h.comap (intoStage H d n),fun h => h.comap (stage H d n).2⟩

theorem cover_iff (d : A) (n : ℕ) :
    IsCountableUnionOfTriangleFree (stage H d n).1 ↔ IsCountableUnionOfTriangleFree H :=
  ⟨countable_union_of_hom (intoStage H d n),countable_union_of_hom (stage H d n).2⟩

omit [H.LocallyFinite] in
lemma countable_target_cover [Countable A] : IsCountableUnionOfTriangleFree H := by
  classical
  obtain ⟨enc,henc⟩ := exists_injective_nat (Sym2 A)
  apply Erdos595FinitePalette.HasColoring.countable_cover (C := ℕ)
  refine ⟨enc,?_⟩
  intro a b c hab hac hbc hm
  have he : b=c := by
    rcases Sym2.eq_iff.mp (henc hm.1) with h | h
    · exact h.2
    · exact h.2.trans h.1
  exact hbc.ne he

/-- A concrete counterexample to the proposed finite-to-countable palette
amplification, even using arbitrarily many finite full-OR stages. -/
theorem folkman_stages :
    ∃ d : Erdos595LocallyFiniteFolkmanTarget.Carrier, ∀ n : ℕ,
      (stage Erdos595LocallyFiniteFolkmanTarget.H d n).1.CliqueFree 4 ∧
      IsCountableUnionOfTriangleFree (stage Erdos595LocallyFiniteFolkmanTarget.H d n).1 ∧
      ∀ (C : Type) [Finite C],
        ¬Erdos595FinitePalette.HasColoring (stage Erdos595LocallyFiniteFolkmanTarget.H d n).1 C := by
  obtain ⟨f⟩ := Erdos595LocallyFiniteFolkmanTarget.finite_universal
    (⊥ : SimpleGraph (Fin 1)) (SimpleGraph.cliqueFree_bot (by decide))
  refine ⟨f 0,fun n => ⟨stage_cliqueFree _ _ Erdos595LocallyFiniteFolkmanTarget.cliqueFree n,
    (cover_iff _ _ n).mpr (countable_target_cover _),?_⟩⟩
  intro C _ h
  exact Erdos595LocallyFiniteFolkmanTarget.no_finite_palette C ((palette_iff _ _ n C).mp h)

#print axioms countable_target_cover
#print axioms folkman_stages
#print axioms principal_pair
#print axioms retract
#print axioms stage_cliqueFree
#print axioms palette_iff
#print axioms cover_iff
end Erdos595LocallyFiniteOrFold
