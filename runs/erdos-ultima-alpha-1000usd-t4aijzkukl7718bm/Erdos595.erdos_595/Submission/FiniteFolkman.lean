import Submission.FiniteFolkmanHomogenize
import Submission.FiniteFolkmanRamsey
import Submission.CountableGenericUniversality

/-!
The finite triangle Folkman theorem: for each fixed finite palette there
is a finite K4-free graph with a monochromatic triangle in every edge
coloring. This does NOT assert the countable-palette analogue.
-/

open SimpleGraph Set
open Erdos595FinitePalette
namespace Erdos595FiniteFolkman

private def triangleEmbedding {R : Type*} (K : SimpleGraph R) (a b d : R)
    (hab : K.Adj a b) (had : K.Adj a d) (hbd : K.Adj b d) :
    (⊤ : SimpleGraph (Fin 3)) ↪g K := by
  let f : (⊤ : SimpleGraph (Fin 3)) →g K :=
    { toFun := ![a,b,d]
      map_rel' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [K.adj_comm] }
  exact {
    toFun := f
    inj' := f.injective_of_top_hom
    map_rel_iff' := by
      intro i j
      constructor
      · intro h
        change i ≠ j
        intro he
        exact h.ne (congrArg f he)
      · exact f.map_rel }

private def initial {R : Type} (K : SimpleGraph R) :
    SimpleGraph (((⊤ : SimpleGraph (Fin 3)) ↪g K) × Fin 3) where
  Adj a b := a.1 = b.1 ∧ a.2 ≠ b.2
  symm := fun _ _ h => ⟨h.1.symm,Ne.symm h.2⟩
  loopless := fun a h => h.2 rfl

private theorem finite_folkman_nonempty (C : Type) [Finite C] [Nonempty C] :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧ ¬HasColoring G C := by
  classical
  obtain ⟨R,hR,K,hK⟩ := Erdos595FiniteFolkmanRamsey.finite_ramsey C
  letI := hR
  letI : Fintype R := Fintype.ofFinite R
  letI : LinearOrder R := IsWellOrder.linearOrder WellOrderingRel
  let T := (⊤ : SimpleGraph (Fin 3)) ↪g K
  haveI : Finite T := Finite.of_injective (fun f : T => (f : Fin 3 → R)) DFunLike.coe_injective
  let A := T × Fin 3
  let H := initial K
  let π : A → R := fun a => a.1 a.2
  have hH : H.CliqueFree 4 :=
    (show H.Colorable 3 from ⟨SimpleGraph.Coloring.mk Prod.snd (fun h => h.2)⟩).cliqueFree (by decide)
  have hπ : ∀ a b, H.Adj a b → π a ≠ π b := by
    intro a b hab he
    apply hab.2
    apply a.1.injective
    change a.1 a.2 = b.1 b.2 at he
    simpa only [← hab.1] using he
  obtain ⟨V,hV,G,ρ,hG,_,hh⟩ := Erdos595FiniteFolkmanHomogenize.homogenize
    (C := C) H hH π hπ (Finset.univ : Finset (R × R))
  letI := hV
  refine ⟨V,hV,G,hG,?_⟩
  rintro ⟨c,hc⟩
  obtain ⟨f,_,hf⟩ := hh c
  have hz : ∀ r s : R, ∃ z : C, ∀ a b : A, H.Adj a b → π a = r → π b = s → c s(f a,f b) = z := by
    intro r s
    exact hf (r,s) (Finset.mem_univ _)
  choose z hz using hz
  let d₀ : R → R → C := fun r s => if r ≤ s then z r s else z s r
  have hd₀ : ∀ r s, d₀ r s = d₀ s r := by
    intro r s
    by_cases h : r ≤ s
    · by_cases h' : s ≤ r
      · have he := le_antisymm h h'
        subst s
        rfl
      · simp only [d₀,if_pos h,if_neg h']
    · have h' : s ≤ r := le_of_not_ge h
      simp only [d₀,if_neg h,if_pos h']
  let d : Sym2 R → C := Sym2.lift ⟨d₀,hd₀⟩
  have he : ∀ a b : A, H.Adj a b → c s(f a,f b) = d s(π a,π b) := by
    intro a b hab
    change c s(f a,f b) = d₀ (π a) (π b)
    dsimp only [d₀]
    split_ifs with h
    · exact hz (π a) (π b) a b hab rfl rfl
    · simpa only [Sym2.eq_swap] using hz (π b) (π a) b a hab.symm rfl rfl
  apply hK
  refine ⟨d,?_⟩
  intro a b t hab hat hbt hm
  let q : T := triangleEmbedding K a b t hab hat hbt
  have h₀₁ : H.Adj (q,0) (q,1) := ⟨rfl,by change (0 : Fin 3) ≠ 1; decide⟩
  have h₀₂ : H.Adj (q,0) (q,2) := ⟨rfl,by change (0 : Fin 3) ≠ 2; decide⟩
  have h₁₂ : H.Adj (q,1) (q,2) := ⟨rfl,by change (1 : Fin 3) ≠ 2; decide⟩
  apply hc (f (q,0)) (f (q,1)) (f (q,2))
    (f.map_rel_iff.mpr h₀₁) (f.map_rel_iff.mpr h₀₂) (f.map_rel_iff.mpr h₁₂)
  rw [he _ _ h₀₁,he _ _ h₀₂,he _ _ h₁₂]
  exact hm

/-- Finite triangle Folkman theorem, with no extra set-theoretic axiom. -/
theorem finite_folkman (C : Type) [Finite C] :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧ ¬HasColoring G C := by
  classical
  cases isEmpty_or_nonempty C with
  | inl h =>
    refine ⟨Fin 3,inferInstance,⊤,?_,?_⟩
    · exact (SimpleGraph.Coloring.mk (G := (⊤ : SimpleGraph (Fin 3))) id (fun h => h)).colorable.cliqueFree (by decide)
    · rintro ⟨c,_⟩
      exact isEmptyElim (c s(0,1))
  | inr h => exact finite_folkman_nonempty C

/-- The explicit countable generic base has no finite triangle-free edge palette. -/
theorem generic_no_finite_coloring (C : Type) [Finite C] :
    ¬HasColoring Erdos595CountableExtension.G C := by
  obtain ⟨V,hV,H,hH,hn⟩ := finite_folkman C
  letI := hV
  obtain ⟨f⟩ := Erdos595CountableGenericUniversality.universal_countable H hH
  intro hc
  exact hn (hc.comap f.toHom)

#print axioms finite_folkman
#print axioms generic_no_finite_coloring
end Erdos595FiniteFolkman
