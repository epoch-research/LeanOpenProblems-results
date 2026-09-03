import Submission.ArcTwoCover
import Submission.InfiniteTriangleRamsey

/-!
An unrestricted third right-adjoint target need not be countably edge-covered,
even when its base is countable, K4-free, and has a two-piece triangle-free cover.
The target contains a complete graph larger than the continuum, hence also K4.
This is a warning about profile targets, NOT a witness for Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ThirdRightProfile
open Erdos595ArcAdjoint Erdos595Work

variable {I A V W : Type*}

/-- Functoriality, obtained from the arc/right adjunction. -/
noncomputable def rightHom {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) : right G →g right H :=
  toRight (f.comp (fromRight SimpleGraph.Hom.id))

/-- Two complementary selectors give a biclique in a complete graph. -/
noncomputable def selector (e : I × Bool ↪ A) (S : Set I) :
    Biclique (⊤ : SimpleGraph A) := by
  classical
  refine ⟨(e '' {p | p.2 = decide (p.1 ∈ S)},
    e '' {p | p.2 ≠ decide (p.1 ∈ S)}), ?_⟩
  rintro a ⟨p,hp,rfl⟩ b ⟨q,hq,rfl⟩ he
  have hpq := e.injective he
  subst q
  exact hq hp

/-- A right adjoint raises an infinite complete subgraph to its power set. -/
noncomputable def inflation (e : I × Bool ↪ A) :
    (⊤ : SimpleGraph (Set I)) →g right (⊤ : SimpleGraph A) := by
  classical
  refine ⟨selector e, ?_⟩
  intro S T hST
  have hex : ∃ i, decide (i ∈ S) ≠ decide (i ∈ T) := by
    by_contra hn
    push_neg at hn
    apply hST
    ext i
    simpa only [decide_eq_decide] using hn i
  obtain ⟨i,hi⟩ := hex
  refine ⟨⟨e (i,decide (i ∈ T)), ?_, ?_⟩,
    ⟨e (i,decide (i ∈ S)), ?_, ?_⟩⟩
  · exact ⟨(i,decide (i ∈ T)), hi.symm, rfl⟩
  · exact ⟨(i,decide (i ∈ T)), rfl, rfl⟩
  · exact ⟨(i,decide (i ∈ S)), hi, rfl⟩
  · exact ⟨(i,decide (i ∈ S)), rfl, rfl⟩

private noncomputable def natPair : ℕ × Bool ↪ ℕ := by
  classical
  exact ⟨Encodable.encode,Encodable.encode_injective⟩

/-- Prepend a bit to a subset of the naturals. -/
private def setPair : Set ℕ × Bool ↪ Set ℕ where
  toFun p := {n | if n = 0 then p.2 = true else n - 1 ∈ p.1}
  inj' := by
    intro p q he
    apply Prod.ext
    · ext n
      have h := Set.ext_iff.mp he (n + 1)
      simpa using h
    · have h := Set.ext_iff.mp he 0
      simpa using h

abbrev base := arcGraph (⊤ : SimpleGraph ℕ)
abbrev target := right (right (right base))

/-- The complete graph on a double power set of ℕ occurs in the third target. -/
noncomputable def largeClique :
    (⊤ : SimpleGraph (Set (Set ℕ))) →g target :=
  (rightHom (rightHom (unit (⊤ : SimpleGraph ℕ)))).comp
    ((rightHom (inflation natPair)).comp (inflation setPair))

private def binaryToSet : (ℕ → Fin 2) ↪ Set ℕ where
  toFun f := {n | f n = 1}
  inj' := by
    intro f g he
    funext n
    have h := Set.ext_iff.mp he n
    change (f n = 1 ↔ g n = 1) at h
    have hf := (f n).isLt
    have hg := (g n).isLt
    apply Fin.ext
    have hf' : f n = 1 ↔ (f n).val = 1 := by simp [Fin.ext_iff]
    have hg' : g n = 1 ↔ (g n).val = 1 := by simp [Fin.ext_iff]
    rw [hf',hg'] at h
    omega

/-- No countable palette works on this target. This does not assert K4-freeness. -/
theorem no_countable_cover : ¬IsCountableUnionOfTriangleFree target := by
  intro h
  have hc := countable_union_of_hom largeClique h
  obtain ⟨f,hf⟩ := Erdos595InfiniteTriangleRamsey.complete_cover_iff_binary.mp hc
  exact Function.cantor_injective (binaryToSet ∘ f) (binaryToSet.injective.comp hf)

private def fourSets : Fin 4 ↪ Set (Set ℕ) where
  toFun i := {{i.val}}
  inj' := by
    intro i j he
    apply Fin.ext
    exact Set.singleton_injective (Set.singleton_injective he)

private def completeEmbedding {B : Type*} {G : SimpleGraph V}
    (f : (⊤ : SimpleGraph B) →g G) : (⊤ : SimpleGraph B) ↪g G where
  toFun := f
  inj' := f.injective_of_top_hom
  map_rel_iff' := by
    intro a b
    exact ⟨fun h he => h.ne (congrArg f he),f.map_adj⟩

/-- Explicitly record the reason this is not a solution of the conjecture. -/
theorem not_cliqueFree_four : ¬target.CliqueFree 4 := by
  let f : (⊤ : SimpleGraph (Fin 4)) →g (⊤ : SimpleGraph (Set (Set ℕ))) :=
    ⟨fourSets,fun h he => h (fourSets.injective he)⟩
  exact SimpleGraph.not_cliqueFree_of_top_embedding (completeEmbedding (largeClique.comp f))

theorem base_countable : Countable (Arc (⊤ : SimpleGraph ℕ)) := inferInstance

theorem base_cliqueFree_four : base.CliqueFree 4 := arc_cliqueFree_four _

theorem base_two_cover : ∃ H K : SimpleGraph (Arc (⊤ : SimpleGraph ℕ)),
    H.CliqueFree 3 ∧ K.CliqueFree 3 ∧ base = H ⊔ K := arc_two_cover _

#print axioms inflation
#print axioms largeClique
#print axioms no_countable_cover
#print axioms not_cliqueFree_four
#print axioms base_two_cover
end Erdos595ThirdRightProfile
