import Submission.SecondArcBacktracking

/-!
The countable K4-free target condition on the directed second arc graph is
exactly a proper vertex-coloring condition on the source: a palette N -> Fin 4
suffices and is necessary. The countable target can be fixed in advance.
This stronger condition must not be conflated with countable triangle-free
edge coverability, and this file does not settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595SecondArcTarget
open Erdos595SecondArcBacktracking

variable {V : Type*} (G : SimpleGraph V)
abbrev C := ℕ × Fin 4
abbrev Target := Erdos595ArcAdjoint.arcGraph (⊤ : SimpleGraph C)
abbrev TargetVertex := Erdos595ArcAdjoint.Arc (⊤ : SimpleGraph C)

theorem target_cliqueFree : Target.CliqueFree 4 :=
  Erdos595ArcAdjoint.arc_cliqueFree_four _

/-- First differing coordinates color concatenating directed edges properly. -/
noncomputable def arcColor (c : G.Coloring (ℕ → Fin 4)) :
    (Erdos595ArcAdjoint.arcGraph G).Coloring C := by
  classical
  have hd (e : Erdos595ArcAdjoint.Arc G) : ∃ n, c e.val.1 n ≠ c e.val.2 n := by
    by_contra hn
    push_neg at hn
    exact c.valid e.property (funext hn)
  choose d hd using hd
  let col : Erdos595ArcAdjoint.Arc G → C := fun e => (d e,c e.val.1 (d e))
  refine SimpleGraph.Coloring.mk col ?_
  intro e f hef hh
  have hN := congrArg Prod.fst hh
  have hB := congrArg Prod.snd hh
  change d e = d f at hN
  change c e.val.1 (d e) = c f.val.1 (d f) at hB
  rcases hef with hef | hfe
  · apply hd e
    rw [← hN,← hef] at hB
    exact hB
  · apply hd f
    rw [hN,← hfe] at hB
    exact hB.symm

/-- Two consecutive arc colors form a vertex of one fixed countable arc graph. -/
noncomputable def label (c : G.Coloring (ℕ → Fin 4)) : Walk₂ G → TargetVertex :=
  fun e => ⟨(arcColor G c e.val.1,arcColor G c e.val.2),
    (arcColor G c).valid (Or.inl e.property)⟩

lemma label_rel (c : G.Coloring (ℕ → Fin 4)) (e d : Walk₂ G)
    (hed : Erdos595DirectedRight.arc (Erdos595DirectedRight.arc G.Adj) e d) :
    Target.Adj (label G c e) (label G c d) :=
  Or.inl (congrArg (arcColor G c) hed)

/-- Exact characterization by a FIXED countable K4-free target. -/
theorem fixed_target_iff :
    Nonempty (G.Coloring (ℕ → Fin 4)) ↔
      ∃ f : Walk₂ G → TargetVertex,
        ∀ e d, Erdos595DirectedRight.arc (Erdos595DirectedRight.arc G.Adj) e d →
          Target.Adj (f e) (f d) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨label G c,label_rel G c⟩
  · rintro ⟨f,hf⟩
    exact coloring_sequences G Target target_cliqueFree f hf

/-- Allowing ANY countable K4-free target does not enlarge this class. -/
theorem any_target_iff :
    Nonempty (G.Coloring (ℕ → Fin 4)) ↔
      ∃ (W : Type) (_ : Countable W) (H : SimpleGraph W), H.CliqueFree 4 ∧
        ∃ f : Walk₂ G → W,
          ∀ e d, Erdos595DirectedRight.arc (Erdos595DirectedRight.arc G.Adj) e d →
            H.Adj (f e) (f d) := by
  constructor
  · intro h
    obtain ⟨f,hf⟩ := (fixed_target_iff G).mp h
    exact ⟨TargetVertex,inferInstance,Target,target_cliqueFree,f,hf⟩
  · rintro ⟨W,hW,H,hH,f,hf⟩
    letI := hW
    exact coloring_sequences G H hH f hf

#print axioms arcColor
#print axioms fixed_target_iff
#print axioms any_target_iff
end Erdos595SecondArcTarget
