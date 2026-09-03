import Submission.BoundaryPrescribedExtension
import Submission.IncidenceShiftRamsey

/-!
A countably properly colorable attaching subgraph permits literal extension
of a prescribed triangle-avoiding edge coloring across free amalgamation.
Only edge coverability, not proper vertex colorability, is required of the host.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ProperAttachmentExtension
open Erdos595FiniteAdapted Erdos595Work Erdos595FiniteFolkmanAmalgamation
variable {A B I : Type*}

theorem amalgamation (H : SimpleGraph A) (K : SimpleGraph B)
    (D : Set A) (e : I → H.induce D ↪g K) (i₀ : I)
    (c : Sym2 A → ℕ) (hc : Valid H c)
    (hD : Nonempty ((H.induce D).Coloring ℕ))
    (hK : IsCountableUnionOfTriangleFree K) :
    ∃ d : Sym2 (Vertex D (B := B) (I := I)) → ℕ,
      Valid (graph H K D e) d ∧
      ∀ a b, d s(copy H K D e i₀ a,copy H K D e i₀ b) = c s(a,b) := by
  classical
  obtain ⟨k⟩ := hD
  have hH := (countable_union_iff_edge_coloring H).mpr ⟨c,hc⟩
  have hcover := Erdos595AmalgamationCover.countable_cover H K D e hH hK
  let label : A → ℕ := fun a => if h : a ∈ D then k ⟨a,h⟩ else 0
  apply Erdos595BoundaryExtension.along_embedding H (graph H K D e)
    (copyEmbedding H K D e i₀) c hc label ?_ hcover
  intro a b w hw hab haw hbw
  have memD (a : A) (haw : (graph H K D e).Adj (copy H K D e i₀ a) w) :
      a ∈ D := by
    by_contra ha
    rw [copy_of_not_mem H K D e i₀ a ha] at haw
    exact hw (neighbor_private H K D e haw)
  have ha := memD a haw
  have hb := memD b hbw
  simp only [label,dif_pos ha,dif_pos hb]
  exact k.valid hab

universe u
variable {T : Type u} [LinearOrder T]

theorem incidence_amalgamation (H : SimpleGraph A) (K : SimpleGraph B)
    (D : Set A) (e : I → H.induce D ↪g K) (i₀ : I)
    (f : Erdos595IncidenceShiftRamsey.incidence T ≃g H.induce D)
    (c : Sym2 A → ℕ) (hc : Valid H c)
    (hK : IsCountableUnionOfTriangleFree K) :
    ∃ d : Sym2 (Vertex D (B := B) (I := I)) → ℕ,
      Valid (graph H K D e) d ∧
      ∀ a b, d s(copy H K D e i₀ a,copy H K D e i₀ b) = c s(a,b) :=
  amalgamation H K D e i₀ c hc
    ⟨(Erdos595IncidenceShiftRamsey.incidenceColoring T).comp f.symm.toHom⟩ hK

#print axioms amalgamation
#print axioms incidence_amalgamation
end Erdos595ProperAttachmentExtension
