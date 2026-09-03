import Submission.FiniteFolkmanPartite

/-! One finite partite amalgamation step, homogenizing a chosen pair of parts. -/

open SimpleGraph Set
namespace Erdos595FiniteFolkmanStep
open Erdos595FiniteFolkmanPartite

/-- Any edge coloring of the new finite K4-free graph has a part-preserving
copy of H whose edges between the two prescribed parts are monochromatic. -/
theorem step {A R C : Type} [Finite A] [Finite C] [Nonempty C]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) (π : A → R)
    (hπ : ∀ a b, H.Adj a b → π a ≠ π b) (r s : R) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V) (ρ : V → R),
      G.CliqueFree 4 ∧ (∀ a b, G.Adj a b → ρ a ≠ ρ b) ∧
      ∀ c : Sym2 V → C, ∃ f : H ↪g G,
        (∀ a, ρ (f a) = π a) ∧
        ∃ z : C, ∀ a b, H.Adj a b → π a = r → π b = s → c s(f a,f b) = z := by
  classical
  cases isEmpty_or_nonempty (Edge H π r s) with
  | inl hempty =>
    refine ⟨A,inferInstance,H,π,hH,hπ,?_⟩
    intro c
    refine ⟨RelEmbedding.refl _,fun _ => rfl,Classical.arbitrary C,?_⟩
    intro a b hab ha hb
    exact isEmptyElim (show Edge H π r s from ⟨(a,b),hab,ha,hb⟩)
  | inr hnonempty =>
    have hrs : r ≠ s := by
      let x : Edge H π r s := Classical.arbitrary _
      intro he
      exact hπ x.val.1 x.val.2 x.property.1
        (x.property.2.1.trans (he.trans x.property.2.2.symm))
    obtain ⟨B,hB,K,ρ,hK,hρ,hpart⟩ := partite (C := C) H hH π hπ r s hrs
    letI := hB
    let D : Set A := {a | π a = r ∨ π a = s}
    let I := {f : H.induce D ↪g K // ∀ a, ρ (f a) = π a.val}
    haveI : Finite (H.induce D ↪g K) :=
      Finite.of_injective (fun f : H.induce D ↪g K => (f : D → B)) DFunLike.coe_injective
    haveI : Finite I := inferInstance
    let e : I → H.induce D ↪g K := Subtype.val
    let G := Erdos595FiniteFolkmanAmalgamation.graph H K D e
    let χ : Erdos595FiniteFolkmanAmalgamation.Vertex D (B := B) (I := I) → R :=
      fun v => match v with
        | .inl b => ρ b
        | .inr t => π t.2.val
    have hχ : ∀ a b, G.Adj a b → χ a ≠ χ b := by
      intro a b hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact hρ a b hab
        | inr t =>
          obtain ⟨d,hd,hda⟩ := hab
          change ρ a ≠ π t.2.val
          rw [← hd]
          change ρ (t.1.val d) ≠ π t.2.val
          rw [t.1.property d]
          exact hπ _ _ hda
      | inr t =>
        cases b with
        | inl b =>
          obtain ⟨d,hd,had⟩ := hab
          change π t.2.val ≠ ρ b
          rw [← hd]
          change π t.2.val ≠ ρ (t.1.val d)
          rw [t.1.property d]
          exact hπ _ _ had
        | inr u => exact hπ _ _ hab.2
    refine ⟨_,inferInstance,G,χ,Erdos595FiniteFolkmanAmalgamation.cliqueFree H K D e hH hK,hχ,?_⟩
    intro c
    let cB : Sym2 B → C := fun x => c (x.map Sum.inl)
    obtain ⟨f,z,hf,hfz⟩ := hpart cB
    let i : I := ⟨f,hf⟩
    let g := Erdos595FiniteFolkmanAmalgamation.copyEmbedding H K D e i
    refine ⟨g,?_,z,?_⟩
    · intro a
      change χ (Erdos595FiniteFolkmanAmalgamation.copy H K D e i a) = π a
      by_cases ha : a ∈ D
      · rw [Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ ha]
        exact hf ⟨a,ha⟩
      · rw [Erdos595FiniteFolkmanAmalgamation.copy_of_not_mem _ _ _ _ _ _ ha]
    · intro a b hab ha hb
      have had : a ∈ D := Or.inl ha
      have hbd : b ∈ D := Or.inr hb
      change c s(Erdos595FiniteFolkmanAmalgamation.copy H K D e i a,
        Erdos595FiniteFolkmanAmalgamation.copy H K D e i b) = z
      rw [Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ had,
        Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ hbd]
      exact hfz ⟨a,had⟩ ⟨b,hbd⟩ hab

#print axioms step
end Erdos595FiniteFolkmanStep
