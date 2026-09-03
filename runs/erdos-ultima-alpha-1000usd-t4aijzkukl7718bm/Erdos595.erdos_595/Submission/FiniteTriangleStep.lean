import Submission.FiniteTrianglePartite

/-! One finite triangle-partite amalgamation step and its finite iteration. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteTriangleStep
open Erdos595FiniteTrianglePartite

/-- Homogenize one specified ordered triple of parts. -/
theorem step {A R C : Type} [Finite A] [Finite C] [Nonempty C]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) (π : A → R)
    (hπ : ∀ a b, H.Adj a b → π a ≠ π b) (p : Fin 3 → R) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V) (ρ : V → R),
      G.CliqueFree 4 ∧ (∀ a b, G.Adj a b → ρ a ≠ ρ b) ∧
      ∀ c : (Fin 3 → V) → C, ∃ f : H ↪g G,
        (∀ a, ρ (f a) = π a) ∧
        ∃ z : C, ∀ x : Fin 3 → A, IsTriangle H x →
          (∀ i, π (x i) = p i) → c (f ∘ x) = z := by
  classical
  let T := {x : Fin 3 → A // IsTriangle H x ∧ ∀ i, π (x i) = p i}
  cases isEmpty_or_nonempty T with
  | inl hempty =>
    refine ⟨A,inferInstance,H,π,hH,hπ,?_⟩
    intro c
    refine ⟨RelEmbedding.refl _,fun _ => rfl,Classical.arbitrary C,?_⟩
    intro x hx hp
    exact isEmptyElim (show T from ⟨x,hx,hp⟩)
  | inr hnonempty =>
    let t : T := Classical.arbitrary T
    have pinj : Function.Injective p := by
      intro i j he
      by_contra hij
      exact hπ _ _ (t.property.1 i j hij)
        ((t.property.2 i).trans (he.trans (t.property.2 j).symm))
    let D : Set A := {a | π a ∈ Set.range p}
    have hex : ∀ a : D, ∃ i, p i = π a.val := fun a => a.property
    choose part hpart using hex
    have hproper : ∀ a b : D, (H.induce D).Adj a b → part a ≠ part b := by
      intro a b hab he
      exact hπ _ _ hab ((hpart a).symm.trans ((congrArg p he).trans (hpart b)))
    haveI : Nonempty (Triangle (H.induce D) part) := by
      let x : Fin 3 → D := fun i => ⟨t.val i,⟨i,(t.property.2 i).symm⟩⟩
      refine ⟨⟨x,?_,?_⟩⟩
      · intro i
        apply pinj
        exact (hpart (x i)).trans (t.property.2 i)
      · exact t.property.1
    obtain ⟨B,hB,K,σ,hK,hσ,hmono⟩ := partite (C := C) (H.induce D) part hproper
    letI := hB
    let ρ : B → R := p ∘ σ
    have hρ : ∀ a b, K.Adj a b → ρ a ≠ ρ b :=
      fun a b hab he => hσ a b hab (pinj he)
    let I := {f : H.induce D ↪g K // ∀ a, ρ (f a) = π a.val}
    haveI : Finite (H.induce D ↪g K) :=
      Finite.of_injective (fun f : H.induce D ↪g K => (f : D → B)) DFunLike.coe_injective
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
    refine ⟨_,inferInstance,G,χ,
      Erdos595FiniteFolkmanAmalgamation.cliqueFree H K D e hH hK,hχ,?_⟩
    intro c
    let cB : (Fin 3 → B) → C := fun x => c (Sum.inl ∘ x)
    obtain ⟨f,z,hf,hfz⟩ := hmono cB
    have hf' : ∀ a, ρ (f a) = π a.val := fun a =>
      (congrArg p (hf a)).trans (hpart a)
    let i : I := ⟨f,hf'⟩
    let g := Erdos595FiniteFolkmanAmalgamation.copyEmbedding H K D e i
    refine ⟨g,?_,z,?_⟩
    · intro a
      change χ (Erdos595FiniteFolkmanAmalgamation.copy H K D e i a) = π a
      by_cases ha : a ∈ D
      · rw [Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ ha]
        exact hf' ⟨a,ha⟩
      · rw [Erdos595FiniteFolkmanAmalgamation.copy_of_not_mem _ _ _ _ _ _ ha]
    · intro x hx hp
      let xd : Fin 3 → D := fun j => ⟨x j,⟨j,(hp j).symm⟩⟩
      have hxpart : ∀ j, part (xd j) = j := fun j => pinj ((hpart (xd j)).trans (hp j))
      have he : g ∘ x = Sum.inl ∘ f ∘ xd := by
        funext j
        exact Erdos595FiniteFolkmanAmalgamation.copy_of_mem H K D e i (x j) (xd j).property
      rw [he]
      exact hfz xd hx hxpart

/-- Homogenize any finite set of ordered triples of parts. -/
theorem homogenize {A R C : Type} [Finite A] [Finite C] [Nonempty C]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) (π : A → R)
    (hπ : ∀ a b, H.Adj a b → π a ≠ π b) (T : Finset (Fin 3 → R)) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V) (ρ : V → R),
      G.CliqueFree 4 ∧ (∀ a b, G.Adj a b → ρ a ≠ ρ b) ∧
      ∀ c : (Fin 3 → V) → C, ∃ f : H ↪g G,
        (∀ a, ρ (f a) = π a) ∧
        ∀ p ∈ T, ∃ z : C, ∀ x : Fin 3 → A, IsTriangle H x →
          (∀ i, π (x i) = p i) → c (f ∘ x) = z := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨A,inferInstance,H,π,hH,hπ,?_⟩
    intro c
    exact ⟨RelEmbedding.refl _,fun _ => rfl,by simp⟩
  | @insert p T hp ih =>
    obtain ⟨V,hV,G,ρ,hG,hρ,hprev⟩ := ih
    letI := hV
    obtain ⟨W,hW,K,σ,hK,hσ,hnext⟩ := step (C := C) G hG ρ hρ p
    letI := hW
    refine ⟨W,hW,K,σ,hK,hσ,?_⟩
    intro c
    obtain ⟨g,hg,z,hz⟩ := hnext c
    let d : (Fin 3 → V) → C := fun x => c (g ∘ x)
    obtain ⟨f,hf,hfT⟩ := hprev d
    refine ⟨g.comp f,fun a => (hg (f a)).trans (hf a),?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · refine ⟨z,?_⟩
      intro x hx hxp
      exact hz (f ∘ x) (fun i j hij => f.map_rel_iff.mpr (hx i j hij))
        (fun i => (hf (x i)).trans (hxp i))
    · obtain ⟨w,hw⟩ := hfT q hq
      exact ⟨w,fun x hx hxp => hw x hx hxp⟩

#print axioms step
#print axioms homogenize
end Erdos595FiniteTriangleStep
