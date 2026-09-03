import Submission.FiniteFolkmanStep

/-! Iterating finitely many partite steps. The color palette stays finite. -/

open SimpleGraph Set
namespace Erdos595FiniteFolkmanHomogenize

/-- Simultaneously homogenize every requested pair of parts. -/
theorem homogenize {A R C : Type} [Finite A] [Finite C] [Nonempty C]
    (H : SimpleGraph A) (hH : H.CliqueFree 4) (π : A → R)
    (hπ : ∀ a b, H.Adj a b → π a ≠ π b) (T : Finset (R × R)) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V) (ρ : V → R),
      G.CliqueFree 4 ∧ (∀ a b, G.Adj a b → ρ a ≠ ρ b) ∧
      ∀ c : Sym2 V → C, ∃ f : H ↪g G,
        (∀ a, ρ (f a) = π a) ∧
        ∀ p ∈ T, ∃ z : C, ∀ a b, H.Adj a b → π a = p.1 → π b = p.2 → c s(f a,f b) = z := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨A,inferInstance,H,π,hH,hπ,?_⟩
    intro c
    exact ⟨RelEmbedding.refl _,fun _ => rfl,by simp⟩
  | @insert p T hp ih =>
    obtain ⟨V,hV,G,ρ,hG,hρ,hprev⟩ := ih
    letI := hV
    obtain ⟨W,hW,K,σ,hK,hσ,hnext⟩ := Erdos595FiniteFolkmanStep.step (C := C) G hG ρ hρ p.1 p.2
    letI := hW
    refine ⟨W,hW,K,σ,hK,hσ,?_⟩
    intro c
    obtain ⟨g,hg,z,hz⟩ := hnext c
    let d : Sym2 V → C := fun e => c (e.map g)
    obtain ⟨f,hf,hfT⟩ := hprev d
    refine ⟨g.comp f,fun a => (hg (f a)).trans (hf a),?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · refine ⟨z,?_⟩
      intro a b hab ha hb
      exact hz (f a) (f b) (f.map_rel_iff.mpr hab) ((hf a).trans ha) ((hf b).trans hb)
    · obtain ⟨w,hw⟩ := hfT q hq
      exact ⟨w,fun a b hab ha hb => hw a b hab ha hb⟩

#print axioms homogenize
end Erdos595FiniteFolkmanHomogenize
