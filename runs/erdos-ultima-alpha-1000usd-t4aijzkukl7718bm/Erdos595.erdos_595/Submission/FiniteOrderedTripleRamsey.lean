import Submission.InfiniteTripleRamsey

/-! Finite ordered Ramsey for triples and finite palettes, by compactness. -/
set_option autoImplicit false
open Set Filter
namespace Erdos595FiniteOrderedTripleRamsey

/-- The finite target and finite palette have a finite ordered triple-Ramsey host. -/
theorem finite_ramsey (n : ℕ) (C : Type) [Finite C] [Nonempty C] :
    ∃ (R : Type) (_ : Finite R) (_ : LinearOrder R),
      ∀ c : (Fin 3 → R) → C, ∃ (f : Fin n ↪o R) (z : C),
        ∀ x : Fin 3 → Fin n, StrictMono x → c (f ∘ x) = z := by
  classical
  obtain ⟨V,oV,wV,hV⟩ := Erdos595InfiniteTripleRamsey.triple_ramsey_host (Fin n) C
  letI := oV
  letI := wV
  have hex : ∃ S : Finset V, ∀ c : (Fin 3 → S) → C,
      ∃ (f : Fin n ↪o S) (z : C),
        ∀ x : Fin 3 → Fin n, StrictMono x → c (f ∘ x) = z := by
    by_contra hn
    push_neg at hn
    choose c hc using hn
    let col : Finset V → (Fin 3 → V) → C := fun S x =>
      if hx : ∀ i, x i ∈ S then c S (fun i => ⟨x i,hx i⟩) else Classical.arbitrary C
    let U : Ultrafilter (Finset V) := Ultrafilter.of atTop
    have hU : (U : Filter (Finset V)) ≤ atTop := Ultrafilter.of_le _
    have hmem (v : V) : ∀ᶠ S in (U : Filter (Finset V)), v ∈ S := by
      apply hU
      exact Filter.eventually_atTop.mpr ⟨{v},fun S hS => hS (by simp)⟩
    have hd : ∀ x : Fin 3 → V, ∃ z : C,
        ∀ᶠ S in (U : Filter (Finset V)), col S x = z := by
      intro x
      apply Ultrafilter.eventually_exists_iff.mp
      exact Filter.Eventually.of_forall (fun S => ⟨col S x,rfl⟩)
    choose d hd using hd
    obtain ⟨f,z,hf⟩ := hV (fun a b c => d ![a,b,c])
    have hmono : ∀ x : Fin 3 → Fin n, StrictMono x → d (f ∘ x) = z := by
      intro x hx
      have he : f ∘ x = ![f (x 0),f (x 1),f (x 2)] := by
        funext i
        fin_cases i <;> rfl
      rw [he]
      exact hf _ _ _ (hx (by decide : (0 : Fin 3) < 1))
        (hx (by decide : (1 : Fin 3) < 2))
    have hm : ∀ᶠ S in (U : Filter (Finset V)), ∀ i : Fin n, f i ∈ S :=
      Filter.eventually_all.mpr (fun i => hmem (f i))
    have hdall : ∀ᶠ S in (U : Filter (Finset V)),
        ∀ x : Fin 3 → Fin n, col S (f ∘ x) = d (f ∘ x) :=
      Filter.eventually_all.mpr (fun x => hd (f ∘ x))
    obtain ⟨S,hm,hdall⟩ := (hm.and hdall).exists
    let fs : Fin n ↪o S := OrderEmbedding.ofStrictMono (fun i => ⟨f i,hm i⟩)
      (fun i j hij => f.strictMono hij)
    obtain ⟨x,hx,hbad⟩ := hc S fs z
    apply hbad
    have he : col S (f ∘ x) = c S (fs ∘ x) := by
      dsimp only [col,Function.comp_apply]
      rw [dif_pos (fun i => hm (x i))]
      rfl
    exact he.symm.trans ((hdall x).trans (hmono x hx))
  obtain ⟨S,hS⟩ := hex
  exact ⟨S,inferInstance,inferInstance,hS⟩

#print axioms finite_ramsey
end Erdos595FiniteOrderedTripleRamsey
