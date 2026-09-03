import Submission.FiniteTriangleStep
import Submission.FiniteOrderedTripleRamsey
import Submission.FiniteInducedRamsey

/-! Finite ordered triangle-Ramsey hosts preserving K4-freeness. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteTriangleRamsey
open Erdos595FiniteTrianglePartite

/-- Every finite ordered K4-free graph has a finite K4-free host for a fixed
finite coloring of ordered triangles. No countable-palette assertion is made. -/
theorem finite_triangle_ramsey (n : ℕ) (C : Type) [Finite C] [Nonempty C]
    (H : SimpleGraph (Fin n)) (hH : H.CliqueFree 4) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ c : (Fin 3 → V) → C, ∃ (f : H ↪g G) (z : C),
        ∀ x : Fin 3 → Fin n, StrictMono x → IsTriangle H x → c (f ∘ x) = z := by
  classical
  obtain ⟨R,hR,oR,hRam⟩ := Erdos595FiniteOrderedTripleRamsey.finite_ramsey n C
  letI := hR
  letI := oR
  letI : Fintype R := Fintype.ofFinite R
  let I := ((Fin n) ↪ R) × Fin n
  haveI : Finite ((Fin n) ↪ R) := Finite.of_injective
    (fun f : (Fin n) ↪ R => (f : Fin n → R)) DFunLike.coe_injective
  let K := Erdos595FiniteInducedRamsey.initial H R
  let π : I → R := fun a => a.1 a.2
  have hπ : ∀ a b, K.Adj a b → π a ≠ π b := by
    intro a b hab he
    apply hab.2.ne
    apply a.1.injective
    change a.1 a.2 = b.1 b.2 at he
    simpa only [← hab.1] using he
  obtain ⟨V,hV,G,ρ,hG,_,hh⟩ := Erdos595FiniteTriangleStep.homogenize
    (C := C) K (Erdos595FiniteInducedRamsey.initial_cliqueFree H hH)
    π hπ (Finset.univ : Finset (Fin 3 → R))
  refine ⟨V,hV,G,hG,?_⟩
  intro c
  obtain ⟨f,_,hf⟩ := hh c
  have hz : ∀ p : Fin 3 → R, ∃ z : C, ∀ x : Fin 3 → I,
      IsTriangle K x → (∀ i, π (x i) = p i) → c (f ∘ x) = z := by
    intro p
    exact hf p (Finset.mem_univ _)
  choose d hd using hz
  obtain ⟨q,z,hq⟩ := hRam d
  let g := Erdos595FiniteInducedRamsey.initialCopy H q.toEmbedding
  refine ⟨f.comp g,z,?_⟩
  intro x hx ht
  have he := hd (q ∘ x) (g ∘ x)
    (fun i j hij => g.map_rel_iff.mpr (ht i j hij)) (fun _ => rfl)
  exact he.trans (hq x hx)

#print axioms finite_triangle_ramsey
end Erdos595FiniteTriangleRamsey
