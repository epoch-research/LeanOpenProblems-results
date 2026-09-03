import Submission.FiniteTriangleRamsey
import Submission.UniformAffineObstruction
import Submission.FiniteF4Obstruction

/-!
For every finite palette of affine ratios, there is a finite K4-free graph
with no noncollapsed affine edge representation using that palette, in any
dimension and over any field. In particular NO fixed finite field satisfies
the premise of AffineCompactnessReduction.universal_cover_of_finite_field.
This excludes that proposed approach; it does not settle Erdős 595.
-/
set_option autoImplicit false
set_option linter.style.existsImplication false
open SimpleGraph Set
namespace Erdos595FiniteRatioObstruction
open Erdos595FiniteTrianglePartite Erdos595AffineCompactness
universe u

variable {K C V E : Type*} [Field K] [AddCommGroup E] [Module K E]

def RepresentsUsing (r : C → K) (G : SimpleGraph V) (f : Sym2 V → E) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
    ∃ k : C, r k ≠ 0 ∧ r k ≠ 1 ∧
      f s(a,c) = r k • f s(a,b) + (1-r k) • f s(b,c) ∧ f s(a,b) ≠ f s(b,c)

/-- A finite obstruction for any fixed finite set of allowed ratios. -/
theorem finite_ratio_obstruction (K : Type*) [Field K] (C : Type) [Finite C]
    (r : C → K) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ (E : Type u) [AddCommGroup E] [Module K E],
        ¬∃ f : Sym2 V → E, RepresentsUsing r G f := by
  classical
  let H := Erdos595UniformAffineObstruction.G
  obtain ⟨V,hV,G,hG,hRam⟩ := Erdos595FiniteTriangleRamsey.finite_triangle_ramsey
    12 (Option C) H Erdos595UniformAffineObstruction.cliqueFree
  refine ⟨V,hV,G,hG,?_⟩
  intro E _ _
  rintro ⟨F,hF⟩
  let ratio : Option C → K := Option.elim' 0 r
  have hchoice : ∀ x : Fin 3 → V, ∃ k : Option C, IsTriangle G x →
      ratio k ≠ 0 ∧ ratio k ≠ 1 ∧
      F s(x 0,x 2) = ratio k • F s(x 0,x 1) + (1-ratio k) • F s(x 1,x 2) ∧
      F s(x 0,x 1) ≠ F s(x 1,x 2) := by
    intro x
    by_cases hx : IsTriangle G x
    · obtain ⟨k,hk⟩ := hF (x 0) (x 1) (x 2)
        (hx 0 1 (by decide)) (hx 0 2 (by decide)) (hx 1 2 (by decide))
      exact ⟨some k,fun _ => hk⟩
    · exact ⟨none,fun h => (hx h).elim⟩
  choose col hcol using hchoice
  obtain ⟨e,z,he⟩ := hRam col
  let f : Fin 12 → Fin 12 → E := fun a b => F s(e a,e b)
  have ht (a b c : Fin 12) (hab : a < b) (hbc : b < c)
      (h₁ : H.Adj a b) (h₂ : H.Adj a c) (h₃ : H.Adj b c) :
      ratio z ≠ 0 ∧ ratio z ≠ 1 ∧
      f a c = ratio z • f a b + (1-ratio z) • f b c ∧ f a b ≠ f b c := by
    let x : Fin 3 → Fin 12 := ![a,b,c]
    have hx : IsTriangle H x := Erdos595FiniteF4Obstruction.triangle_vec H a b c h₁ h₂ h₃
    have hx' : IsTriangle G (e ∘ x) := fun i j hij => e.map_rel_iff.mpr (hx i j hij)
    have hz := he x (Erdos595FiniteF4Obstruction.strict_vec a b c hab hbc) hx
    have hh := hcol (e ∘ x) hx'
    rw [hz] at hh
    exact hh
  have hs := ht 1 6 10 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact Erdos595UniformAffineObstruction.no_uniform (ratio z) hs.1 hs.2.1 f
    (fun a b c hab hbc h₁ h₂ h₃ => (ht a b c hab hbc h₁ h₂ h₃).2.2.1) hs.2.2.2

/-- No fixed finite field represents all finite K4-free graphs, even with
arbitrarily large vector-space dimensions. -/
theorem finite_field_obstruction (K : Type) [Field K] [Finite K] :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V), G.CliqueFree 4 ∧
      ∀ (E : Type u) [AddCommGroup E] [Module K E],
        ¬∃ f : Sym2 V → E, Represents (K := K) G f :=
  finite_ratio_obstruction K K id

/-- This is exactly the failure of the finite-field premise proposed earlier. -/
theorem no_universal_finite_field (K : Type) [Field K] [Finite K] :
    ¬(∀ (A : Type) [Finite A] (H : SimpleGraph A), H.CliqueFree 4 →
      ∃ n : ℕ, ∃ f : Sym2 A → (Fin n → K), Represents (K := K) H f) := by
  intro h
  obtain ⟨V,hV,G,hG,hbad⟩ := finite_field_obstruction K
  letI := hV
  obtain ⟨n,f,hf⟩ := h V G hG
  exact hbad (Fin n → K) ⟨f,hf⟩

#print axioms finite_ratio_obstruction
#print axioms finite_field_obstruction
#print axioms no_universal_finite_field
end Erdos595FiniteRatioObstruction
