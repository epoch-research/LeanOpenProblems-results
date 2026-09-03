import Submission.AffineCompactnessReduction
import Submission.InfiniteTriangleRamsey

/-!
Finite-subgraph affine representability over a countable field does not have
unrestricted compactness. Every countable graph has an injective scalar
representation over Q, whereas a sufficiently large complete graph has no
representation over any countable field, in any vector-space dimension.

The counterexample contains K4. Nothing here disproves compactness restricted
to K4-free graphs, or settles Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595CountableFieldNoncompactness
open Erdos595AffineCompactness

variable {V K : Type*} [Field K]

/-- Three different scalar labels are nondegenerately affinely dependent. -/
theorem represents_of_injective (G : SimpleGraph V) (f : Sym2 V → K)
    (hf : Function.Injective f) : Represents (K := K) G f := by
  intro a b c hab hac hbc
  have hxy : f s(a,b) ≠ f s(a,c) := by
    intro he
    rcases Sym2.eq_iff.mp (hf he) with h | h
    · exact hbc.ne h.2
    · exact hac.ne h.1
  have hxz : f s(a,b) ≠ f s(b,c) := by
    intro he
    rcases Sym2.eq_iff.mp (hf he) with h | h
    · exact hab.ne h.1
    · exact hac.ne h.1
  have hyz : f s(a,c) ≠ f s(b,c) := by
    intro he
    rcases Sym2.eq_iff.mp (hf he) with h | h
    · exact hab.ne h.1
    · exact hac.ne h.1
  let x := f s(a,b)
  let y := f s(a,c)
  let z := f s(b,c)
  have hden : x - z ≠ 0 := sub_ne_zero.mpr hxz
  refine ⟨(y-z)/(x-z), div_ne_zero (sub_ne_zero.mpr hyz) hden, ?_, ?_, hxz⟩
  · intro he
    have h : y - z = x - z := (div_eq_one_iff_eq hden).mp he
    apply hxy
    change x = y
    linear_combination -h
  · change y = ((y-z)/(x-z))*x + (1-(y-z)/(x-z))*z
    field_simp
    ring

/-- This does not require K4-freeness, or even triangle-freeness. -/
theorem countable_rational_representation [Countable V] (G : SimpleGraph V) :
    ∃ f : Sym2 V → ℚ, Represents (K := ℚ) G f := by
  obtain ⟨e,he⟩ := exists_injective_nat (Sym2 V)
  let f : Sym2 V → ℚ := fun a => (e a : ℚ)
  refine ⟨f, represents_of_injective G f ?_⟩
  intro a b hab
  exact he (Nat.cast_injective hab)

/-- In particular, every finite induced subgraph of every graph has such a
one-dimensional representation over the same countable field. -/
theorem finite_subgraphs_rational (G : SimpleGraph V) (S : Finset V) :
    ∃ f : Sym2 S → ℚ, Represents (K := ℚ) (G.induce (S : Set V)) f :=
  countable_rational_representation _

abbrev Large := Set (ℕ → Fin 2)

/-- A global representation would give a forbidden countable edge cover. -/
theorem large_complete_not_representable (K E : Type*) [Field K] [Countable K]
    [AddCommGroup E] [Module K E] :
    ¬∃ f : Sym2 Large → E, Represents (K := K) (⊤ : SimpleGraph Large) f := by
  rintro ⟨f,hf⟩
  exact Erdos595InfiniteTriangleRamsey.large_complete_no_cover
    (cover_of_represents _ f hf)

/-- Unrestricted finite-subgraph compactness over Q is false, even with no
bound at all on the dimension of the putative global representation. -/
theorem noncompactness (E : Type*) [AddCommGroup E] [Module ℚ E] :
    (∀ S : Finset Large, ∃ f : Sym2 S → ℚ,
      Represents (K := ℚ) ((⊤ : SimpleGraph Large).induce (S : Set Large)) f) ∧
    ¬∃ f : Sym2 Large → E, Represents (K := ℚ) (⊤ : SimpleGraph Large) f :=
  ⟨finite_subgraphs_rational _, large_complete_not_representable ℚ E⟩

#print axioms represents_of_injective
#print axioms countable_rational_representation
#print axioms noncompactness
end Erdos595CountableFieldNoncompactness
