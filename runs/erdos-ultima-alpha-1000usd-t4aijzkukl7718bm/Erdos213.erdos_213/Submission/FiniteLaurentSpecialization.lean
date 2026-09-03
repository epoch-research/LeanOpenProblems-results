import FormalConjecturesUtil

/-! A finite-family specialization from several Laurent variables to one.
It preserves any specified finite list of nonzero Laurent polynomials, and
commutes with the involution that negates exponent vectors. This is a
function-field statement, not a bound on numerical rational-distance sets. -/
namespace Erdos213.FiniteLaurentSpecialization
noncomputable section
open Polynomial

/-- A finite set of nonzero integer exponent vectors can simultaneously be
kept nonzero by an integer linear functional. -/
theorem exists_nonvanishing_linear (m : ℕ) (S : Finset (Fin m → ℤ))
    (hS : ∀ v ∈ S, v ≠ 0) :
    ∃ L : (Fin m → ℤ) →ₗ[ℤ] ℤ, ∀ v ∈ S, L v ≠ 0 := by
  classical
  let P : ℤ[X] := ∏ v ∈ S, Polynomial.ofFn m v
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv he
    apply hS v hv
    apply Polynomial.injective_ofFn m
    simpa using he
  obtain ⟨b, hb⟩ : ∃ b : ℤ, P.eval b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hP (Polynomial.zero_of_eval_zero P hn)
  refine ⟨(Polynomial.leval b).comp (Polynomial.ofFn m), ?_⟩
  intro v hv
  have he : ∏ v ∈ S, (Polynomial.ofFn m v).eval b ≠ 0 := by
    simpa only [P, Polynomial.eval_prod] using hb
  exact (Finset.prod_ne_zero_iff.mp he) v hv

/-- No cardinality or exponent bound is needed: a suitable functional is
injective on any prescribed finite collection of exponent vectors. -/
theorem exists_injective_linear (m : ℕ) (S : Finset (Fin m → ℤ)) :
    ∃ L : (Fin m → ℤ) →ₗ[ℤ] ℤ, Set.InjOn L (S : Set (Fin m → ℤ)) := by
  classical
  let D := (S.biUnion (fun x => S.image (fun y => x-y))).erase 0
  obtain ⟨L, hL⟩ := exists_nonvanishing_linear m D
    (fun v hv => Finset.ne_of_mem_erase hv)
  refine ⟨L, ?_⟩
  intro x hx y hy he
  by_contra hxy
  have hd : x-y ∈ D := by
    apply Finset.mem_erase.mpr
    refine ⟨sub_ne_zero.mpr hxy, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩
  exact hL (x-y) hd (by simp only [map_sub,he,sub_self])

abbrev Laurent (m : ℕ) := AddMonoidAlgebra ℚ (Fin m → ℤ)
abbrev OneLaurent := AddMonoidAlgebra ℚ ℤ

/-- Substitution of the variables by powers of a single variable. -/
def specialize {m : ℕ} (L : (Fin m → ℤ) →ₗ[ℤ] ℤ) :
    Laurent m →+* OneLaurent :=
  AddMonoidAlgebra.mapDomainRingHom ℚ L.toAddMonoidHom

/-- A prescribed finite support undergoes no coefficient cancellation. -/
theorem exists_support_injective_specialization (m : ℕ)
    (S : Finset (Fin m → ℤ)) :
    ∃ L : (Fin m → ℤ) →ₗ[ℤ] ℤ,
      Set.InjOn (specialize L) {p : Laurent m | (p.support : Set (Fin m → ℤ)) ⊆ (S : Set (Fin m → ℤ))} := by
  obtain ⟨L,hL⟩ := exists_injective_linear m S
  exact ⟨L,Finsupp.mapDomain_injOn (S : Set (Fin m → ℤ)) hL⟩

/-- Every member of a finite family stays nonzero exactly when it was nonzero.
In particular, denominators and incidence determinants may all be included
in the same finite family. -/
theorem finite_family_preserved (m : ℕ) (T : Finset (Laurent m)) :
    ∃ L : (Fin m → ℤ) →ₗ[ℤ] ℤ,
      ∀ p ∈ T, specialize L p = 0 ↔ p = 0 := by
  classical
  let S := T.biUnion (fun p => p.support)
  obtain ⟨L,hL⟩ := exists_support_injective_specialization m S
  refine ⟨L,?_⟩
  intro p hp
  constructor
  · intro he
    apply hL (x₁ := p) (x₂ := 0)
    · intro a ha
      exact Finset.mem_biUnion.mpr ⟨p,hp,ha⟩
    · simp
    · simpa only [map_zero] using he
  · rintro rfl
    exact map_zero _

/-- Negating exponents is the unit-circle conjugation on the rational
Laurent algebra. No complex specialization is asserted by this definition. -/
def reverse (G : Type*) [AddCommGroup G] :
    AddMonoidAlgebra ℚ G →+* AddMonoidAlgebra ℚ G :=
  AddMonoidAlgebra.mapDomainRingHom ℚ (-AddMonoidHom.id G)

/-- Monomial specialization commutes with exponent reversal. -/
theorem specialize_reverse {m : ℕ} (L : (Fin m → ℤ) →ₗ[ℤ] ℤ)
    (p : Laurent m) :
    specialize L (reverse (Fin m → ℤ) p) = reverse ℤ (specialize L p) := by
  change Finsupp.mapDomain L (Finsupp.mapDomain (fun x => -x) p) =
    Finsupp.mapDomain (fun x => -x) (Finsupp.mapDomain L p)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext x
  exact map_neg L x

#print axioms exists_injective_linear
#print axioms finite_family_preserved
#print axioms specialize_reverse
end
end Erdos213.FiniteLaurentSpecialization
