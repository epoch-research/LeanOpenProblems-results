import Submission.AdditiveSlices

/-!
Semilinear evaluation families can be nonlinear globally but additive on
subfield cosets. The statements below make that obstruction explicit.
They do not prove or disprove the balanced Zarankiewicz conjecture.
-/

noncomputable section
open Finset SimpleGraph Classical

namespace Erdos714SemilinearCodeSlices

variable {K E I A : Type*} [CommRing K] [CommRing E] [AddCommGroup A]
  [Fintype K] [Fintype I] [Fintype A]

/-- A semilinear quadratic evaluation family, with arbitrary additive output maps. -/
def family (σ : E →+* E) (T B : E →+ (I → A)) (a : E) : I → A :=
  T a + B (a * σ a)

/-- The additive part of the family on a subring coset. -/
def polarSlice (ι : K →+* E) (σ : E →+* E) (T B : E →+ (I → A))
    (a : E) : K →+ (I → A) where
  toFun t := T (ι t) + B (a * σ (ι t) + ι t * σ a)
  map_zero' := by simp
  map_add' := by
    intro t u
    simp [map_add, mul_add, add_mul, add_assoc, add_left_comm, add_comm]

omit [Fintype K] [Fintype I] [Fintype A] in
/-- If the quadratic output vanishes on the subring, it also vanishes on
its semilinear squares. The remaining coset dependence is additive. -/
lemma coset_factorization (ι : K →+* E) (σ : E →+* E) (τ : K →+* K)
    (hστ : ∀ t, σ (ι t) = ι (τ t))
    (T B : E →+ (I → A)) (hB : ∀ t, B (ι t) = 0) (a : E) (t : K) :
    family σ T B (a + ι t) = family σ T B a + polarSlice ι σ T B a t := by
  have hex : (a + ι t) * σ (a + ι t) =
      a * σ a + (a * σ (ι t) + ι t * σ a) + ι (t * τ t) := by
    rw [map_add, map_mul, ← hστ]
    ring
  unfold family
  rw [hex]
  simp only [polarSlice, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    map_add, hB, add_zero]
  abel

/-- Every subring coset is a genuine additive message slice, regardless of its center. -/
theorem coset_length_bound (ι : K →+* E) (hι : Function.Injective ι)
    (σ : E →+* E) (τ : K →+* K) (hστ : ∀ t, σ (ι t) = ι (τ t))
    (T B : E →+ (I → A)) (hB : ∀ t, B (ι t) = 0) (a : E)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (family σ T B)))
    (hsize : 8*Fintype.card A ≤ Fintype.card K) :
    Fintype.card I ≤ 6*(Fintype.card A)^2 := by
  let e : K ↪ E := ⟨fun t => a + ι t, fun _ _ h => hι (add_left_cancel h)⟩
  apply Erdos714AdditiveSlices.affine_slice_length_bound (family σ T B) e
    (polarSlice ι σ T B a) (family σ T B a) _ hfree hsize
  intro t i
  exact congrFun (coset_factorization ι σ τ hστ T B hB a t) i

/-- Even a positive-density selection from one coset is sufficient. The ambient
row selection can be arbitrary; its embedding and factorization are explicit. -/
theorem selected_coset_length_bound {R : Type*} (f : R → I → A)
    (ι : K →+* E) (σ : E →+* E) (τ : K →+* K) (hστ : ∀ t, σ (ι t) = ι (τ t))
    (T B : E →+ (I → A)) (hB : ∀ t, B (ι t) = 0) (a : E)
    (S : Finset K) (e : S ↪ R)
    (hf : ∀ t : S, f (e t) = family σ T B (a + ι t.1))
    (D : ℕ) (hS : Fintype.card K ≤ D*S.card)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Coding.graph f))
    (hsize : 8*D^3*Fintype.card A ≤ Fintype.card K) :
    Fintype.card I ≤ 6*D^3*(Fintype.card A)^2 := by
  apply Erdos714AdditiveSlices.selected_affine_slice_length_bound f S e
    (polarSlice ι σ T B a) (family σ T B a) D _ hfree hS hsize
  intro t i
  rw [hf]
  exact congrFun (coset_factorization ι σ τ hστ T B hB a t.1) i

/-- Quadratic subfield size and cubic code length are incompatible with freeness. -/
theorem quadratic_subring_not_free (ι : K →+* E) (hι : Function.Injective ι)
    (σ : E →+* E) (τ : K →+* K) (hστ : ∀ t, σ (ι t) = ι (τ t))
    (T B : E →+ (I → A)) (hB : ∀ t, B (ι t) = 0)
    (hq : 8 ≤ Fintype.card A)
    (hK : Fintype.card K = (Fintype.card A)^2)
    (hI : Fintype.card I = (Fintype.card A)^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (family σ T B)) := by
  intro hfree
  have hsize : 8*Fintype.card A ≤ Fintype.card K := by rw [hK]; nlinarith
  have hb := coset_length_bound ι hι σ τ hστ T B hB 0 hfree hsize
  rw [hI] at hb
  have hq6 : Fintype.card A ≤ 6 := by
    apply Nat.le_of_mul_le_mul_right (c := (Fintype.card A)^2) _
      (pow_pos (Fintype.card_pos (α := A)) 2)
    nlinarith
  omega

/-- In characteristic two, a relative-trace output automatically annihilates
the fixed subring. This includes the proposed norm-weighted trace evaluations;
the coordinate-dependent additive maps T and W are entirely arbitrary. -/
theorem quadratic_trace_not_free [CharP E 2]
    (ι : K →+* E) (hι : Function.Injective ι)
    (σ : E →+* E) (τ : K →+* K) (hστ : ∀ t, σ (ι t) = ι (τ t))
    (ρ : E →+* E) (hρ : ∀ t, ρ (ι t) = ι t) (T W : E →+ (I → A))
    (hq : 8 ≤ Fintype.card A)
    (hK : Fintype.card K = (Fintype.card A)^2)
    (hI : Fintype.card I = (Fintype.card A)^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun a => T a + W (a * σ a + ρ (a * σ a)))) := by
  let B : E →+ (I → A) := W.comp (AddMonoidHom.id E + ρ.toAddMonoidHom)
  have hB (t : K) : B (ι t) = 0 := by
    change W (ι t + ρ (ι t)) = 0
    rw [hρ, CharTwo.add_self_eq_zero, map_zero]
  exact quadratic_subring_not_free ι hι σ τ hστ T B hB hq hK hI

#print axioms coset_factorization
#print axioms coset_length_bound
#print axioms selected_coset_length_bound
#print axioms quadratic_subring_not_free
#print axioms quadratic_trace_not_free

end Erdos714SemilinearCodeSlices
