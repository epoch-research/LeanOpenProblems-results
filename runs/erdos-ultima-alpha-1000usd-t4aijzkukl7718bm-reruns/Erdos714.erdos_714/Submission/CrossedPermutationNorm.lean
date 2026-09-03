import Submission.DicksonPermutation

/-!
Exact counts for norm graphs with crossed permutation parameters. No freeness
claim is made: the crossed Dickson example has separately checked finite
bicliques. The norm and the two sides of each incidence are kept explicit.
-/

open SimpleGraph
namespace Erdos714CrossedNorm

variable {F E : Type*} [Field F] [Field E]

/-- Crossed parameters: the row point is permuted using the column weight. -/
def graph (N : E →*₀ F) (P : Fˣ → E ≃ E) : SimpleGraph (Bool × (E × Fˣ)) where
  Adj v w := v.1 ≠ w.1 ∧
    N (P w.2.2 v.2.1 + P v.2.2 w.2.1) = (v.2.2 : F)*(w.2.2 : F)
  symm := by
    intro v w h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by intro v h; exact h.1 rfl

def recoveredWeight (N : E →*₀ F) (a : Fˣ) (z : {z : E // z ≠ 0}) : Fˣ :=
  Units.mk0 (N z.val / (a : F)) (div_ne_zero ((map_ne_zero N).mpr z.property) a.ne_zero)

/-- Each neighbor is parameterized by one nonzero value of the norm argument.
No assumption that the norm is surjective, or that its fibers are uniform,
is required for this exact equivalence. -/
def neighborEquiv (N : E →*₀ F) (P : Fˣ → E ≃ E) (v : Bool × (E × Fˣ)) :
    (graph N P).neighborSet v ≃ {z : E // z ≠ 0} where
  toFun w := ⟨P w.val.2.2 v.2.1 + P v.2.2 w.val.2.1, by
    intro hz
    have he := w.property.2
    rw [hz, map_zero] at he
    exact mul_ne_zero v.2.2.ne_zero w.val.2.2.ne_zero he.symm⟩
  invFun z := ⟨(!v.1,
    ((P v.2.2).symm (z.val-P (recoveredWeight N v.2.2 z) v.2.1),
      recoveredWeight N v.2.2 z)), by
    constructor
    · change v.1 ≠ !v.1
      cases v.1 <;> decide
    · change N (P (recoveredWeight N v.2.2 z) v.2.1 +
        P v.2.2 ((P v.2.2).symm (z.val-P (recoveredWeight N v.2.2 z) v.2.1))) =
        (v.2.2 : F)*(N z.val/(v.2.2 : F))
      rw [Equiv.apply_symm_apply, add_sub_cancel]
      field_simp⟩
  left_inv w := by
    have hn : P w.val.2.2 v.2.1+P v.2.2 w.val.2.1 ≠ 0 := by
      intro hz
      have he := w.property.2
      rw [hz, map_zero] at he
      exact mul_ne_zero v.2.2.ne_zero w.val.2.2.ne_zero he.symm
    have hb : recoveredWeight N v.2.2
        ⟨P w.val.2.2 v.2.1+P v.2.2 w.val.2.1, hn⟩ = w.val.2.2 := by
      apply Units.ext
      change N (P w.val.2.2 v.2.1+P v.2.2 w.val.2.1)/(v.2.2 : F) = (w.val.2.2 : F)
      rw [w.property.2]
      field_simp
    apply Subtype.ext
    apply Prod.ext
    · change (!v.1) = w.val.1
      have hs := w.property.1
      cases hv : v.1 <;> cases hw : w.val.1 <;> simp_all
    · apply Prod.ext
      · change (P v.2.2).symm
          (P w.val.2.2 v.2.1+P v.2.2 w.val.2.1-P (recoveredWeight N v.2.2 _) v.2.1) = _
        rw [hb, add_sub_cancel_left, Equiv.symm_apply_apply]
      · exact hb
  right_inv z := by
    apply Subtype.ext
    change P (recoveredWeight N v.2.2 z) v.2.1 +
      P v.2.2 ((P v.2.2).symm (z.val-P (recoveredWeight N v.2.2 z) v.2.1)) = z.val
    rw [Equiv.apply_symm_apply, add_sub_cancel]

open Classical in
/-- The degree is exactly the number of nonzero elements of the extension. -/
theorem degree [Fintype F] [Fintype E] (N : E →*₀ F) (P : Fˣ → E ≃ E)
    (v : Bool × (E × Fˣ)) : (graph N P).degree v = Fintype.card E-1 := by
  rw [← card_neighborSet_eq_degree, Fintype.card_congr (neighborEquiv N P v)]
  rw [Fintype.card_subtype_compl]
  simp

open Classical in
/-- The two-part graph has precisely |E|(|F|-1)(|E|-1) edges. -/
theorem edges [Fintype F] [Fintype E] (N : E →*₀ F) (P : Fˣ → E ≃ E) :
    (graph N P).edgeFinset.card =
      Fintype.card E*(Fintype.card F-1)*(Fintype.card E-1) := by
  have h := (graph N P).sum_degrees_eq_twice_card_edges
  simp only [degree N P, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_units, smul_eq_mul] at h
  nlinarith

omit [Field E] in
open Classical in
lemma vertices [Fintype F] [Fintype E] :
    Fintype.card (Bool × (E × Fˣ)) = 2*Fintype.card E*(Fintype.card F-1) := by
  simp [Fintype.card_prod, Fintype.card_units, mul_assoc]

section Dickson
variable [Algebra F E] [FiniteDimensional F E] [Fintype E] [CharP E 3]

noncomputable def fieldNorm : E →*₀ F where
  toMonoidHom := Algebra.norm F
  map_zero' := Algebra.norm_zero

noncomputable def dicksonPerms
    (hm : Fintype.card E % 5 = 2 ∨ Fintype.card E % 5 = 3) (a : Fˣ) : E ≃ E :=
  Equiv.ofBijective
    (fun x => x^5+algebraMap F E (a : F)*x^3-(algebraMap F E (a : F))^2*x)
    (Erdos714Dickson.sparse_quintic_bijective (algebraMap F E (a : F)) hm)

noncomputable def dicksonGraph
    (hm : Fintype.card E % 5 = 2 ∨ Fintype.card E % 5 = 3) :=
  graph (fieldNorm (F := F) (E := E)) (dicksonPerms hm)

/-- Exact semantics of the proposed cross-parameter Dickson norm relation. -/
lemma dickson_adj_iff
    (hm : Fintype.card E % 5 = 2 ∨ Fintype.card E % 5 = 3)
    (v w : Bool × (E × Fˣ)) :
    (dicksonGraph (F := F) hm).Adj v w ↔ v.1 ≠ w.1 ∧
      Algebra.norm F
        ((v.2.1^5 + algebraMap F E (w.2.2 : F)*v.2.1^3 -
          (algebraMap F E (w.2.2 : F))^2*v.2.1) +
         (w.2.1^5 + algebraMap F E (v.2.2 : F)*w.2.1^3 -
          (algebraMap F E (v.2.2 : F))^2*w.2.1)) = (v.2.2 : F)*(w.2.2 : F) := Iff.rfl

open Classical in
/-- The actual cubic-extension host has the conjectured fourth-case scale,
but this count is not a claim that it avoids K₄,₄. -/
theorem dickson_cubic_edges [Fintype F]
    (hm : Fintype.card E % 5 = 2 ∨ Fintype.card E % 5 = 3)
    (hE : Fintype.card E = Fintype.card F^3) :
    (dicksonGraph (F := F) hm).edgeFinset.card =
      Fintype.card F^3*(Fintype.card F-1)*(Fintype.card F^3-1) := by
  rw [dicksonGraph, edges, hE]

omit [FiniteDimensional F E] [CharP E 3] in
/-- A cubic extension of an odd-degree ternary field satisfies the permutation
hypothesis used above. Both cardinalities refer to the actual fields. -/
lemma odd_cubic_mod [Fintype F] (k : ℕ)
    (hF : Fintype.card F = 3^(2*k+1))
    (hdeg : Module.finrank F E = 3) :
    Fintype.card E % 5 = 2 ∨ Fintype.card E % 5 = 3 := by
  rw [Module.card_eq_pow_finrank (K := F) (V := E), hdeg, hF, ← pow_mul]
  have he : (2*k+1)*3 = 2*(3*k+1)+1 := by omega
  rw [he]
  exact Erdos714Dickson.odd_power_three_mod_five (3*k+1)

end Dickson
end Erdos714CrossedNorm

#print axioms Erdos714CrossedNorm.neighborEquiv
#print axioms Erdos714CrossedNorm.edges
#print axioms Erdos714CrossedNorm.dickson_adj_iff
#print axioms Erdos714CrossedNorm.dickson_cubic_edges

#print axioms Erdos714CrossedNorm.odd_cubic_mod
