import Submission.SemilinearBothTransport
import Submission.SemilinearBothData

/-! The refined candidate fails on an unbounded family of genuine binary fields,
using the separately checked base-field copy. -/

open SimpleGraph Erdos714BothModel Erdos714BothTransport
noncomputable section
namespace Erdos714BothFamily

abbrev F := Erdos714BothCertificate.F
abbrev Ext (m : ℕ) [NeZero m] := FiniteField.Extension F 2 m

instance extension_charP (m : ℕ) [NeZero m] : CharP (Ext m) 2 :=
  charP_of_injective_algebraMap (algebraMap F (Ext m)).injective 2

lemma extension_card (m : ℕ) [NeZero m] : Nat.card (Ext m) = 2^(9*m) := by
  rw [FiniteField.natCard_extension, Erdos714BothCertificate.field_card]
  norm_num [pow_mul]

lemma extension_copy (m : ℕ) [NeZero m] (hm : Odd m)
    (hs : (completeBipartiteGraph (Fin 4) (Fin 4)) ⊑ graph (K := F)) :
    (completeBipartiteGraph (Fin 4) (Fin 4)) ⊑ graphAt (K := Ext m) (9*m) := by
  have ho : Odd (Module.finrank F (Ext m)) := by
    simpa only [FiniteField.finrank_extension] using hm
  exact hs.trans (graph_map (L := Ext m) Erdos714BothCertificate.field_pow m hm ho)

lemma field_orders_strictMono : StrictMono (fun j : ℕ => Nat.card (Ext (2*j+1))) := by
  intro i j hij
  simp only [extension_card]
  exact Nat.pow_lt_pow_right (by omega) (by omega)

/-- The refined candidate is not free at every odd absolute degree divisible by nine. -/
theorem actual_not_free (m : ℕ) [NeZero m] (hm : Odd m) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graphAt (K := Ext m) (9*m)) := by
  intro h
  exact h (extension_copy m hm Erdos714BothData.actual_copy)

/-- A genuinely unbounded sequence of field orders, each with an actual copy. -/
theorem odd_family :
    StrictMono (fun j : ℕ => Nat.card (Ext (2*j+1))) ∧
      ∀ j : ℕ, ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
        (graphAt (K := Ext (2*j+1)) (9*(2*j+1))) := by
  refine ⟨field_orders_strictMono, fun j => actual_not_free (2*j+1) ?_⟩
  exact ⟨j, by omega⟩

#print axioms actual_not_free
#print axioms odd_family

#print axioms extension_copy
#print axioms extension_card
#print axioms field_orders_strictMono
end Erdos714BothFamily
