import Submission.ExponentLemmas
import Submission.C4Lower
import Submission.K2tUpper

/-!
# The rational-exponent conclusion for graphs between C₄ and K₂,t

The finite-field lower construction and the common-neighbor upper bound force
exponent `3/2` whenever `C₄ ⊑ H ⊑ K₂,t`. This is a cyclic special case, not a
resolution for arbitrary bipartite forbidden graphs.
-/

open Filter Asymptotics SimpleGraph

namespace Erdos713Cyclic

universe u

lemma extremalNumber_isBigO_of_isContained {V W : Type*}
    {H : SimpleGraph V} {G : SimpleGraph W} (h : H ⊑ G) :
    (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (extremalNumber n G : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [] with n
  have hn : (extremalNumber n H : ℝ) ≤ extremalNumber n G := by
    exact_mod_cast h.extremalNumber_le (n := n)
  simpa using hn

/-- Every graph sandwiched between C₄ and K₂,t has only the possible pure-power
exponent `3/2`. The asymptotic coefficient is assumed positive. -/
theorem exponent_eq_three_halves_of_equivalent {W : Type u} {H : SimpleGraph W}
    {t : ℕ} (ht : 1 ≤ t)
    (hLower : Erdos713C4Lower.C4 ⊑ H) (hUpper : H ⊑ Erdos713K2tUpper.K2t t)
    {a c : ℝ} (hc : 0 < c)
    (ha : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 := by
  have hTheta := ha.isTheta.of_const_mul_right hc.ne'
  apply le_antisymm
  · exact Erdos713Work.exponent_le_of_isBigO (hTheta.2.trans
      (Erdos713K2tUpper.extremalNumber_isBigO_rpow_of_isContained ht hUpper))
  · exact Erdos713C4Lower.exponent_ge_three_halves_of_isBigO
      ((extremalNumber_isBigO_of_isContained hLower).trans hTheta.1)

/-- Rationality for all finite forbidden graphs between C₄ and K₂,t. -/
theorem rational_exponent_of_equivalent {q t : ℕ} {H : SimpleGraph (Fin q)}
    (ht : 1 ≤ t)
    (hLower : Erdos713C4Lower.C4 ⊑ H) (hUpper : H ⊑ Erdos713K2tUpper.K2t t)
    {a c : ℝ} (hc : 0 < c)
    (ha : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) :
    a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3 / 2, ?_⟩
  push_cast
  exact (exponent_eq_three_halves_of_equivalent ht hLower hUpper hc ha).symm

/-- The first cyclic forbidden graph has exponent exactly `3/2`. -/
theorem C4_exponent_eq_three_halves {a c : ℝ} (hc : 0 < c)
    (ha : (fun n : ℕ => (extremalNumber n Erdos713C4Lower.C4 : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 :=
  exponent_eq_three_halves_of_equivalent (t := 2) (by omega)
    (IsContained.refl _) (IsContained.refl _) hc ha

/-- K₂,t contains C₄ whenever `t ≥ 2`. -/
lemma C4_isContained_K2t {t : ℕ} (ht : 2 ≤ t) :
    Erdos713C4Lower.C4 ⊑ Erdos713K2tUpper.K2t t := by
  refine ⟨⟨⟨Sum.map id (Fin.castLE ht), ?_⟩, ?_⟩⟩
  · rintro (a | a) (b | b) h <;>
      simp_all [Erdos713C4Lower.C4, Erdos713K2tUpper.K2t,
        completeBipartiteGraph_adj]
  · exact Function.injective_id.sumMap (Fin.castLE_injective ht)

/-- In particular, every K₂,t with `t ≥ 2` has the unique possible exponent `3/2`. -/
theorem K2t_exponent_eq_three_halves {t : ℕ} (ht : 2 ≤ t) {a c : ℝ} (hc : 0 < c)
    (ha : (fun n : ℕ => (extremalNumber n (Erdos713K2tUpper.K2t t) : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 :=
  exponent_eq_three_halves_of_equivalent (by omega) (C4_isContained_K2t ht)
    (IsContained.refl _) hc ha


end Erdos713Cyclic

#print axioms Erdos713Cyclic.exponent_eq_three_halves_of_equivalent
#print axioms Erdos713Cyclic.rational_exponent_of_equivalent
#print axioms Erdos713Cyclic.C4_exponent_eq_three_halves
