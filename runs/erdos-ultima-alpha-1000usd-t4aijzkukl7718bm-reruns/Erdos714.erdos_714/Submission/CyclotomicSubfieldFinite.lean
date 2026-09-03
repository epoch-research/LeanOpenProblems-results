import Submission.CyclotomicSubfield

/-! Actual finite-field instantiation of the degree-six weight quotient.
The subfield embedding is constructed, not left as a hypothesis. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000

namespace Erdos714WeightedPower
variable (p k : ℕ) [Fact p.Prime]
local instance (n : ℕ) : Fintype (GaloisField p n) := Fintype.ofFinite _

def quadraticEmbedding (hk : k ≠ 0) : GaloisField p (2*k) →ₐ[ZMod p] GaloisField p (6*k) := by
  apply Classical.choice
  apply FiniteField.nonempty_algHom_of_finrank_dvd
  rw [GaloisField.finrank p (by omega : 2*k ≠ 0),GaloisField.finrank p (by omega : 6*k ≠ 0)]
  exact ⟨3,by ring⟩

lemma sixth_card (hk : k ≠ 0) : Fintype.card (GaloisField p (6*k))=(p^k)^6 := by
  rw [Fintype.card_eq_nat_card,GaloisField.card p (6*k) (by omega),←pow_mul]
  congr 1
  ring

lemma second_card (hk : k ≠ 0) : Fintype.card (GaloisField p (2*k))=(p^k)^2 := by
  rw [Fintype.card_eq_nat_card,GaloisField.card p (2*k) (by omega),←pow_mul]
  congr 1
  ring

/-- Every prime and every positive extension parameter are included. -/
theorem finite_quotient_budget (hk : k ≠ 0) (C : ℕ)
    (H : SimpleGraph ((GaloisField p (6*k) × Weight (GaloisField p (6*k)) (quotientExponent (p^k))) ⊕
      (GaloisField p (6*k) × Weight (GaloisField p (6*k)) (quotientExponent (p^k)))))
    (hH : H ≤ graph (powerMap (GaloisField p (6*k)) (quotientExponent (p^k))))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hdense : (p^k)^14 ≤ C*H.edgeFinset.card) : (p^k)^2 ≤ 663552*C^4 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq : 2 ≤ p^k := by
    calc
      2 ≤ p := hp
      _ ≤ p^k := by simpa only [pow_one] using pow_le_pow_right' (show 1 ≤ p by omega) (show 1 ≤ k by omega)
  exact quotient_budget (p^k) C hq (sixth_card p k hk)
    (quadraticEmbedding p k hk).toRingHom (second_card p k hk) H hH hfree hdense

/-- The full host already contains K44 once q>=3; no claim is made here for q=2. -/
theorem finite_quotient_not_free (hk : k ≠ 0) (hq : 3 ≤ p^k) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (powerMap (GaloisField p (6*k)) (quotientExponent (p^k)))) := by
  let ι := (quadraticEmbedding p k hk).toRingHom
  have hd : Fintype.card (GaloisField p (2*k))-1 ∣ quotientExponent (p^k) := by
    rw [second_card p k hk]
    exact quadratic_kernel_divides (p^k) (by omega)
  have hc : 2*4 ≤ Fintype.card (GaloisField p (2*k)) := by
    rw [second_card p k hk]
    nlinarith
  intro hfree
  exact hfree ⟨subfieldCopy _ ι (power_kernel _ ι hd) 4 hc⟩

end Erdos714WeightedPower
#print axioms Erdos714WeightedPower.quadraticEmbedding
#print axioms Erdos714WeightedPower.finite_quotient_budget
#print axioms Erdos714WeightedPower.finite_quotient_not_free
