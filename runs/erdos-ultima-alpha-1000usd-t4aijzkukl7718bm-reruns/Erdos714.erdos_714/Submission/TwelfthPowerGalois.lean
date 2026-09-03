import Submission.AffinePowerFinite

/-! The degree-twelve exclusion on explicit Galois fields, with the base-field
embedding constructed rather than supplied as an assumption. -/
noncomputable section
open Classical SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714SkewPowerGrid
variable (p k : ℕ) [Fact p.Prime]
local instance (n : ℕ) : Fintype (GaloisField p n) := Fintype.ofFinite _

lemma galois_card (n : ℕ) (hn : n ≠ 0) :
    Fintype.card (GaloisField p n)=p^n := by
  rw [Fintype.card_eq_nat_card,GaloisField.card p n hn]

def baseEmbedding (hk : k ≠ 0) : GaloisField p k →ₐ[ZMod p] GaloisField p (12*k) := by
  apply Classical.choice
  apply FiniteField.nonempty_algHom_of_finrank_dvd
  rw [GaloisField.finrank p hk,GaloisField.finrank p (by omega : 12*k ≠ 0)]
  exact ⟨12,by ring⟩

lemma base_degree (hk : k ≠ 0) :
    letI : Algebra (GaloisField p k) (GaloisField p (12*k)) :=
      (baseEmbedding p k hk).toRingHom.toAlgebra
    Module.finrank (GaloisField p k) (GaloisField p (12*k))=12 := by
  letI : Algebra (GaloisField p k) (GaloisField p (12*k)) :=
    (baseEmbedding p k hk).toRingHom.toAlgebra
  have hq : 2 ≤ p^k := by
    rw [←galois_card p k hk]
    exact Fintype.one_lt_card
  have he := Module.card_eq_pow_finrank (K := GaloisField p k) (V := GaloisField p (12*k))
  rw [galois_card p k hk,galois_card p (12*k) (by omega)] at he
  have hpow : p^(12*k)=(p^k)^12 := by rw [←pow_mul]; congr 1; ring
  rw [hpow] at he
  exact (Nat.pow_right_injective hq he).symm

/-- Every characteristic and every positive extension parameter are included. -/
theorem galois_twelfth_not_free (hk : k ≠ 0) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714WeightedPower.graph (Erdos714WeightedPower.powerMap
        (GaloisField p (12*k)) (torusExponent (p^k)))) := by
  letI : Algebra (GaloisField p k) (GaloisField p (12*k)) :=
    (baseEmbedding p k hk).toRingHom.toAlgebra
  have h := Erdos714AffinePowerGrid.twelfth_not_free_all (base_degree p k hk)
  rw [galois_card p k hk] at h
  exact h

/-- The two-sheet refinement also fails in every odd characteristic. -/
theorem galois_twelfth_double_not_free (hk : k ≠ 0) (hp : p ≠ 2) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714WeightedPower.graph (Erdos714WeightedPower.powerMap
        (GaloisField p (12*k)) (torusExponent (p^k)/2))) := by
  letI : Algebra (GaloisField p k) (GaloisField p (12*k)) :=
    (baseEmbedding p k hk).toRingHom.toAlgebra
  have hq : Odd (Fintype.card (GaloisField p k)) := by
    rw [galois_card p k hk]
    exact ((Fact.out : Nat.Prime p).odd_of_ne_two hp).pow
  have h := twelfth_double_not_free hq (base_degree p k hk)
  rw [galois_card p k hk] at h
  exact h

end Erdos714SkewPowerGrid
#print axioms Erdos714SkewPowerGrid.baseEmbedding
#print axioms Erdos714SkewPowerGrid.galois_twelfth_not_free
#print axioms Erdos714SkewPowerGrid.galois_twelfth_double_not_free
