import Submission.ArithmeticProgressions

/-!
# Axiom audit and interface checks for the progression component

This audit imports only the proof component, not the conjecture specification.
-/

#print axioms Erdos672.Progression.gcd_terms_eq_gcd_distance
#print axioms Erdos672.Progression.gcd_terms_dvd_distance
#print axioms Erdos672.Progression.min_factorization_le_distance
#print axioms Erdos672.Progression.off_peak_factorization
#print axioms Erdos672.Progression.distance_product
#print axioms Erdos672.Progression.distance_product_dvd_factorial
#print axioms Erdos672.Progression.off_peak_sum_le_factorial
#print axioms Erdos672.Progression.factorization_product_terms
#print axioms Erdos672.Progression.exists_coefficient_root_bundle
#print axioms Erdos672.Progression.exists_coefficient_root_bundle_range
#print axioms Erdos672.Progression.canonicalFinset_card
#print axioms Erdos672.Progression.canonicalFinset_isAP
#print axioms Erdos672.Progression.finset_eq_canonical
#print axioms Erdos672.Progression.isAP_iff_eq_canonical
#print axioms Erdos672.Progression.product_canonicalFinset
#print axioms Erdos672.Progression.product_eq_of_isAP
#print axioms Erdos672.Progression.forall_ap_product_ne_iff
#print axioms Erdos672.Progression.power_eq_prime_power
#print axioms Erdos672.Progression.no_powers_iff_no_prime_powers

namespace Erdos672.Progression

/-- A nontrivial example: the prime 2 has off-peak residue 1 and peak valuation 5
in the progression 18, 25, 32, whose product is 120 squared. -/
example :
    ∃ U V w : Fin 3 → ℕ, ∃ D : ℕ,
      (∀ i, 0 < U i) ∧ (∀ i, 0 < V i) ∧ (∀ i, 0 < w i) ∧ 0 < D ∧
      (∀ i, V i * (18 + i.val * 7) = U i * w i ^ 2) ∧
      (∀ i, (U i).gcd (V i) = 1) ∧
      (∏ i, U i) = D ∧ (∏ i, V i) = D ∧ D ∣ 2 ∧
      Pairwise (fun i j => (V i).Coprime (V j)) ∧
      (∏ i, w i) = 120 ∧
      (∀ i j, ((w i).gcd (w j)) ^ 2 ∣ Nat.dist i.val j.val) := by
  have hp : (∏ i : Fin 3, (18 + i.val * 7)) = 120 ^ 2 := by
    norm_num [Fin.prod_univ_three]
  simpa using exists_coefficient_root_bundle (by norm_num : 0 < 18)
    (by norm_num : 0 < 3) (by norm_num : Nat.gcd 18 7 = 1)
    (by norm_num : 0 < 2) hp

/-- The theorem also covers the endpoint k = l = 1 and zero step. -/
example : ∃ D : ℕ, 0 < D ∧ D ∣ Nat.factorial 0 := by
  have hp : (∏ i : Fin 1, (1 + i.val * 0)) = 1 ^ 1 := by simp
  obtain ⟨U, V, w, D, _, _, _, hD, _, _, _, _, hDdvd, _, _, _⟩ :=
    exists_coefficient_root_bundle (by norm_num : 0 < 1)
      (by norm_num : 0 < 1) (by norm_num : Nat.gcd 1 0 = 1)
      (by norm_num : 0 < 1) hp
  exact ⟨D, hD, hDdvd⟩

end Erdos672.Progression
