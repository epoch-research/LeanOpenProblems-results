import Submission.GraphReduction

/-! Reduction to finite barriers around the fixed Gaussian prime 3. -/

namespace Erdos952Investigation

lemma gaussian_prime_three : Prime (3 : GaussianInt) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 3).mpr rfl

lemma gaussian_moat_fixed_seed_equivalence :
    (∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) ↔
    ∃ C : ℤ, {w | (primeGraph C).Reachable (3 : GaussianInt) w}.Infinite := by
  constructor
  · rintro ⟨x, C, hx, h⟩
    let D := max C ((x 0 - 3).norm + 1)
    have hCD : C ≤ D := le_max_left _ _
    have hstart : (primeGraph D).Reachable (3 : GaussianInt) (x 0) := by
      by_cases h0 : x 0 = 3
      · rw [h0]
      · apply SimpleGraph.Adj.reachable
        refine ⟨gaussian_prime_three, (h 0).1, Ne.symm h0, ?_⟩
        exact lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
    have hreach (n : ℕ) : (primeGraph D).Reachable (3 : GaussianInt) (x n) := by
      induction n with
      | zero => exact hstart
      | succ n ih =>
        apply ih.trans
        apply SimpleGraph.Adj.reachable
        refine ⟨(h n).1, (h (n + 1)).1, ?_, lt_of_lt_of_le (h n).2 hCD⟩
        intro heq
        have := hx heq
        omega
    refine ⟨D, (Set.infinite_range_of_injective hx).mono ?_⟩
    rintro w ⟨n, rfl⟩
    exact hreach n
  · rintro ⟨C, h⟩
    exact gaussian_moat_graph_equivalence.mpr ⟨C, 3, h⟩

/-- A finite set that contains 3 and cannot be left by a permitted prime step. -/
def MoatCertificate (C : ℤ) (S : Finset GaussianInt) : Prop :=
  (3 : GaussianInt) ∈ S ∧
    ∀ z ∈ S, ∀ w, (primeGraph C).Adj z w → w ∈ S

lemma fixed_component_finite_iff_certificate (C : ℤ) :
    {w | (primeGraph C).Reachable (3 : GaussianInt) w}.Finite ↔
      ∃ S : Finset GaussianInt, MoatCertificate C S := by
  classical
  constructor
  · intro hfin
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · simp
    · intro z hz w hzw
      have hz' : (primeGraph C).Reachable (3 : GaussianInt) z := by simpa using hz
      simpa using hz'.trans hzw.reachable
  · rintro ⟨S, hs⟩
    apply S.finite_toSet.subset
    have hwalk : ∀ {a b : GaussianInt}, (primeGraph C).Walk a b → a ∈ S → b ∈ S := by
      intro a b p
      induction p with
      | nil => exact id
      | cons hadj p ih =>
        intro ha
        exact ih (hs.2 _ ha _ hadj)
    intro w hw
    exact hw.elim fun p => hwalk p hs.1

lemma gaussian_moat_negation_iff_certificates :
    (¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) ↔
    ∀ C : ℤ, ∃ S : Finset GaussianInt, MoatCertificate C S := by
  rw [gaussian_moat_fixed_seed_equivalence]
  simp only [not_exists, Set.not_infinite]
  exact forall_congr' fixed_component_finite_iff_certificate

#print axioms gaussian_moat_fixed_seed_equivalence
#print axioms gaussian_moat_negation_iff_certificates

end Erdos952Investigation
