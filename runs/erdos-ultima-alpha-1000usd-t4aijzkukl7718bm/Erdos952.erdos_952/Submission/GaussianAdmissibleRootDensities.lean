import Submission.FinitePatternAdmissibility
import Submission.GaussianHigherPolynomialCounts

/-! Every nonempty locally admissible finite Gaussian pattern has strictly
positive and strictly subunit root density at EVERY Gaussian prime. This
verifies the density hypotheses of the optimized sieve, without inferring
any existence of actual prime translates from admissibility. -/
namespace Erdos952Investigation.GaussianAdmissibleRootDensities
open FinitePatternAdmissibility FiniteSieveReduction GaussianIdealRepresentatives
open GaussianPolynomialBoxCounts GaussianWeightedSieve
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

lemma prime_norm_ne_one (q : GaussianInt) (hq : Prime q) : q.norm.natAbs ≠ 1 := by
  intro h
  have hn : q.norm = 1 := by
    have hh := congrArg (fun n : ℕ => (n : ℤ)) h
    simpa only [Int.natCast_natAbs,abs_of_nonneg (GaussianInt.norm_nonneg q),Nat.cast_one] using hh
  exact hq.not_unit ((Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) q).mp hn)

lemma exists_translate_avoiding_prime {κ : Type*} [Fintype κ] (z : κ → GaussianInt)
    (hz : FiniteAdmissible z) (q : GaussianInt) (hq : Prime q) :
    ∃ t : GaussianInt, ¬ q ∣ (patternPolynomial z).eval t := by
  obtain ⟨p,hp,hpq⟩ := Nat.exists_prime_and_dvd (prime_norm_ne_one q hq)
  have hdiv : (p : ℤ) ∣ q.norm := by
    have hh : (p : ℤ) ∣ (q.norm.natAbs : ℤ) := by exact_mod_cast hpq
    simpa only [Int.natCast_natAbs,abs_of_nonneg (GaussianInt.norm_nonneg q)] using hh
  obtain ⟨t,ht⟩ := (admissible_iff_sieve_translates z).mp hz p
  refine ⟨t,?_⟩
  intro he
  rw [patternPolynomial_eval,hq.dvd_finset_prod_iff] at he
  obtain ⟨i,_,hi⟩ := he
  exact ht i p le_rfl hp (hdiv.trans (Zsqrtd.normMonoidHom.map_dvd hi))

lemma admissible_rootCount_lt {κ : Type*} [Fintype κ] (z : κ → GaussianInt)
    (hz : FiniteAdmissible z) (q : GaussianInt) (hq : Prime q) :
    rho (patternPolynomial z) q < q.norm.natAbs := by
  classical
  letI : Finite (GaussianInt ⧸ multiples q) := quotient_finite q hq.ne_zero
  letI := Fintype.ofFinite (GaussianInt ⧸ multiples q)
  obtain ⟨t,ht⟩ := exists_translate_avoiding_prime z hz q hq
  have hmiss : (Submodule.Quotient.mk t : GaussianInt ⧸ multiples q) ∉
      rootClasses q hq.ne_zero (patternPolynomial z) := by
    simpa only [mem_rootClasses] using ht
  have hss : rootClasses q hq.ne_zero (patternPolynomial z) ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _,?_⟩
    intro he
    exact hmiss (he.symm ▸ Finset.mem_univ _)
  have hh := Finset.card_lt_card hss
  rw [Finset.card_univ,← Nat.card_eq_fintype_card,quotient_card q hq.ne_zero] at hh
  simpa only [rho_of_ne_zero _ q hq.ne_zero,rootCount] using hh

lemma nonempty_rootCount_pos {κ : Type*} [Fintype κ] [Nonempty κ]
    (z : κ → GaussianInt) (q : GaussianInt) (hq : Prime q) : 0 < rho (patternPolynomial z) q := by
  rw [rho_of_ne_zero _ q hq.ne_zero,rootCount,rootClasses_prime_pattern z q hq]
  exact Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- The exact local-density condition needed by the Selberg optimizer. -/
theorem admissible_root_density_bounds {κ : Type*} [Fintype κ] [Nonempty κ]
    (z : κ → GaussianInt) (hz : FiniteAdmissible z) (q : GaussianInt) (hq : Prime q) :
    0 < rho (patternPolynomial z) q ∧ rho (patternPolynomial z) q < q.norm.natAbs :=
  ⟨nonempty_rootCount_pos z q hq,admissible_rootCount_lt z hz q hq⟩

#print axioms exists_translate_avoiding_prime
#print axioms admissible_root_density_bounds
end
end Erdos952Investigation.GaussianAdmissibleRootDensities
