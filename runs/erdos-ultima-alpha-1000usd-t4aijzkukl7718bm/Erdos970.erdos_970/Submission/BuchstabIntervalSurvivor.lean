import Submission.BuchstabGridMain
import Submission.BuchstabDominatingTransfer
import Submission.FirstHitEndpointSurvivor

/-! The refined grid yields a fully charged interval survivor criterion for
arbitrary prime sets, using marginal domination rather than extremality. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg

lemma referenceLower_antitone_prefix (n K k : ℕ) (hK : K ≤ k) (D : ℝ)
    (hkeep : primeKeep nthPrime k D) : referenceLower n k D ≤ referenceLower n K D := by
  classical
  have hkeepK : primeKeep nthPrime K D := by
    change (nthPrime K : ℝ)^2 ≤ D
    apply le_trans _ hkeep
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast nthPrime_strictMono.monotone hK
  have hsum : (∑ i : Fin K, primeMarginal i.val*referenceUpper n i.val (D*primeMarginal i.val)) ≤
      ∑ i : Fin k, primeMarginal i.val*referenceUpper n i.val (D*primeMarginal i.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => primeMarginal i*referenceUpper n i (D*primeMarginal i)) K,
      Fin.sum_univ_eq_sum_range (fun i => primeMarginal i*referenceUpper n i (D*primeMarginal i)) k]
    apply sum_le_sum_of_subset_of_nonneg (range_mono hK)
    intro i hi _
    exact mul_nonneg (primeMarginal_pos i).le
      ((nthPrime_prefix_density_pos i).le.trans (reference_density_bounds n i _).2)
  simp only [referenceLower,lowerStep,if_pos hkeep,if_pos hkeepK]
  exact max_le_max_left 0 (sub_le_sub_left hsum 1)

/-- Positivity after all errors transfers from the first-prime reference to
any set with no more than k distinct primes. -/
theorem prime_survivor_of_refined_main (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (k m : ℕ) (hPk : P.card ≤ k) (D : ℝ) (hD : 0 ≤ D)
    (hkeep : primeKeep nthPrime k D) (a : ℝ) (ha : 1 < a)
    (hpos : 4*(1+reciprocalPowerConstant a)^3*D^a < (m : ℝ)*referenceLower 1 k D) :
    ∃ j < m, ∀ p ∈ P, ¬j ≡ r p [MOD p] := by
  classical
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  let q : Fin P.card → ℝ := fun i => 1/(p i : ℝ)
  have hq (i : Fin P.card) : q i < 1 ∧ q i ≤ 1/(nthPrime i.val : ℝ) := by
    have ha : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hb : (0 : ℝ) < nthPrime i.val := by exact_mod_cast (nthPrime_prime i.val).pos
    have hab : (nthPrime i.val : ℝ) ≤ p i := by exact_mod_cast nth_prime_le_sorted p hp hmono i
    exact ⟨(div_lt_one (by linarith)).mpr ha,one_div_le_one_div_of_le hb hab⟩
  have hpos' : 4*(1+reciprocalPowerConstant a)^(2*1+1)*D^a <
      (m : ℝ)*lowerStep (fun i => 1/(nthPrime i : ℝ)) (primeKeep nthPrime)
        (upperMain (fun i => 1/(nthPrime i : ℝ)) (primeKeep nthPrime) (scaledSelbergBase nthPrime) 1) P.card D := by
    change 4*(1+reciprocalPowerConstant a)^3*D^a < (m : ℝ)*referenceLower 1 P.card D
    exact hpos.trans_le (mul_le_mul_of_nonneg_left
      (referenceLower_antitone_prefix 1 P.card k hPk D hkeep) (Nat.cast_nonneg m))
  obtain ⟨j,hj,hjall⟩ := survivor_from_dominating_refinement P.card m q nthPrime nthPrime_prime nthPrime_strictMono
    hq (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hmono.injective r m) D hD a ha 1 hpos'
  refine ⟨j,hj,fun b hb => ?_⟩
  have hrange : b ∈ Set.range p := by simpa only [p,Finset.range_orderEmbOfFin,mem_coe] using hb
  obtain ⟨i,rfl⟩ := hrange
  exact of_decide_eq_false (hjall i)

/-- A uniform Jacobsthal bound, with both its main term and error explicit. -/
theorem isJacobsthalBound_of_refined_main (k m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hkeep : primeKeep nthPrime k D) (a : ℝ) (ha : 1 < a)
    (hpos : 4*(1+reciprocalPowerConstant a)^3*D^a < (m : ℝ)*referenceLower 1 k D) :
    IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  obtain ⟨j,hj,havoid⟩ := prime_survivor_of_refined_main P hP r k m hPk D hD hkeep a ha hpos
  obtain ⟨p,hp,hjp⟩ := hcover j hj
  exact havoid p hp hjp

#print axioms isJacobsthalBound_of_refined_main
end Erdos970.RecursiveSieve.Buchstab
