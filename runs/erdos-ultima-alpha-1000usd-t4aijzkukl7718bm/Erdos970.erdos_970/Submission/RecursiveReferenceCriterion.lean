import Submission.RecursiveSieveRational
import Submission.SieveReferenceCriterion

/-! A sufficient, purely numerical recursive criterion for the Jacobsthal conjecture. -/
namespace Erdos970.RecursiveSieve
open FiniteSelberg

/-- Positivity of the rational first-hit sieve at the first `k` primes. -/
def ReferencePositive (k m : ℕ) : Prop :=
  0 < (linearEnvelope (fun i => 1 / (Nat.nth Nat.Prime i : ℚ)) k (m : ℚ)).1

theorem survivor_of_referencePositive (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) (hpos : ReferencePositive P.card m) :
    ∃ j < m, ∀ p ∈ P, ¬j ≡ r p [MOD p] := by
  classical
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  let q' (i : Fin P.card) := 1 / (Nat.nth Nat.Prime i.val : ℝ)
  have hq (i : Fin P.card) :
      1 / (p i : ℝ) < 1 ∧ 1 / (p i : ℝ) ≤ q' i ∧ q' i ≤ 1 := by
    have ha : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hb : (1 : ℝ) < Nat.nth Nat.Prime i.val := by
      exact_mod_cast (Nat.prime_nth_prime i.val).one_lt
    have hab : (Nat.nth Nat.Prime i.val : ℝ) ≤ p i := by
      exact_mod_cast nth_prime_le_sorted p hp hmono i
    refine ⟨(div_lt_iff₀ (by linarith : (0 : ℝ) < p i)).mpr (by linarith),
      one_div_le_one_div_of_le (by linarith) hab, ?_⟩
    exact (div_le_one (by linarith : (0 : ℝ) < Nat.nth Nat.Prime i.val)).mpr hb.le
  have hr : 0 < (linearEnvelope (extendMarginal q') P.card (m : ℝ)).1 := by
    have hc := congrArg Prod.fst
      (cast_linearEnvelope (fun i => 1 / (Nat.nth Nat.Prime i : ℚ)) P.card (m : ℚ))
    simp only [Prod.map_fst, Rat.cast_natCast, Rat.cast_div, Rat.cast_one] at hc
    have he := linearEnvelope_congr
      (fun i => 1 / (Nat.nth Nat.Prime i : ℝ)) (extendMarginal q') P.card (m : ℝ)
      (fun i hi => by simp [extendMarginal, hi, q'])
    rw [← he, ← hc]
    exact_mod_cast hpos
  obtain ⟨j, hj, hja⟩ := survivor_of_positive_linearEnvelope P.card m
    (fun i => 1 / (p i : ℝ)) q' hq
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hmono.injective r m) hr
  refine ⟨j, hj, ?_⟩
  intro a ha
  have har : a ∈ Set.range p := by
    simpa only [p, Finset.range_orderEmbOfFin, Finset.mem_coe] using ha
  obtain ⟨i, rfl⟩ := har
  exact of_decide_eq_false (hja i)

/-- Padding a prime set shows that a certificate for exactly `k` primes also works
for at most `k` primes. -/
theorem isJacobsthalBound_of_referencePositive (k m : ℕ)
    (hpos : ReferencePositive k m) : IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  obtain ⟨R, hR, hRk⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq k
  have hkPR : k ≤ (P ∪ R).card := by
    rw [← hRk]
    exact Finset.card_le_card Finset.subset_union_right
  obtain ⟨Q, hPQ, hQPR, hQk⟩ :=
    Finset.exists_subsuperset_card_eq Finset.subset_union_left hPk hkPR
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp (hQPR hp) with hp | hp
    · exact hP p hp
    · exact hR hp
  obtain ⟨j, hj, hja⟩ := survivor_of_referencePositive Q hQ r m (hQk ▸ hpos)
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact hja p (hPQ hp) hjp

/-- This is a sufficient route to the original conjecture, with its unproved
uniform numerical estimate exposed as a hypothesis. -/
theorem quadratic_bound_of_referencePositive (D : ℕ) (hD : 0 < D)
    (hpos : ∀ k, 0 < k → ReferencePositive k (D * k ^ 2)) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  apply quadratic_bound_iff_nat.mpr
  exact ⟨D, hD, fun k hk => isJacobsthalBound_of_referencePositive k _ (hpos k hk)⟩

#print axioms survivor_of_referencePositive
#print axioms isJacobsthalBound_of_referencePositive
#print axioms quadratic_bound_of_referencePositive
end Erdos970.RecursiveSieve
