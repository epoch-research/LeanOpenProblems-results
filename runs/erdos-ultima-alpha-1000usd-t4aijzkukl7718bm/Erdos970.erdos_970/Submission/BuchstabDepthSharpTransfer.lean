import Submission.BuchstabSharpTransfer

/-! Transfer with a uniform exact sharp error budget. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

theorem prime_survivor_of_depth_sharp_cost (d : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (k m : ℕ) (hPk : P.card ≤ k) (D : ℝ) (hD : 0 ≤ D)
    (hkeep : primeKeep nthPrime k D)
    (E : ℝ)
    (hcost : ∀ j : ℕ, j ≤ k → lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) d) j D ≤ E)
    (hpos : E < (m : ℝ)*referenceLower d k D) :
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
  have hpos' : E <
      (m : ℝ)*lowerStep (fun i => 1/(nthPrime i : ℝ)) (primeKeep nthPrime)
        (upperMain (fun i => 1/(nthPrime i : ℝ)) (primeKeep nthPrime) (scaledSelbergBase nthPrime) d) P.card D := by
    change E < (m : ℝ)*referenceLower d P.card D
    exact hpos.trans_le (mul_le_mul_of_nonneg_left
      (referenceLower_antitone_prefix d P.card k hPk D hkeep) (Nat.cast_nonneg m))
  have herrpos := (hcost P.card hPk).trans_lt hpos'
  obtain ⟨j,hj,hjall⟩ := survivor_from_dominating_sharp_refinement P.card m q nthPrime nthPrime_prime nthPrime_strictMono
    hq (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hmono.injective r m) D d herrpos
  refine ⟨j,hj,fun b hb => ?_⟩
  have hrange : b ∈ Set.range p := by simpa only [p,Finset.range_orderEmbOfFin,mem_coe] using hb
  obtain ⟨i,rfl⟩ := hrange
  exact of_decide_eq_false (hjall i)

/-- A uniform Jacobsthal bound, with both its main term and error explicit. -/
theorem isJacobsthalBound_of_depth_sharp_cost (d : ℕ) (k m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hkeep : primeKeep nthPrime k D)
    (E : ℝ)
    (hcost : ∀ j : ℕ, j ≤ k → lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) d) j D ≤ E)
    (hpos : E < (m : ℝ)*referenceLower d k D) :
    IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  obtain ⟨j,hj,havoid⟩ := prime_survivor_of_depth_sharp_cost d P hP r k m hPk D hD hkeep E hcost hpos
  obtain ⟨p,hp,hjp⟩ := hcover j hj
  exact havoid p hp hjp


#print axioms isJacobsthalBound_of_depth_sharp_cost
end Erdos970.RecursiveSieve.Buchstab
