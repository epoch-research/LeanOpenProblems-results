import Submission.BuchstabSharpCost
import Submission.BuchstabDominatingTransfer
import Submission.BuchstabIntervalSurvivor

/-! Arbitrary-prime marginal transfer for the exact Selberg cost and its
complete depth-one bound. The Jacobsthal criterion has no extra hypotheses. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

theorem survivor_from_dominating_sharp_refinement (k m : ℕ) (q : Fin k → ℝ)
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (hq : ∀ i, q i < 1 ∧ q i ≤ 1/(p i.val : ℝ))
    (ω : ℕ → Fin k → Bool)
    (herr : ∀ T : Finset (Fin k),
      |(∑ j ∈ range m, hitMonomial T (ω j))-(m : ℝ)*∏ i ∈ T, q i| ≤ 1)
    (D : ℝ) (n : ℕ)
    (hpos : lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSharpSelbergCost p) n) k D <
      (m : ℝ)*lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
        (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSelbergBase p) n) k D) :
    ∃ j < m, ∀ i, ω j i = false := by
  classical
  let q' (i : Fin k) : ℝ := 1/(p i.val : ℝ)
  have hq' (i : Fin k) : q' i ≤ 1 := by
    have hp' : (1 : ℝ) < p i.val := by exact_mod_cast (hp i.val).one_lt
    exact ((div_lt_one (by linarith : (0 : ℝ) < p i.val)).mpr hp').le
  let b (i : Fin k) := (q' i-q i)/(1-q i)
  have hb (i : Fin k) : 0 ≤ b i ∧ b i ≤ 1 := by
    have hd : 0 < 1-q i := sub_pos.mpr (hq i).1
    exact ⟨div_nonneg (sub_nonneg.mpr (hq i).2) hd.le,
      (div_le_one hd).mpr (by linarith [hq' i])⟩
  have hbq (i : Fin k) : b i+(1-b i)*q i = q' i := by
    have hd : 1-q i ≠ 0 := (sub_pos.mpr (hq i).1).ne'
    dsimp [b]
    field_simp
    ring
  let A := (range m) ×ˢ (univ : Finset (Fin k → Bool))
  let w (x : ℕ × (Fin k → Bool)) := probability b x.2
  let v (x : ℕ × (Fin k → Bool)) := extendPattern (fun i => ω x.1 i || x.2 i)
  have hw : ∀ x ∈ A, 0 ≤ w x := by
    intro x hx
    apply prod_nonneg
    intro i hi
    split_ifs
    · exact (hb i).1
    · exact sub_nonneg.mpr (hb i).2
  have hmom (T : Finset ℕ) (hT : T ⊆ range k) :
      |moment A w v T-(m : ℝ)*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1 := by
    have hh := added_hits_moment_error b q hb m ω herr (liftSet k T)
    simp_rw [hbq] at hh
    dsimp only [q'] at hh
    rw [liftSet_prod T hT (fun i => 1/(p i : ℝ))] at hh
    simpa only [A,w,v,boosted_moment] using hh
  obtain ⟨x,hx,hxall⟩ := survivor_of_scaled_sharp_refinement A w v p hp hmono
    (m : ℝ) D k (Nat.cast_nonneg m) hw hmom n hpos
  refine ⟨x.1,mem_range.mp (mem_product.mp hx).1,fun i => ?_⟩
  have hh := hxall i.val i.isLt
  simp only [v,extendPattern,i.isLt,↓reduceDIte] at hh
  exact (Bool.or_eq_false_iff.mp hh).1

theorem prime_survivor_of_sharp_refinement (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (k m : ℕ) (hPk : P.card ≤ k) (D : ℝ) (hD : 0 ≤ D)
    (hkeep : primeKeep nthPrime k D)
    (hpos : sharpRefinementCostConstant*(1+prefixReciprocal nthPrime k)^2*D < (m : ℝ)*referenceLower 1 k D) :
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
  have hpos' : sharpRefinementCostConstant*(1+prefixReciprocal nthPrime k)^2*D <
      (m : ℝ)*lowerStep (fun i => 1/(nthPrime i : ℝ)) (primeKeep nthPrime)
        (upperMain (fun i => 1/(nthPrime i : ℝ)) (primeKeep nthPrime) (scaledSelbergBase nthPrime) 1) P.card D := by
    change sharpRefinementCostConstant*(1+prefixReciprocal nthPrime k)^2*D < (m : ℝ)*referenceLower 1 P.card D
    exact hpos.trans_le (mul_le_mul_of_nonneg_left
      (referenceLower_antitone_prefix 1 P.card k hPk D hkeep) (Nat.cast_nonneg m))
  have herrpos := (sharp_lower_one_le_linear P.card k hPk D hD).trans_lt hpos'
  obtain ⟨j,hj,hjall⟩ := survivor_from_dominating_sharp_refinement P.card m q nthPrime nthPrime_prime nthPrime_strictMono
    hq (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hmono.injective r m) D 1 herrpos
  refine ⟨j,hj,fun b hb => ?_⟩
  have hrange : b ∈ Set.range p := by simpa only [p,Finset.range_orderEmbOfFin,mem_coe] using hb
  obtain ⟨i,rfl⟩ := hrange
  exact of_decide_eq_false (hjall i)

/-- A uniform Jacobsthal bound, with both its main term and error explicit. -/
theorem isJacobsthalBound_of_sharp_refinement (k m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hkeep : primeKeep nthPrime k D)
    (hpos : sharpRefinementCostConstant*(1+prefixReciprocal nthPrime k)^2*D < (m : ℝ)*referenceLower 1 k D) :
    IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  obtain ⟨j,hj,havoid⟩ := prime_survivor_of_sharp_refinement P hP r k m hPk D hD hkeep hpos
  obtain ⟨p,hp,hjp⟩ := hcover j hj
  exact havoid p hp hjp



#print axioms survivor_from_dominating_sharp_refinement
#print axioms isJacobsthalBound_of_sharp_refinement
end Erdos970.RecursiveSieve.Buchstab
