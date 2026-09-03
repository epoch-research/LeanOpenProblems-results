import Submission.ContinuousIntervalQuantumIteration
import Submission.ContinuousIntervalReference

/-! Uniform prime-set transfer for the integer-threshold recursion. Positivity
remains an explicit premise, not an asserted asymptotic estimate. -/
namespace Erdos970.ContinuousInterval

theorem survivor_of_quantumReferencePositive (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (cells : ℕ → List ℕ) (trigger : ℕ → ℕ) (m : ℕ)
    (hpos : 0 < (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) cells trigger P.card).1 m) :
    ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  classical
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  let p' (i : ℕ) := if h : i < P.card then p ⟨i, h⟩ else 2
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hm : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  have hp' (i : ℕ) (hi : i < P.card) : 1 < p' i := by
    simpa only [p', dif_pos hi] using (hp ⟨i, hi⟩).one_lt
  have hcop (i : ℕ) (hi : i < P.card) (j : ℕ) (hj : j < i) : (p' i).Coprime (p' j) := by
    have hjP : j < P.card := hj.trans hi
    simp only [p', dif_pos hi, dif_pos hjP]
    apply (Nat.coprime_primes (hp ⟨i, hi⟩) (hp ⟨j, hjP⟩)).mpr
    exact ne_of_gt (hm hj)
  have hQ (i : ℕ) (hi : i < P.card) :
      1 / (p' i : ℝ) ≤ (referenceMarginal i : ℝ) ∧ (referenceMarginal i : ℝ) ≤ 1 := by
    have hle := FiniteSelberg.nth_prime_le_sorted p hp hm ⟨i, hi⟩
    have hpos : (0 : ℝ) < Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).pos
    simp only [referenceMarginal, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, p', dif_pos hi]
    exact ⟨one_div_le_one_div_of_le hpos (by exact_mod_cast hle),
      (div_le_one hpos).mpr (by exact_mod_cast (Nat.prime_nth_prime i).one_lt.le)⟩
  obtain ⟨x, hx, hxa⟩ := survivor_of_positive_quantumEnvelope p' (fun i => (referenceMarginal i : ℝ))
    cells trigger P.card hp' hcop hQ m hpos (fun i => r (p' i))
  refine ⟨x, hx, ?_⟩
  intro q hq
  have hrange : q ∈ Set.range p := by
    simpa only [p, Finset.range_orderEmbOfFin, Finset.mem_coe] using hq
  obtain ⟨i, rfl⟩ := hrange
  simpa only [p', dif_pos i.isLt] using hxa i.val i.isLt

/-- Padding to exactly `k` primes turns one numerical reference certificate into
a uniform bound for all sets of at most `k` primes. -/
theorem isJacobsthalBound_of_quantumReferencePositive (cells : ℕ → List ℕ) (trigger : ℕ → ℕ) (k m : ℕ)
    (hpos : 0 < (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) cells trigger k).1 m) :
    IsJacobsthalBound k m := by
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
  obtain ⟨x, hx, hxa⟩ := survivor_of_quantumReferencePositive Q hQ r cells trigger m (hQk ▸ hpos)
  obtain ⟨p, hp, hxp⟩ := hcover x hx
  exact hxa p (hPQ hp) hxp

theorem jacobsthalFunction_le_of_quantumReferencePositive (cells : ℕ → List ℕ) (trigger : ℕ → ℕ) (k m : ℕ)
    (hpos : 0 < (quantumEnvelope (fun i => (referenceMarginal i : ℝ)) cells trigger k).1 m) :
    jacobsthalFunction k ≤ m :=
  (jacobsthalFunction_le_iff k m).mpr (isJacobsthalBound_of_quantumReferencePositive cells trigger k m hpos)

#print axioms isJacobsthalBound_of_quantumReferencePositive
end Erdos970.ContinuousInterval
