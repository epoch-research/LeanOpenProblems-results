import Submission.PrimePatternApproximation

/-! First-colour block observables and the reflection symmetry needed for
prime-block orthogonality. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

noncomputable def atomColour (p : ℕ) (T : Finset PrimeAtom) : ℝ :=
  (if (p,true) ∈ T then 1 else 0)-(if (p,false) ∈ T then 1 else 0)

def activeBlockPrimes (B : Finset ℕ) (T : Finset PrimeAtom) : Finset ℕ :=
  B.filter (fun p => (p,false) ∈ T ∨ (p,true) ∈ T)

noncomputable def firstBlockColour (B : Finset ℕ) (T : Finset PrimeAtom) : ℝ :=
  if h : (activeBlockPrimes B T).Nonempty then
    atomColour ((activeBlockPrimes B T).min' h) T else 0

noncomputable def blockParity (B : Finset ℕ) (T : Finset PrimeAtom) : ℝ :=
  (-1 : ℝ)^(activeBlockPrimes B T).card

lemma atomColour_abs_le (p : ℕ) (T : Finset PrimeAtom) : |atomColour p T| ≤ 1 := by
  unfold atomColour
  split_ifs <;> norm_num

lemma firstBlockColour_abs_le (B : Finset ℕ) (T : Finset PrimeAtom) : |firstBlockColour B T| ≤ 1 := by
  unfold firstBlockColour
  split_ifs
  · exact atomColour_abs_le _ _
  · norm_num

lemma blockParity_abs (B : Finset ℕ) (T : Finset PrimeAtom) : |blockParity B T|=1 := by
  simp only [blockParity,abs_pow,abs_neg,abs_one,one_pow]

lemma activeBlockPrimes_flip (B R : Finset ℕ) (T : Finset PrimeAtom) :
    activeBlockPrimes B (T.map (primeColourFlip R).toEmbedding) = activeBlockPrimes B T := by
  ext p
  simp only [activeBlockPrimes,mem_filter,mem_map_equiv,primeColourFlip]
  by_cases hp : p ∈ R <;> simp [hp,or_comm]

lemma atomColour_flip_of_mem (R : Finset ℕ) (T : Finset PrimeAtom) (p : ℕ) (hp : p ∈ R) :
    atomColour p (T.map (primeColourFlip R).toEmbedding) = -atomColour p T := by
  simp [atomColour,mem_map_equiv,primeColourFlip,hp,neg_sub]

lemma atomColour_flip_of_notMem (R : Finset ℕ) (T : Finset PrimeAtom) (p : ℕ) (hp : p ∉ R) :
    atomColour p (T.map (primeColourFlip R).toEmbedding) = atomColour p T := by
  simp [atomColour,mem_map_equiv,primeColourFlip,hp]

lemma firstBlockColour_flip (B R : Finset ℕ) (T : Finset PrimeAtom) (hBR : B ⊆ R) :
    firstBlockColour B (T.map (primeColourFlip R).toEmbedding) = -firstBlockColour B T := by
  unfold firstBlockColour
  simp only [activeBlockPrimes_flip]
  split_ifs with h
  · exact atomColour_flip_of_mem R T _ (hBR ((mem_filter.mp ((activeBlockPrimes B T).min'_mem h)).1))
  · simp

lemma firstBlockColour_flip_disjoint (B R : Finset ℕ) (T : Finset PrimeAtom) (hBR : Disjoint B R) :
    firstBlockColour B (T.map (primeColourFlip R).toEmbedding) = firstBlockColour B T := by
  unfold firstBlockColour
  simp only [activeBlockPrimes_flip]
  split_ifs with h
  · apply atomColour_flip_of_notMem
    exact disjoint_left.mp hBR ((mem_filter.mp ((activeBlockPrimes B T).min'_mem h)).1)
  · rfl

lemma blockParity_flip (B R : Finset ℕ) (T : Finset PrimeAtom) :
    blockParity B (T.map (primeColourFlip R).toEmbedding) = blockParity B T := by
  simp only [blockParity,activeBlockPrimes_flip]

noncomputable def blockPairObservable (A B C : Finset ℕ) (T : Finset PrimeAtom) : ℝ :=
  blockParity A T*firstBlockColour B T*firstBlockColour C T

lemma blockPairObservable_abs_le (A B C : Finset ℕ) (T : Finset PrimeAtom) :
    |blockPairObservable A B C T| ≤ 1 := by
  unfold blockPairObservable
  rw [abs_mul,abs_mul,blockParity_abs,one_mul]
  exact mul_le_one₀ (firstBlockColour_abs_le B T) (abs_nonneg _) (firstBlockColour_abs_le C T)

lemma blockPairObservable_odd (A B C : Finset ℕ) (hBC : Disjoint B C) (T : Finset PrimeAtom) :
    blockPairObservable A B C (T.map (primeColourFlip C).toEmbedding) = -blockPairObservable A B C T := by
  simp only [blockPairObservable,blockParity_flip,firstBlockColour_flip_disjoint B C T hBC,
    firstBlockColour_flip C C T Subset.rfl,mul_neg]

/-- Quantitative natural-prefix orthogonality for disjoint first-colour
blocks, with an arbitrary additional block-parity factor. -/
theorem exists_small_power_for_block_pair (M ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop, ∀ (P A B C : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M → Disjoint B C →
      |(∑ n ∈ range N, blockPairObservable A B C (activePrimeAtoms P n))/N| < ε := by
  obtain ⟨δ,hδ,h⟩ := exists_small_power_for_pattern_symmetry M ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [h] with N hN
  intro P A B C hP hmass hBC
  exact hN P (primeColourFlip C) (blockPairObservable A B C) hP hmass
    (primeColourFlip_fst C) (primeColourFlip_atoms C P)
    (fun T _ => blockPairObservable_abs_le A B C T) (blockPairObservable_odd A B C hBC)

#print axioms exists_small_power_for_block_pair
end Erdos371.FiniteSieve
