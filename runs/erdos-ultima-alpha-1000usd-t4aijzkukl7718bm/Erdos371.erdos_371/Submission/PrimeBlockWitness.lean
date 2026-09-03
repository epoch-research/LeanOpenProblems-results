import Submission.PrimeBlockColour
import Submission.FiniteBesselSelection

/-! Locality and parity cancellation for arithmetic prime-block witnesses.
The common low-prime parity drops out of products of nested witnesses. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

lemma activeBlockPrimes_congr (B : Finset ℕ) (T U : Finset PrimeAtom)
    (h : ∀ p ∈ B, ∀ b : Bool, (p,b) ∈ T ↔ (p,b) ∈ U) :
    activeBlockPrimes B T = activeBlockPrimes B U := by
  apply filter_congr
  intro p hp
  rw [h p hp false,h p hp true]

lemma atomColour_congr (p : ℕ) (T U : Finset PrimeAtom)
    (h : ∀ b : Bool, (p,b) ∈ T ↔ (p,b) ∈ U) : atomColour p T=atomColour p U := by
  simp only [atomColour,h true,h false]

lemma firstBlockColour_congr (B : Finset ℕ) (T U : Finset PrimeAtom)
    (h : ∀ p ∈ B, ∀ b : Bool, (p,b) ∈ T ↔ (p,b) ∈ U) :
    firstBlockColour B T=firstBlockColour B U := by
  unfold firstBlockColour
  simp only [activeBlockPrimes_congr B T U h]
  split_ifs with hu
  · exact atomColour_congr _ T U (h _ (mem_filter.mp ((activeBlockPrimes B U).min'_mem hu)).1)
  · rfl

lemma activePrimeAtoms_locality (B P : Finset ℕ) (hBP : B ⊆ P) (n : ℕ) :
    ∀ p ∈ B, ∀ b : Bool, (p,b) ∈ activePrimeAtoms B n ↔ (p,b) ∈ activePrimeAtoms P n := by
  intro p hp b
  simp only [activePrimeAtoms,mem_filter,primeAtoms,mem_product,mem_univ,and_true,
    hp,hBP hp,true_and]

noncomputable def naturalBlockParity (B : Finset ℕ) (n : ℕ) : ℝ :=
  blockParity B (activePrimeAtoms B n)

noncomputable def naturalFirstBlockColour (B : Finset ℕ) (n : ℕ) : ℝ :=
  firstBlockColour B (activePrimeAtoms B n)

noncomputable def primeBlockWitness (A B : Finset ℕ) (n : ℕ) : ℝ :=
  naturalBlockParity A n*naturalFirstBlockColour B n

lemma naturalBlockParity_locality (B P : Finset ℕ) (hBP : B ⊆ P) (n : ℕ) :
    naturalBlockParity B n=blockParity B (activePrimeAtoms P n) := by
  unfold naturalBlockParity blockParity
  rw [activeBlockPrimes_congr B _ _ (activePrimeAtoms_locality B P hBP n)]

lemma naturalFirstBlockColour_locality (B P : Finset ℕ) (hBP : B ⊆ P) (n : ℕ) :
    naturalFirstBlockColour B n=firstBlockColour B (activePrimeAtoms P n) :=
  firstBlockColour_congr B _ _ (activePrimeAtoms_locality B P hBP n)

lemma activeBlockPrimes_mono (A B : Finset ℕ) (hAB : A ⊆ B) (T : Finset PrimeAtom) :
    activeBlockPrimes A T ⊆ activeBlockPrimes B T := by
  intro p hp
  exact mem_filter.mpr ⟨hAB (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩

lemma activeBlockPrimes_sdiff (A B : Finset ℕ) (T : Finset PrimeAtom) :
    activeBlockPrimes (B\A) T=activeBlockPrimes B T\activeBlockPrimes A T := by
  ext p
  simp only [activeBlockPrimes,mem_filter,Finset.mem_sdiff]
  tauto

lemma blockParity_mul_of_subset (A B : Finset ℕ) (hAB : A ⊆ B) (T : Finset PrimeAtom) :
    blockParity A T*blockParity B T=blockParity (B\A) T := by
  have hc := card_sdiff_add_card_eq_card (activeBlockPrimes_mono A B hAB T)
  rw [← activeBlockPrimes_sdiff A B T] at hc
  unfold blockParity
  rw [← hc,pow_add]
  have hs : ((-1 : ℝ)^(activeBlockPrimes A T).card)^2=1 := by
    rw [← pow_mul,mul_comm _ 2,pow_mul]
    norm_num
  calc
    _ = ((-1 : ℝ)^(activeBlockPrimes A T).card)^2*
        (-1 : ℝ)^(activeBlockPrimes (B\A) T).card := by ring
    _ = _ := by rw [hs,one_mul]

lemma naturalBlockParity_mul_of_subset (A B : Finset ℕ) (hAB : A ⊆ B) (n : ℕ) :
    naturalBlockParity A n*naturalBlockParity B n=naturalBlockParity (B\A) n := by
  rw [naturalBlockParity_locality A B hAB n,
    naturalBlockParity_locality B B Subset.rfl n,
    naturalBlockParity_locality (B\A) B sdiff_subset n]
  exact blockParity_mul_of_subset A B hAB _

lemma primeBlockWitness_abs_le (A B : Finset ℕ) (n : ℕ) : |primeBlockWitness A B n|≤1 := by
  simp only [primeBlockWitness,naturalBlockParity,naturalFirstBlockColour,abs_mul,blockParity_abs,one_mul]
  exact firstBlockColour_abs_le _ _

/-- Only the intermediate parity primes and the two first-colour blocks
are needed to calculate the product of two witnesses. -/
theorem primeBlockWitness_product (A B C D P : Finset ℕ) (hAC : A ⊆ C)
    (hCP : C\A ⊆ P) (hBP : B ⊆ P) (hDP : D ⊆ P) (n : ℕ) :
    primeBlockWitness A B n*primeBlockWitness C D n =
      blockPairObservable (C\A) B D (activePrimeAtoms P n) := by
  unfold primeBlockWitness
  rw [show naturalBlockParity A n*naturalFirstBlockColour B n*
      (naturalBlockParity C n*naturalFirstBlockColour D n) =
      (naturalBlockParity A n*naturalBlockParity C n)*
        naturalFirstBlockColour B n*naturalFirstBlockColour D n by ring]
  rw [naturalBlockParity_mul_of_subset A C hAC n,
    naturalBlockParity_locality (C\A) P hCP n,
    naturalFirstBlockColour_locality B P hBP n,naturalFirstBlockColour_locality D P hDP n]
  rfl

#print axioms primeBlockWitness_product
end Erdos371.FiniteSieve
