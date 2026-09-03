import Submission.PrimeBlockWitness

/-! Bessel selection for general bounded local odd pattern observables.
The common arithmetic parity factor cancels in every pair of witnesses. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

noncomputable def localPatternWitness (A P : Finset ℕ)
    (F : Finset PrimeAtom → ℝ) (n : ℕ) : ℝ :=
  naturalBlockParity A n*F (activePrimeAtoms P n)

lemma localPatternWitness_abs_le (A P : Finset ℕ) (F : Finset PrimeAtom → ℝ)
    (hF : ∀ T ⊆ primeAtoms P, |F T| ≤ 1) (n : ℕ) :
    |localPatternWitness A P F n| ≤ 1 := by
  rw [localPatternWitness,abs_mul]
  have he : |naturalBlockParity A n|=1 := blockParity_abs _ _
  rw [he,one_mul]
  exact hF _ (activePrimeAtoms_subset P n)

lemma localPatternWitness_product (A C P : Finset ℕ)
    (F H : Finset PrimeAtom → ℝ) (hAC : A ⊆ C) (hCP : C\A ⊆ P) (n : ℕ) :
    localPatternWitness A P F n*localPatternWitness C P H n =
      blockParity (C\A) (activePrimeAtoms P n)*
        F (activePrimeAtoms P n)*H (activePrimeAtoms P n) := by
  unfold localPatternWitness
  calc
    _ = (naturalBlockParity A n*naturalBlockParity C n)*
        F (activePrimeAtoms P n)*H (activePrimeAtoms P n) := by ring
    _ = _ := by
      rw [naturalBlockParity_mul_of_subset A C hAC n,
        naturalBlockParity_locality (C\A) P hCP n]

/-- F_i need not be first-prime colours. It suffices that F_j is odd under
a prime-colour flip which fixes F_i for every earlier i. -/
theorem exists_small_power_for_odd_pattern_selection (M η ε : ℝ) (K : ℕ)
    (hK : 0 < K) (hη : 0 < η) (hε : 0 < ε)
    (hsize : (1 : ℝ)/K+η < ε^2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (P : Finset ℕ) (A B : ℕ → Finset ℕ)
        (F : ℕ → Finset PrimeAtom → ℝ) (G : ℕ → ℝ),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∀ i j, i < j → j < K → A i ⊆ A j) →
      (∀ i j, i < j → j < K → A j\A i ⊆ P) →
      (∀ i, i < K → ∀ T ⊆ primeAtoms P, |F i T| ≤ 1) →
      (∀ i, i < K → ∀ T,
        F i (T.map (primeColourFlip (B i)).toEmbedding) = -F i T) →
      (∀ i j, i < j → j < K → ∀ T,
        F i (T.map (primeColourFlip (B j)).toEmbedding) = F i T) →
      (∀ n < N, |G n| ≤ 1) →
      ∃ i < K, |(∑ n ∈ range N, G n*localPatternWitness (A i) P (F i) n)/N| < ε := by
  obtain ⟨δ,hδ,hpattern⟩ := exists_small_power_for_pattern_symmetry M η hη
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hpattern,eventually_gt_atTop (0 : ℕ)] with N hpattern hN
  intro P A B F G hP hmass hnest hdiff hF hodd hfix hG
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpair (i j : ℕ) (hij : i < j) (hj : j < K) :
      |∑ n ∈ range N, localPatternWitness (A i) P (F i) n*
        localPatternWitness (A j) P (F j) n| ≤ η*N := by
    let V : Finset PrimeAtom → ℝ := fun T => blockParity (A j\A i) T*F i T*F j T
    have hV (T : Finset PrimeAtom) (hT : T ⊆ primeAtoms P) : |V T| ≤ 1 := by
      dsimp only [V]
      rw [abs_mul,abs_mul,blockParity_abs,one_mul]
      exact mul_le_one₀ (hF i (hij.trans hj) T hT) (abs_nonneg _) (hF j hj T hT)
    have hVo (T : Finset PrimeAtom) :
        V (T.map (primeColourFlip (B j)).toEmbedding) = -V T := by
      dsimp only [V]
      rw [blockParity_flip,hfix i j hij hj T,hodd j hj T,mul_neg]
    have h := hpattern P (primeColourFlip (B j)) V hP hmass
      (primeColourFlip_fst _) (primeColourFlip_atoms _ _) hV hVo
    have he (n : ℕ) := localPatternWitness_product (A i) (A j) P (F i) (F j)
      (hnest i j hij hj) (hdiff i j hij hj) n
    change |(∑ n ∈ range N, blockParity (A j\A i) (activePrimeAtoms P n)*
      F i (activePrimeAtoms P n)*F j (activePrimeAtoms P n))/N| < η at h
    simp_rw [← he] at h
    rw [abs_div,abs_of_pos hNr] at h
    exact ((div_lt_iff₀ hNr).mp h).le
  obtain ⟨i,hi,hcorr⟩ := finite_bessel_selection (range K) (nonempty_range_iff.mpr hK.ne')
    (range N) (nonempty_range_iff.mpr hN.ne') G (fun i => localPatternWitness (A i) P (F i)) η ε
    hη.le hε (by simpa only [card_range] using hsize)
    (fun n hn => hG n (mem_range.mp hn))
    (fun i hi n _ => localPatternWitness_abs_le (A i) P (F i) (hF i (mem_range.mp hi)) n)
    (by
      intro i hi j hj hij
      rw [card_range]
      by_cases hlt : i < j
      · exact hpair i j hlt (mem_range.mp hj)
      · have hh := hpair j i (by omega) (mem_range.mp hi)
        simpa only [mul_comm] using hh)
  exact ⟨i,mem_range.mp hi,by simpa only [card_range] using hcorr⟩

#print axioms exists_small_power_for_odd_pattern_selection
end Erdos371.FiniteSieve
