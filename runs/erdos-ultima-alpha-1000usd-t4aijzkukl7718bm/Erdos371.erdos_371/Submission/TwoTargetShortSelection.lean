import Submission.ShortComplementPattern
import Submission.TwoTargetPatternSelection

/-! Selection for polynomially bounded short-complement observables. The
individual-block mass bound is fixed before the number of blocks is chosen;
the total band mass may depend on that number. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

/-- A fixed-degree short-complement pattern has a small signed correlation
at some block, uniformly in all product cutoffs X_i and bounded targets G. -/
theorem exists_small_power_for_two_target_short_selection (k : ℕ) (Mb ε : ℝ)
    (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (P : Finset ℕ) (A B : ℕ → Finset ℕ) (X : ℕ → ℕ) (G : Bool → ℕ → ℝ) (b : ℕ → Bool),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∀ i j, i < j → j < K → A i ⊆ A j) →
      (∀ i j, i < j → j < K → A j\A i ⊆ P) →
      (∀ i, i < K → B i ⊆ P) →
      (∀ i j, i < j → j < K → Disjoint (B i) (B j)) →
      (∀ i, i < K → (2*∑ p ∈ B i, (1 : ℝ)/p) ≤ Mb) →
      (∀ t n, n < N → |G t n| ≤ 1) →
      ∃ i < K, |(∑ n ∈ range N, G (b i) n*
        localPatternWitness (A i) P (shortComplementPattern (B i) (X i) k) n)/N| < ε := by
  obtain ⟨R,hR,htail⟩ := prime_pattern_polynomial_tail k Mb (ε/2) (by positivity)
  let Q := 1+subsetPolynomial k R
  have hQ : 0 < Q := by dsimp [Q]; linarith [subsetPolynomial_nonneg k R]
  let ε' := ε/(2*Q)
  have hε' : 0 < ε' := by dsimp [ε']; positivity
  let η := ε'^2/16
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨K,hK,hKs⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const
      (show (0 : ℝ) < ε'^2/8 by positivity))).exists
  have hsize : 4*((1 : ℝ)/K+η) < ε'^2 := by dsimp [η]; nlinarith [sq_pos_of_pos hε']
  refine ⟨K,hK,?_⟩
  intro M
  obtain ⟨δ',hδ',hselect⟩ := exists_small_power_for_two_target_odd_pattern_selection M η ε' K hK hη hε' hsize
  let d : ℝ := 1/(4*(k+3 : ℝ))
  let δ := min δ' d
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨δ,lt_min hδ' hd,?_⟩
  filter_upwards [hselect,htail,eventually_ge_atTop (1 : ℕ)] with N hselect htail hN
  intro P A B X G b hP hmass hnest hdiff hBP hdisj hMb hG
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hP' : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ' := by
    intro p hp
    exact ⟨(hP p hp).1,(hP p hp).2.trans
      (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _))⟩
  let F : ℕ → Finset PrimeAtom → ℝ := fun i U => clippedShortComplementPattern (B i) (X i) k R U/Q
  have hF (i : ℕ) (_ : i < K) (U : Finset PrimeAtom) (_ : U ⊆ primeAtoms P) : |F i U| ≤ 1 := by
    dsimp only [F]
    rw [abs_div,abs_of_pos hQ]
    apply (div_le_one hQ).mpr
    exact (clippedShortComplementPattern_abs_le (B i) (X i) k R U).trans
      (by dsimp [Q]; linarith)
  obtain ⟨i,hi,hcorr⟩ := hselect P A B F G b hP' hmass hnest hdiff hF
    (fun i _ U => by dsimp only [F]; rw [clippedShortComplementPattern_odd,neg_div])
    (fun i j hij hj U => by
      dsimp only [F]
      rw [clippedShortComplementPattern_flip_disjoint (B i) (B j) (hdisj i j hij hj)]) hG
  have hmoment := htail (B i) (by
    intro p hp
    have hpp := hP p (hBP i hi hp)
    exact ⟨hpp.1,hpp.2.trans (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _))⟩) (hMb i hi)
  let V : ℕ → ℝ := fun n => G (b i) n*localPatternWitness (A i) P (shortComplementPattern (B i) (X i) k) n
  let W : ℕ → ℝ := fun n => G (b i) n*localPatternWitness (A i) P (clippedShortComplementPattern (B i) (X i) k R) n
  have he : (∑ n ∈ range N, W n)/N =
      Q*((∑ n ∈ range N, G (b i) n*localPatternWitness (A i) P (F i) n)/N) := by
    rw [← mul_div_assoc,mul_sum]
    congr 1
    apply sum_congr rfl
    intro n _
    dsimp [W,F,localPatternWitness]
    field_simp
  have hW : |(∑ n ∈ range N, W n)/N| < ε/2 := by
    rw [he,abs_mul,abs_of_pos hQ]
    have hh := mul_lt_mul_of_pos_left hcorr hQ
    have heps : Q*ε'=ε/2 := by dsimp [ε']; field_simp
    rwa [heps] at hh
  have hpoint (n : ℕ) (hn : n ∈ range N) :
      |V n-W n| ≤ if R ≤ (activePrimeAtoms (B i) n).card then
        subsetPolynomial k (activePrimeAtoms (B i) n).card else 0 := by
    have hg := hG (b i) n (mem_range.mp hn)
    dsimp only [V,W,localPatternWitness]
    rw [← mul_sub,← mul_sub,abs_mul,abs_mul]
    have hp : |naturalBlockParity (A i) n|=1 := blockParity_abs _ _
    rw [hp,one_mul]
    exact ((mul_le_mul_of_nonneg_right hg (abs_nonneg _)).trans_eq (one_mul _)).trans
      (clippedShortComplementPattern_arithmetic_error (B i) P (hBP i hi) (X i) k R n)
  have herr : |(∑ n ∈ range N, V n)/N-(∑ n ∈ range N, W n)/N| < ε/2 := by
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_pos hNr]
    exact ((div_le_div_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans
      (sum_le_sum hpoint)) hNr.le)).trans_lt hmoment
  refine ⟨i,hi,?_⟩
  change |(∑ n ∈ range N, V n)/N| < ε
  have htri := abs_sub_le ((∑ n ∈ range N, V n)/N) ((∑ n ∈ range N, W n)/N) 0
  simp only [sub_zero] at htri
  linarith

#print axioms exists_small_power_for_two_target_short_selection
end Erdos371.FiniteSieve
