import Submission.PrimeBlockWitness

/-! Selection among moving, nested prime-block witnesses. All endpoints and
witness families may vary with N, subject to the explicit local hypotheses. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

/-- A single witness has small signed correlation with an arbitrary bounded
target. Small-power prime-pattern transfer and finite Bessel selection are
combined at the SAME natural endpoint. -/
theorem exists_small_power_for_block_selection (M η ε : ℝ) (K : ℕ)
    (hK : 0<K) (hη : 0<η) (hε : 0<ε) (hsize : (1 : ℝ)/K+η<ε^2) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (P : Finset ℕ) (A B : ℕ → Finset ℕ) (G : ℕ → ℝ),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (N : ℝ)^δ) →
      (2*∑ p ∈ P, (1 : ℝ)/p) ≤ M →
      (∀ i j, i<j → j<K → A i ⊆ A j) →
      (∀ i j, i<j → j<K → A j\A i ⊆ P) →
      (∀ i, i<K → B i ⊆ P) →
      (∀ i j, i<j → j<K → Disjoint (B i) (B j)) →
      (∀ n<N, |G n|≤1) →
      ∃ i<K, |(∑ n ∈ range N, G n*primeBlockWitness (A i) (B i) n)/N|<ε := by
  obtain ⟨δ,hδ,hblock⟩ := exists_small_power_for_block_pair M η hη
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hblock,eventually_gt_atTop (0 : ℕ)] with N hblock hN
  intro P A B G hP hmass hnest hdiff hB hdisj hG
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hpair (i j : ℕ) (hij : i<j) (hj : j<K) :
      |∑ n ∈ range N, primeBlockWitness (A i) (B i) n*primeBlockWitness (A j) (B j) n|≤η*N := by
    have h := hblock P (A j\A i) (B i) (B j) hP hmass (hdisj i j hij hj)
    have he (n : ℕ) := primeBlockWitness_product (A i) (B i) (A j) (B j) P
      (hnest i j hij hj) (hdiff i j hij hj) (hB i (hij.trans hj)) (hB j hj) n
    simp_rw [← he] at h
    rw [abs_div,abs_of_pos hNr] at h
    exact ((div_lt_iff₀ hNr).mp h).le
  obtain ⟨i,hi,hcorr⟩ := finite_bessel_selection (range K) (nonempty_range_iff.mpr hK.ne')
    (range N) (nonempty_range_iff.mpr hN.ne') G (fun i => primeBlockWitness (A i) (B i)) η ε
    hη.le hε (by simpa only [card_range] using hsize)
    (fun n hn => hG n (mem_range.mp hn))
    (fun i _ n _ => primeBlockWitness_abs_le (A i) (B i) n)
    (by
      intro i hi j hj hij
      rw [card_range]
      by_cases hlt : i<j
      · exact hpair i j hlt (mem_range.mp hj)
      · have hh := hpair j i (by omega) (mem_range.mp hi)
        simpa only [mul_comm] using hh)
  exact ⟨i,mem_range.mp hi,by simpa only [card_range] using hcorr⟩

#print axioms exists_small_power_for_block_selection
end Erdos371.FiniteSieve
