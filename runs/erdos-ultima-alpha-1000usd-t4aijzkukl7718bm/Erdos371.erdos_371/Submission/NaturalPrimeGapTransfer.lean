import Submission.CyclicPrimeGapTransfer
import Submission.CyclicBoundaryTransfer

/-! Entropy-based prime-gap transfer for ordinary natural averages. This bounds
the conditioned-minus-unconditioned discrepancy only; it does not assert that
natural adjacent comparison averages converge. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology

lemma abs_finset_average_le {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (F : ι → ℝ) (B : ℝ) (hF : ∀ i ∈ S, |F i| ≤ B) :
    |(∑ i ∈ S, F i)/(S.card : ℝ)| ≤ B := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  rw [abs_div, abs_of_pos hcard]
  apply (div_le_iff₀ hcard).mpr
  calc
    _ ≤ ∑ i ∈ S, |F i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ S, B := sum_le_sum hF
    _ = _ := by simp [mul_comm]

lemma natural_cyclic_rounded_error {A : Type*} (M N q B Q : ℕ) [NeZero M]
    (hMN : M ≤ N) (hhalf : N ≤ 2*M) (htail : N-M ≤ Q) (hqB : q ≤ B) (hBM : B ≤ M)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |naturalGapDiscrepancy N q L C-cyclicGapDiscrepancy M q (fun x => L x.val) C| ≤
      (2*(B+1 : ℝ)*Q+4*B*(B+1 : ℝ))/N := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le hM hMN
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hp : (q : ℝ) ≤ B := by exact_mod_cast hqB
  have he := natural_gap_endpoint_error M N q hM hMN L C hC
  have hc := cyclic_natural_gap_error M q (hqB.trans hBM) L C hC
  have he' : 2*(q+1 : ℝ)*(N-M : ℕ)/N ≤ 2*(B+1 : ℝ)*Q/N := by
    gcongr
  have hnum : 2*(q : ℝ)*(q+1)/M ≤ 2*(B : ℝ)*(B+1)/M := by gcongr
  have hdiv : 1/(M : ℝ) ≤ 2/(N : ℝ) := by
    apply (div_le_div_iff₀ hMr hNr).mpr
    simpa only [one_mul] using (show (N : ℝ) ≤ 2*M by exact_mod_cast hhalf)
  have hc' : 2*(q : ℝ)*(q+1)/M ≤ 4*(B : ℝ)*(B+1)/N := by
    calc
      _ ≤ 2*(B : ℝ)*(B+1)/M := hnum
      _ = (2*(B : ℝ)*(B+1))*(1/M) := by ring
      _ ≤ (2*(B : ℝ)*(B+1))*(2/N) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  calc
    _ ≤ |naturalGapDiscrepancy N q L C-naturalGapDiscrepancy M q L C|+
        |naturalGapDiscrepancy M q L C-cyclicGapDiscrepancy M q (fun x => L x.val) C| :=
      abs_sub_le _ _ _
    _ ≤ 2*(B+1 : ℝ)*Q/N+4*(B : ℝ)*(B+1)/N := by
      apply add_le_add (he.trans he')
      rw [abs_sub_comm]
      exact hc.trans hc'
    _ = _ := by ring

/-- The horizon is uniform over arbitrary finite label sequences, including
sequences that themselves depend on the natural endpoint N. The selected scale
works simultaneously for every unit-bounded pair observable. -/
theorem natural_prime_gap_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ L : ℕ → A, ∃ n < K,
      ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
        |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n), naturalGapDiscrepancy N p L C) /
          (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨K,hK,htransfer⟩ := cyclic_prime_gap_transfer (A := A) H₀ hH₀ (ε/2) (by positivity)
  let Q : ℕ := ∏ n ∈ range K, primorial (factorialScale H₀ n)
  let B : ℕ := (range K).sup (factorialScale H₀)
  let D : ℝ := 2*(B+1 : ℝ)*Q+4*B*(B+1 : ℝ)
  have hQ : 0 < Q := prod_pos fun _ _ => primorial_pos _
  have ht := tendsto_const_div_atTop_nhds_zero_nat D
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_ge_atTop (2*Q+2*B),
    ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)] with N hN hsmall
  intro L
  let M := Q*(N/Q)
  have hdecomp : N = M+N%Q := (Nat.div_add_mod N Q).symm
  have hmod : N%Q < Q := Nat.mod_lt N hQ
  have hMN : M ≤ N := Nat.mul_div_le N Q
  have hM : 0 < M := by omega
  have hBM : B ≤ M := by omega
  have hhalf : N ≤ 2*M := by omega
  have htail : N-M ≤ Q := by omega
  letI : NeZero M := ⟨hM.ne'⟩
  have hQM : Q ∣ M := dvd_mul_right Q (N/Q)
  obtain ⟨n,hn,hscale⟩ := htransfer M hQM (fun x => L x.val)
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  have herr : |(∑ p ∈ S, (naturalGapDiscrepancy N p L C-
      cyclicGapDiscrepancy M p (fun x => L x.val) C))/(S.card : ℝ)| ≤ D/N := by
    apply abs_finset_average_le S hS
    intro p hp
    have hpb := (mem_halfBlockPrimes.mp hp).2
    have hpB : p ≤ B := by omega
    exact natural_cyclic_rounded_error M N p B Q hMN hhalf htail hpB hBM L C hC
  have hcyc := hscale C hC
  change |(∑ p ∈ S, naturalGapDiscrepancy N p L C)/(S.card : ℝ)| < ε
  rw [sum_sub_distrib, sub_div] at herr
  have htri := abs_sub_le
    ((∑ p ∈ S, naturalGapDiscrepancy N p L C)/(S.card : ℝ))
    ((∑ p ∈ S, cyclicGapDiscrepancy M p (fun x => L x.val) C)/(S.card : ℝ)) 0
  simp only [sub_zero] at htri
  change |(∑ p ∈ S, cyclicGapDiscrepancy M p (fun x => L x.val) C)/(S.card : ℝ)| < ε/2 at hcyc
  linarith

#print axioms natural_prime_gap_transfer
end Erdos371.FiniteInformation
