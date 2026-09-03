import Submission.MixtureCyclicPrimeTransfer
import Submission.HarmonicPrefixMixture
import Submission.NaturalPrimeGapTransfer

/-! Harmonic prime-gap transfer from one entropy selection on a positive
mixture of rounded cycles. Every rounding cost is explicitly integrated. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

lemma mean_const_mul {ι : Type*} [Fintype ι] (ρ : Law ι) (c : ℝ) (F : ι → ℝ) :
    mean ρ (fun i => c*F i) = c*mean ρ F := by
  simp only [mean,mul_sum]
  apply sum_congr rfl
  intro i _
  ring

lemma abs_mean_le_mean_abs {ι : Type*} [Fintype ι] (ρ : Law ι) (F : ι → ℝ) :
    |mean ρ F| ≤ mean ρ (fun i => |F i|) := by
  exact (abs_sum_le_sum_abs _ _).trans_eq (by
    simp only [mean,abs_mul,abs_of_nonneg (ρ.nonneg _)])

lemma mean_mono {ι : Type*} [Fintype ι] (ρ : Law ι) (F G : ι → ℝ)
    (h : ∀ i, F i ≤ G i) : mean ρ F ≤ mean ρ G :=
  sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (ρ.nonneg i))

noncomputable def harmonicRangeMean (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  (∑ n ∈ range N, F n/(n+1 : ℝ))/(harmonic N : ℝ)

noncomputable def harmonicRangeGapDiscrepancy {A : Type*}
    (N q : ℕ) (L : ℕ → A) (C : A → A → ℝ) : ℝ :=
  q*harmonicRangeMean N (fun n => if q ∣ n then C (L n) (L (n+q)) else 0) -
    harmonicRangeMean N (fun n => C (L n) (L (n+q)))

lemma harmonicRangeGapDiscrepancy_mixture {A : Type*}
    (N q : ℕ) (L : ℕ → A) (C : A → A → ℝ) :
    mean (harmonicPrefixLaw N) (fun i => naturalGapDiscrepancy (harmonicPrefixLength N i) q L C) =
      harmonicRangeGapDiscrepancy (N+1) q L C := by
  simp only [naturalGapDiscrepancy,mean_sub,mean_const_mul,harmonicPrefixLaw_representation,
    harmonicRangeGapDiscrepancy,harmonicRangeMean]

lemma natural_cyclic_round_up_error {A : Type*} (k M q B T : ℕ) [NeZero M]
    (hk : 0 < k) (hkM : k ≤ M) (htail : M-k ≤ T) (hqB : q ≤ B) (hBM : B ≤ M)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |naturalGapDiscrepancy k q L C-cyclicGapDiscrepancy M q (fun x => L x.val) C| ≤
      (2*(B+1 : ℝ)*T+2*B*(B+1 : ℝ))/k := by
  have hM : 0 < M := hk.trans_le hkM
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have he := natural_gap_endpoint_error k M q hk hkM L C hC
  rw [abs_sub_comm] at he
  have hc := cyclic_natural_gap_error M q (hqB.trans hBM) L C hC
  rw [abs_sub_comm] at hc
  have he' : 2*(q+1 : ℝ)*(M-k : ℕ)/M ≤ 2*(B+1 : ℝ)*T/k := by
    calc
      _ ≤ 2*(B+1 : ℝ)*T/M := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hkr (by exact_mod_cast hkM)
  have hc' : 2*(q : ℝ)*(q+1)/M ≤ 2*(B : ℝ)*(B+1)/k := by
    calc
      _ ≤ 2*(B : ℝ)*(B+1)/M := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hkr (by exact_mod_cast hkM)
  calc
    _ ≤ |naturalGapDiscrepancy k q L C-naturalGapDiscrepancy M q L C|+
      |naturalGapDiscrepancy M q L C-cyclicGapDiscrepancy M q (fun x => L x.val) C| :=
        abs_sub_le _ _ _
    _ ≤ 2*(B+1 : ℝ)*T/k+2*(B : ℝ)*(B+1)/k := add_le_add (he.trans he') (hc.trans hc')
    _ = _ := by ring

/-- Uniform harmonic discrepancy transfer. The alphabet, tolerance and base
scale determine the finite horizon BEFORE the endpoint and labels are chosen. -/
theorem harmonic_range_prime_gap_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ L : ℕ → A, ∃ n < K,
      ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
        |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
          harmonicRangeGapDiscrepancy (N+1) p L C) /
            (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  classical
  obtain ⟨K,hK,htransfer⟩ := mixture_cyclic_prime_gap_transfer (A := A) H₀ hH₀ (ε/2) (by positivity)
  let Q : ℕ := ∏ n ∈ range K, primorial (factorialScale H₀ n)
  let B : ℕ := (range K).sup (factorialScale H₀)
  let T : ℕ := Q*(B+1)
  let D : ℝ := 2*(B+1 : ℝ)*T+2*B*(B+1 : ℝ)
  have hQ : 0 < Q := prod_pos (fun _ _ => primorial_pos _)
  have ht : Tendsto (fun N : ℕ => D/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  refine ⟨K,hK,?_⟩
  filter_upwards [ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with N hsmall
  intro L
  let M (i : Fin (N+1)) := Q*(harmonicPrefixLength N i/Q+B+1)
  have hprops (i : Fin (N+1)) :
      harmonicPrefixLength N i ≤ M i ∧ B ≤ M i ∧ M i-harmonicPrefixLength N i ≤ T := by
    have hd := Nat.div_add_mod (harmonicPrefixLength N i) Q
    have hm := Nat.mod_lt (harmonicPrefixLength N i) hQ
    have hB : B ≤ Q*(B+1) := by nlinarith
    have hme : M i = Q*(harmonicPrefixLength N i/Q)+Q*(B+1) := by dsimp [M]; ring
    dsimp [T]
    rw [hme]
    constructor
    · nlinarith
    constructor <;> omega
  have hM (i : Fin (N+1)) : 0 < M i :=
    (harmonicPrefixLength_pos N i).trans_le (hprops i).1
  letI (i : Fin (N+1)) : NeZero (M i) := ⟨(hM i).ne'⟩
  have hQM (i : Fin (N+1)) : Q ∣ M i := dvd_mul_right Q _
  obtain ⟨n,hn,hscale⟩ := htransfer (Fin (N+1)) M hQM (harmonicPrefixLaw N)
    (fun i x => L x.val)
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  let U (i : Fin (N+1)) := (∑ p ∈ S, naturalGapDiscrepancy (harmonicPrefixLength N i) p L C)/(S.card : ℝ)
  let V (i : Fin (N+1)) := (∑ p ∈ S, cyclicGapDiscrepancy (M i) p (fun x => L x.val) C)/(S.card : ℝ)
  have he (i : Fin (N+1)) : |U i-V i| ≤ D/harmonicPrefixLength N i := by
    dsimp [U,V]
    rw [← sub_div,← sum_sub_distrib]
    apply abs_finset_average_le S hS
    intro p hp
    have hpH := (mem_halfBlockPrimes.mp hp).2
    exact natural_cyclic_round_up_error (harmonicPrefixLength N i) (M i) p B T
      (harmonicPrefixLength_pos N i) (hprops i).1 (hprops i).2.2
      (by omega) (hprops i).2.1 L C hC
  have herr : |mean (harmonicPrefixLaw N) U-mean (harmonicPrefixLaw N) V| ≤
      D/(harmonic (N+1) : ℝ) := by
    rw [← mean_sub]
    apply (abs_mean_le_mean_abs _ _).trans
    apply (mean_mono _ _ _ he).trans_eq
    have hid : (fun i => D/(harmonicPrefixLength N i : ℝ)) =
        (fun i => D*((1 : ℝ)/harmonicPrefixLength N i)) := by funext i; ring
    rw [hid,mean_const_mul,harmonicPrefixLaw_reciprocal_length]
    ring
  have hu : mean (harmonicPrefixLaw N) U =
      (∑ p ∈ S, harmonicRangeGapDiscrepancy (N+1) p L C)/(S.card : ℝ) := by
    dsimp [U]
    rw [mean_div,mean_finset_sum]
    simp_rw [harmonicRangeGapDiscrepancy_mixture]
  have hv := hscale C hC
  change |mean (harmonicPrefixLaw N) V| < ε/2 at hv
  have htri := abs_sub_le (mean (harmonicPrefixLaw N) U) (mean (harmonicPrefixLaw N) V) 0
  simp only [sub_zero] at htri
  rw [← hu]
  linarith

#print axioms natural_cyclic_round_up_error
#print axioms harmonic_range_prime_gap_transfer
end Erdos371.FiniteInformation
