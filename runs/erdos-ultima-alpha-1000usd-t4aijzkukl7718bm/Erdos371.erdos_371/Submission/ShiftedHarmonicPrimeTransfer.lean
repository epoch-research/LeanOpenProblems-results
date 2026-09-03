import Submission.TranslatedCyclicBoundary
import Submission.ShiftedHarmonicDilation

/-! Common-scale entropy transfer on harmonic intervals with arbitrary lower
endpoints. Only the total harmonic mass is required to diverge. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

theorem translated_decreasing_weight_prime_gap_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) (w : ℕ → ℝ),
      (∀ n≤N, 0 ≤ w n) → AntitoneOn w (Set.Iic N) →
      0 < (∑ n ∈ range (N+1), w n) →
      D*w 0/(∑ n ∈ range (N+1), w n) < ε/2 →
      ∀ (a : ℕ) (L : ℕ → A), ∃ n < K, ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
        |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
          (∑ m ∈ range (N+1), w m*translatedGapTest p L C (a+m)) / (∑ m ∈ range (N+1), w m)) /
              (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  classical
  obtain ⟨K,hK,htransfer⟩ := mixture_cyclic_prime_gap_transfer (A := A) H₀ hH₀ (ε/2) (by positivity)
  let Q : ℕ := ∏ n ∈ range K, primorial (factorialScale H₀ n)
  let B : ℕ := (range K).sup (factorialScale H₀)
  let T : ℕ := Q*(B+1)
  let D : ℝ := 2*(B+1 : ℝ)*T+2*B*(B+1 : ℝ)+1
  have hQ : 0 < Q := prod_pos (fun _ _ => primorial_pos _)
  refine ⟨K,hK,D,by dsimp [D]; positivity,?_⟩
  intro N w hw hanti hW hsmall a L
  let ρ := decreasingPrefixLaw w N hw hanti hW
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
  have hM (i : Fin (N+1)) : 0 < M i := (harmonicPrefixLength_pos N i).trans_le (hprops i).1
  letI (i : Fin (N+1)) : NeZero (M i) := ⟨(hM i).ne'⟩
  have hQM (i : Fin (N+1)) : Q ∣ M i := dvd_mul_right Q _
  obtain ⟨n,hn,hscale⟩ := htransfer (Fin (N+1)) M hQM ρ (fun i => translatedCycleLabel a (M i) L)
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  let U (i : Fin (N+1)) := (∑ p ∈ S, translatedNaturalGapDiscrepancy a (harmonicPrefixLength N i) p L C)/(S.card : ℝ)
  let V (i : Fin (N+1)) := (∑ p ∈ S, cyclicGapDiscrepancy (M i) p (translatedCycleLabel a (M i) L) C)/(S.card : ℝ)
  have he (i : Fin (N+1)) : |U i-V i| ≤ D/harmonicPrefixLength N i := by
    dsimp [U,V]
    rw [← sub_div,← sum_sub_distrib]
    apply abs_finset_average_le S hS
    intro p hp
    have hpH := (mem_halfBlockPrimes.mp hp).2
    have hpHdiv : p ∣ primorial (factorialScale H₀ n) :=
      (dvd_prod_of_mem (fun p : halfBlockPrimes (factorialScale H₀ n) => (p : ℕ))
        (mem_univ ⟨p,hp⟩)).trans (halfBlockPrimes_prod_dvd_primorial _)
    have hpQ : p ∣ Q := hpHdiv.trans
      (dvd_prod_of_mem (fun j => primorial (factorialScale H₀ j)) (mem_range.mpr hn))
    have h := translated_natural_cyclic_round_up_error a (harmonicPrefixLength N i) (M i) p B T
      (harmonicPrefixLength_pos N i) (hprops i).1 (hprops i).2.2
      (by omega) (hprops i).2.1 (hpQ.trans (hQM i)) L C hC
    exact h.trans (div_le_div_of_nonneg_right (by dsimp [D]; linarith) (Nat.cast_nonneg _))
  have herr : |mean ρ U-mean ρ V| ≤ D*w 0/(∑ m ∈ range (N+1), w m) := by
    rw [← mean_sub]
    apply (abs_mean_le_mean_abs _ _).trans
    apply (mean_mono _ _ _ he).trans_eq
    have hid : (fun i => D/(harmonicPrefixLength N i : ℝ)) =
        (fun i => D*((1 : ℝ)/harmonicPrefixLength N i)) := by funext i; ring
    rw [hid,mean_const_mul]
    dsimp only [ρ]
    rw [decreasingPrefixLaw_reciprocal_length]
    ring
  have hu : mean ρ U =
      (∑ p ∈ S, (∑ m ∈ range (N+1), w m*translatedGapTest p L C (a+m)) / (∑ m ∈ range (N+1), w m)) / (S.card : ℝ) := by
    dsimp [U]
    rw [mean_div,mean_finset_sum]
    congr 1
    apply sum_congr rfl
    intro p hp
    simp only [translatedNaturalGapDiscrepancy]
    exact decreasingPrefixLaw_representation w N hw hanti hW _
  have hv := hscale C hC
  change |mean ρ V| < ε/2 at hv
  have htri := abs_sub_le (mean ρ U) (mean ρ V) 0
  simp only [sub_zero] at htri
  rw [← hu]
  linarith


noncomputable def shiftedHarmonicGapDiscrepancy {X : Type*} (A N p : ℕ)
    (L : ℕ → X) (C : X → X → ℝ) : ℝ :=
  shiftedHarmonicMean A N (translatedGapTest p L C)

/-- One finite entropy horizon works for every sequence of intervals, every
finite-label process, and every unit-bounded pair observable. -/
theorem shifted_harmonic_prime_gap_transfer {X : Type*} [Fintype X]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ A M : ℕ → ℕ,
      Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop →
      ∀ᶠ j : ℕ in atTop, ∀ L : ℕ → X, ∃ n < K,
        ∀ C : X → X → ℝ, (∀ a b, |C a b| ≤ 1) →
          |(∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
            shiftedHarmonicGapDiscrepancy (A j) (M j) p L C) /
              (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨K,hK,D,hD,ht⟩ := translated_decreasing_weight_prime_gap_transfer (A := X) H₀ hH₀ ε hε
  refine ⟨K,hK,?_⟩
  intro A M hH
  have he : Tendsto (fun j => D/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hH
  filter_upwards [he.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)] with j hj
  intro L
  have hw : D*((1 : ℝ)/(A j+(0 : ℕ)+1))/shiftedHarmonicMass (A j) (M j) < ε/2 := by
    apply lt_of_le_of_lt _ hj
    apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos _ _).le
    apply mul_le_of_le_one_right hD.le
    apply (div_le_one (by positivity)).mpr
    have := Nat.cast_nonneg (α := ℝ) (A j)
    simp only [Nat.cast_zero,add_zero]
    linarith
  obtain ⟨n,hn,hscale⟩ := ht (M j) (fun k => (1 : ℝ)/(A j+k+1))
    (fun _ _ => by positivity) ((shifted_reciprocal_antitone (A j)).antitoneOn _)
    (shiftedHarmonicMass_pos _ _) hw (A j+1) L
  refine ⟨n,hn,?_⟩
  intro C hC
  have hs := hscale C hC
  have hid (p : ℕ) :
      (∑ m ∈ range (M j+1), (1 : ℝ)/(A j+m+1)*translatedGapTest p L C (A j+1+m)) /
          (∑ m ∈ range (M j+1), (1 : ℝ)/(A j+m+1)) =
        shiftedHarmonicGapDiscrepancy (A j) (M j) p L C := by
    unfold shiftedHarmonicGapDiscrepancy shiftedHarmonicMean shiftedHarmonicRaw shiftedHarmonicMass
    congr 1
    apply sum_congr rfl
    intro m _
    rw [show A j+1+m=A j+m+1 by omega]
    ring
  simpa only [hid] using hs

#print axioms translated_decreasing_weight_prime_gap_transfer
#print axioms shifted_harmonic_prime_gap_transfer
end Erdos371.FiniteInformation
