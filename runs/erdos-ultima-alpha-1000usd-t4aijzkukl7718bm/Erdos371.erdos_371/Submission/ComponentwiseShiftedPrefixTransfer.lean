import Submission.ComponentwiseMixturePrimeTransfer
import Submission.ShiftedPrefixEndpointLaw

/-! A common entropy scale controls absolute natural discrepancies in
harmonically sampled global prefixes over arbitrary moving windows. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

/-- Unlike scalar harmonic transfer, this controls cancellation separately
at most component endpoints. It does not identify the adjacent endpoint
N/p with N. -/
theorem componentwise_shifted_prefix_prime_subset_transfer {X : Type*} [Fintype X]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (S : ℕ → Finset ℕ)
    (hS : ∀ H, H₀ ≤ H → S H ⊆ halfBlockPrimes H)
    (hcard : ∀ H, H₀ ≤ H → c*H/Real.log (H : ℝ) ≤ (S H).card) :
    ∃ K > 0, ∀ A W : ℕ → ℕ,
      Tendsto (fun j => shiftedHarmonicMass (A j) (W j)) atTop atTop →
      ∀ᶠ j : ℕ in atTop, ∀ L : ℕ → X, ∃ n < K,
      ∀ C : Fin (W j+1) → X → X → ℝ, (∀ i a b, |C i a b| ≤ 1) →
        mean (shiftedEndpointLaw (A j) (W j)) (fun i =>
          |(∑ p ∈ S (factorialScale H₀ n), naturalGapDiscrepancy
            (shiftedEndpoint (A j) (W j) i) p L (C i)) /
              (S (factorialScale H₀ n)).card|) < ε := by
  classical
  obtain ⟨K,hK,htransfer⟩ := componentwise_cyclic_prime_subset_L1_transfer
    (A := X) H₀ hH₀ (ε/2) c (half_pos hε) hc S hS hcard
  let Q : ℕ := ∏ n ∈ range K, primorial (factorialScale H₀ n)
  let B : ℕ := (range K).sup (factorialScale H₀)
  let T : ℕ := Q*(B+1)
  let D : ℝ := 2*(B+1 : ℝ)*T+2*B*(B+1 : ℝ)
  have hQ : 0 < Q := prod_pos (fun _ _ => primorial_pos _)
  refine ⟨K,hK,?_⟩
  intro A W hH
  have ht : Tendsto (fun j : ℕ => 2*D/shiftedHarmonicMass (A j) (W j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hH
  filter_upwards [ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with j hsmall
  intro L
  let M (i : Fin (W j+1)) := Q*(shiftedEndpoint (A j) (W j) i/Q+B+1)
  have hprops (i : Fin (W j+1)) :
      shiftedEndpoint (A j) (W j) i ≤ M i ∧ B ≤ M i ∧ M i-shiftedEndpoint (A j) (W j) i ≤ T := by
    have hd := Nat.div_add_mod (shiftedEndpoint (A j) (W j) i) Q
    have hm := Nat.mod_lt (shiftedEndpoint (A j) (W j) i) hQ
    have hB : B ≤ Q*(B+1) := by nlinarith
    have hme : M i = Q*(shiftedEndpoint (A j) (W j) i/Q)+Q*(B+1) := by dsimp [M]; ring
    dsimp [T]
    rw [hme]
    constructor
    · nlinarith
    constructor <;> omega
  have hM (i : Fin (W j+1)) : 0 < M i :=
    (shiftedEndpoint_pos (A j) (W j) i).trans_le (hprops i).1
  letI (i : Fin (W j+1)) : NeZero (M i) := ⟨(hM i).ne'⟩
  have hQM (i : Fin (W j+1)) : Q ∣ M i := dvd_mul_right Q _
  obtain ⟨n,hn,hscale⟩ := htransfer (Fin (W j+1)) M hQM (shiftedEndpointLaw (A j) (W j))
    (fun _ x => L x.val)
  refine ⟨n,hn,?_⟩
  intro C hC
  let H := factorialScale H₀ n
  have hH : H₀ ≤ H := factorialScale_ge H₀ n
  have hHB : H ≤ B := by
    exact le_sup (f := factorialScale H₀) (mem_range.mpr hn)
  have hnon : (S H).Nonempty := by
    apply card_pos.mp
    have hHr : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
    exact_mod_cast (div_pos (mul_pos hc hHr) hlog).trans_le (hcard H hH)
  let U (i : Fin (W j+1)) := (∑ p ∈ S H,
    naturalGapDiscrepancy (shiftedEndpoint (A j) (W j) i) p L (C i))/((S H).card : ℝ)
  let V (i : Fin (W j+1)) := (∑ p ∈ S H,
    cyclicGapDiscrepancy (M i) p (fun x => L x.val) (C i))/((S H).card : ℝ)
  have he (i : Fin (W j+1)) : |U i-V i| ≤ D/shiftedEndpoint (A j) (W j) i := by
    dsimp [U,V]
    rw [← sub_div,← sum_sub_distrib]
    apply abs_finset_average_le (S H) hnon
    intro p hp
    have hpH := (mem_halfBlockPrimes.mp (hS H hH hp)).2
    exact natural_cyclic_round_up_error (shiftedEndpoint (A j) (W j) i) (M i) p B T
      (shiftedEndpoint_pos (A j) (W j) i) (hprops i).1 (hprops i).2.2
      (by omega) (hprops i).2.1 L (C i) (hC i)
  have hmean := mean_mono (shiftedEndpointLaw (A j) (W j)) (fun i => |U i|)
    (fun i => |V i|+D/shiftedEndpoint (A j) (W j) i) (fun i => by
      have htri := abs_sub_le (U i) (V i) 0
      simp only [sub_zero] at htri
      linarith [he i])
  rw [mean_add] at hmean
  have hid : (fun i => D/(shiftedEndpoint (A j) (W j) i : ℝ)) =
      (fun i => D*((1 : ℝ)/shiftedEndpoint (A j) (W j) i)) := by funext i; ring
  rw [hid,mean_const_mul] at hmean
  have hrec := mul_le_mul_of_nonneg_left (shiftedEndpointLaw_reciprocal_bound (A j) (W j))
    (show 0 ≤ D by dsimp [D]; positivity)
  have he : D*(2/shiftedHarmonicMass (A j) (W j)) = 2*D/shiftedHarmonicMass (A j) (W j) := by ring
  rw [he] at hrec
  have hcyc := hscale C hC
  change mean (shiftedEndpointLaw (A j) (W j)) (fun i => |V i|) < ε/2 at hcyc
  change mean (shiftedEndpointLaw (A j) (W j)) (fun i => |U i|) < ε
  linarith

#print axioms componentwise_shifted_prefix_prime_subset_transfer
end Erdos371.FiniteInformation
