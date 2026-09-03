import Submission.ComponentwiseMixturePrimeTransfer

/-! A common entropy scale controls the harmonic-prefix mixture of absolute
natural prime-gap discrepancies. The absolute value is INSIDE the mixture. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

/-- Unlike scalar harmonic transfer, this controls cancellation separately
at most component endpoints. It does not identify the adjacent endpoint
N/p with N. -/
theorem componentwise_harmonic_prefix_prime_subset_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (S : ℕ → Finset ℕ)
    (hS : ∀ H, H₀ ≤ H → S H ⊆ halfBlockPrimes H)
    (hcard : ∀ H, H₀ ≤ H → c*H/Real.log (H : ℝ) ≤ (S H).card) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∀ L : ℕ → A, ∃ n < K,
      ∀ C : Fin (N+1) → A → A → ℝ, (∀ i a b, |C i a b| ≤ 1) →
        mean (harmonicPrefixLaw N) (fun i =>
          |(∑ p ∈ S (factorialScale H₀ n), naturalGapDiscrepancy
            (harmonicPrefixLength N i) p L (C i)) /
              (S (factorialScale H₀ n)).card|) < ε := by
  classical
  obtain ⟨K,hK,htransfer⟩ := componentwise_cyclic_prime_subset_L1_transfer
    (A := A) H₀ hH₀ (ε/2) c (half_pos hε) hc S hS hcard
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
  let U (i : Fin (N+1)) := (∑ p ∈ S H,
    naturalGapDiscrepancy (harmonicPrefixLength N i) p L (C i))/((S H).card : ℝ)
  let V (i : Fin (N+1)) := (∑ p ∈ S H,
    cyclicGapDiscrepancy (M i) p (fun x => L x.val) (C i))/((S H).card : ℝ)
  have he (i : Fin (N+1)) : |U i-V i| ≤ D/harmonicPrefixLength N i := by
    dsimp [U,V]
    rw [← sub_div,← sum_sub_distrib]
    apply abs_finset_average_le (S H) hnon
    intro p hp
    have hpH := (mem_halfBlockPrimes.mp (hS H hH hp)).2
    exact natural_cyclic_round_up_error (harmonicPrefixLength N i) (M i) p B T
      (harmonicPrefixLength_pos N i) (hprops i).1 (hprops i).2.2
      (by omega) (hprops i).2.1 L (C i) (hC i)
  have hmean := mean_mono (harmonicPrefixLaw N) (fun i => |U i|)
    (fun i => |V i|+D/harmonicPrefixLength N i) (fun i => by
      have htri := abs_sub_le (U i) (V i) 0
      simp only [sub_zero] at htri
      linarith [he i])
  rw [mean_add] at hmean
  have hid : (fun i => D/(harmonicPrefixLength N i : ℝ)) =
      (fun i => D*((1 : ℝ)/harmonicPrefixLength N i)) := by funext i; ring
  rw [hid,mean_const_mul,harmonicPrefixLaw_reciprocal_length] at hmean
  simp only [mul_one_div] at hmean
  have hcyc := hscale C hC
  change mean (harmonicPrefixLaw N) (fun i => |V i|) < ε/2 at hcyc
  change mean (harmonicPrefixLaw N) (fun i => |U i|) < ε
  linarith

#print axioms componentwise_harmonic_prefix_prime_subset_transfer
end Erdos371.FiniteInformation
