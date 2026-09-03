import Submission.ShiftedDivisorPole
import Submission.InverseTotientMomentEndpoint

/-!
# Unbounded normalized Dirichlet moments over actual shifted primes

Prime powers contribute a convergent remainder at s=1. The resulting lower
statement has no quantitative rate and is weaker than the high-moment
bounds needed in the proposed smooth-prime comparison.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta Topology

namespace Erdos821.HigherDivisors

set_option maxHeartbeats 2000000

noncomputable def primeMomentWeight (k n : ℕ) : ℝ :=
  if n.Prime then vonMangoldt n*(tau k (n-1) : ℝ) else 0

noncomputable def nonprimeMomentWeight (k n : ℕ) : ℝ :=
  if n.Prime then 0 else vonMangoldt n*(tau k (n-1) : ℝ)

lemma primeMomentWeight_nonneg (k n : ℕ) : 0 ≤ primeMomentWeight k n := by
  unfold primeMomentWeight
  positivity [vonMangoldt_nonneg (n := n)]

lemma nonprimeMomentWeight_nonneg (k n : ℕ) : 0 ≤ nonprimeMomentWeight k n := by
  unfold nonprimeMomentWeight
  positivity [vonMangoldt_nonneg (n := n)]

lemma momentWeight_add (k n : ℕ) :
    primeMomentWeight k n + nonprimeMomentWeight k n = vonMangoldt n*(tau k (n-1) : ℝ) := by
  unfold primeMomentWeight nonprimeMomentWeight
  split_ifs <;> simp

lemma sum_nonprimeMomentWeight (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, nonprimeMomentWeight k n) = nonprimeMangoldtMoment k X := by
  unfold nonprimeMangoldtMoment nonprimeMomentWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp_all

/-- The weighted nonprime prime-power series converges at the boundary. -/
theorem summable_nonprimeMomentWeight_div (k : ℕ) :
    Summable (fun n : ℕ => nonprimeMomentWeight (k+1) n/(n : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := nonprimeMangoldtMoment_subpower_bound k
  let f : ℕ → ℝ := fun n => nonprimeMomentWeight (k+1) n/(n : ℝ)
  have hf : ∀ n, 0 ≤ f n := fun n => div_nonneg (nonprimeMomentWeight_nonneg _ _) (Nat.cast_nonneg n)
  apply Erdos821.summable_of_summable_geometric_blocks f hf 4 (by decide)
  have H1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1/2 : ℝ)‖ < 1)
  have H0 := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have H : Summable (fun j : ℕ => 64*C*Real.log 2*((j : ℝ)+1)*(1/2 : ℝ)^j) := by
    convert (H1.add H0).mul_left (64*C*Real.log 2) using 1
    funext j
    simp only [pow_one]
    ring
  apply H.of_nonneg_of_le (fun j => Finset.sum_nonneg (fun n _ => hf n))
  intro j
  let L : ℕ := 2^(4*j)
  let U : ℕ := 2^(4*(j+1))
  have hL : (0 : ℝ) < L := by dsimp [L]; positivity
  have hU : 1 ≤ U := by dsimp [U]; exact one_le_pow₀ (by norm_num)
  have hsub : Finset.Ico L U ⊆ Finset.Icc 1 U := by
    intro n hn
    obtain ⟨hLn,hnU⟩ := Finset.mem_Ico.mp hn
    have hL1 : 1 ≤ L := by dsimp [L]; exact one_le_pow₀ (by norm_num)
    exact Finset.mem_Icc.mpr ⟨hL1.trans hLn,hnU.le⟩
  have hp : (U : ℝ)^(3/4 : ℝ) = (2 : ℝ)^(3*(j+1)) := by
    dsimp [U]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (∑ n ∈ Finset.Ico L U, nonprimeMomentWeight (k+1) n)/(L : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro n hn
      apply div_le_div_of_nonneg_left (nonprimeMomentWeight_nonneg _ _) hL
      exact_mod_cast (Finset.mem_Ico.mp hn).1
    _ ≤ nonprimeMangoldtMoment (k+1) U/(L : ℝ) := by
      rw [← sum_nonprimeMomentWeight]
      apply div_le_div_of_nonneg_right _ hL.le
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => nonprimeMomentWeight_nonneg _ _)
    _ ≤ (2*C*(U : ℝ)^(3/4 : ℝ)*Real.log U)/(L : ℝ) :=
      div_le_div_of_nonneg_right (hbound U hU) hL.le
    _ = _ := by
      rw [hp]
      dsimp [U,L]
      rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      rw [show 3*(j+1) = 3*j+3 by omega, pow_add, show 4*j = 3*j+j by omega, pow_add]
      push_cast
      norm_num
      simp only [div_pow, one_pow]
      field_simp
      ring

noncomputable def shiftedPrimeDirichlet (k : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, primeMomentWeight k n/(n : ℝ)^s

noncomputable def nonprimeDirichlet (k : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, nonprimeMomentWeight k n/(n : ℝ)^s

lemma shiftedPrimeDirichlet_summable (k : ℕ) (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => primeMomentWeight (k+1) n/(n : ℝ)^s) := by
  apply (shiftedMangoldtDirichlet_summable k s hs).of_nonneg_of_le
    (fun n => div_nonneg (primeMomentWeight_nonneg _ _) (by positivity))
  intro n
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← momentWeight_add]
  exact le_add_of_nonneg_right (nonprimeMomentWeight_nonneg _ _)

lemma nonprimeDirichlet_summable (k : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun n : ℕ => nonprimeMomentWeight (k+1) n/(n : ℝ)^s) := by
  apply (summable_nonprimeMomentWeight_div k).of_nonneg_of_le
    (fun n => div_nonneg (nonprimeMomentWeight_nonneg _ _) (by positivity))
  intro n
  by_cases hn : n = 0
  · subst n
    simp [nonprimeMomentWeight]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  apply div_le_div_of_nonneg_left (nonprimeMomentWeight_nonneg _ _) (by linarith : (0 : ℝ) < n)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hs

lemma nonprimeDirichlet_le_boundary (k : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    nonprimeDirichlet (k+1) s ≤ nonprimeDirichlet (k+1) 1 := by
  apply Summable.tsum_le_tsum _ (nonprimeDirichlet_summable k s hs)
    (nonprimeDirichlet_summable k 1 le_rfl)
  intro n
  by_cases hn : n = 0
  · subst n
    simp [nonprimeMomentWeight]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  exact div_le_div_of_nonneg_left (nonprimeMomentWeight_nonneg _ _) (by positivity)
    (Real.rpow_le_rpow_of_exponent_le hn1 hs)

lemma shiftedDirichlet_prime_nonprime (k : ℕ) (s : ℝ) (hs : 1 < s) :
    shiftedMangoldtDirichlet (k+1) s = shiftedPrimeDirichlet (k+1) s + nonprimeDirichlet (k+1) s := by
  unfold shiftedMangoldtDirichlet shiftedPrimeDirichlet nonprimeDirichlet
  rw [← (shiftedPrimeDirichlet_summable k s hs).tsum_add (nonprimeDirichlet_summable k s hs.le)]
  apply tsum_congr
  intro n
  rw [← add_div, momentWeight_add]

/-- A genuine prime-weighted conclusion from fixed-modulus distribution.
The growth rate is unspecified; no full high-moment asymptotic is claimed. -/
theorem tendsto_shiftedPrimeDirichlet_residue (k : ℕ) :
    Tendsto (fun s : ℝ => (s-1)*shiftedPrimeDirichlet (k+2) s) (𝓝[>] 1) atTop := by
  apply tendsto_atTop.mpr
  intro A
  let C := nonprimeDirichlet (k+2) 1
  have hC : 0 ≤ C := tsum_nonneg (fun n => div_nonneg (nonprimeMomentWeight_nonneg _ _) (by positivity))
  have hbig := (tendsto_atTop.mp (tendsto_shiftedMangoldtDirichlet_residue k)) (A+C)
  have htwo : ∀ᶠ s : ℝ in 𝓝[>] 1, s < 2 :=
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hbig, eventually_mem_nhdsWithin, htwo] with s hs hs1 hs2
  have hs1' : 1 < s := hs1
  have hnp := nonprimeDirichlet_le_boundary (k+1) s hs1'.le
  have hnp' : (s-1)*nonprimeDirichlet (k+2) s ≤ C := by
    calc
      _ ≤ (s-1)*C := mul_le_mul_of_nonneg_left hnp (by linarith)
      _ ≤ C := mul_le_of_le_one_left hC (by linarith)
  rw [shiftedDirichlet_prime_nonprime (k+1) s hs1', mul_add] at hs
  linarith

end Erdos821.HigherDivisors
