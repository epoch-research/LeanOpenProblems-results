import Submission.ScaledFractionalTailExplore
import Submission.SummableTailBudgetExplore
import Submission.SummedBernoulliBoundsExplore
import Submission.RepEnvelopeCompactnessExplore

/-! An infinite fixed-relative-tolerance analogue of Erdős 66.
The logarithmic coefficient depends on the tolerance. This is not a proof
of convergence with one fixed coefficient. -/
namespace Erdos66InfiniteLogApproximation
open Filter AdditiveCombinatorics
open Erdos66ScaledFractionalTail Erdos66SummableTailBudget
  Erdos66SummedBernoulliBounds Erdos66RepEnvelopeCompactness
  Erdos66FiniteRepBernoulli
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma log_shift_bound (n : ℕ) (hn : 2 ≤ n) :
    Real.log ((n:ℝ)+2) ≤ 2*Real.log n := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hh := Real.log_le_log (by positivity : 0 < (n:ℝ)+2)
    (show (n:ℝ)+2 ≤ (n:ℝ)^2 by nlinarith)
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

/-- A quantitative fixed-tolerance construction. -/
theorem exists_with_coefficient (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : Set ℕ, ∀ᶠ n : ℕ in atTop,
      |(sumRep A n : ℝ)/Real.log n - 16/δ^2| ≤ 5*δ*(16/δ^2) := by
  let c : ℝ := 16/δ^2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcδ : δ^2*c=16 := by dsimp [c]; field_simp
  obtain ⟨p, hp, hconv⟩ := exists_scaled_probability_profile c hc
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (uniform_mean_approximation p hp c hconv (δ*c) (mul_pos hδ hc))
  obtain ⟨N₂, hN₂⟩ := exists_fourth_tail_budget
  let N := max 2 (max N₁ N₂)
  let V : ℕ → ℝ := fun n ↦ 2*c*Real.log ((n:ℝ)+2)
  have hmean (L n : ℕ) (hn : N ≤ n) (hL : n ≤ L) :
      |repMean L n (fun i ↦ p i.val)/Real.log n-c| < δ*c :=
    hN₁ n (by dsimp [N] at hn; omega) L hL
  have hlog (n : ℕ) (hn : N ≤ n) : 0 < Real.log (n:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<n by dsimp [N] at hn; omega))
  have hmV (L n : ℕ) (hn : N ≤ n) (hL : n ≤ L) :
      repMean L n (fun i ↦ p i.val) ≤ V n := by
    have hh := (abs_lt.mp (hmean L n hn hL)).2
    have hratio : repMean L n (fun i ↦ p i.val)/Real.log n ≤ 2*c := by
      nlinarith
    have hraw := (div_le_iff₀ (hlog n hn)).mp hratio
    have hshift : Real.log (n:ℝ) ≤ Real.log ((n:ℝ)+2) :=
      Real.log_le_log (by exact_mod_cast (show 0<n by dsimp [N] at hn; omega)) (by linarith)
    exact hraw.trans (mul_le_mul_of_nonneg_left hshift (by positivity))
  have htail (n : ℕ) : 2*Real.exp (-δ^2*V n/8)=2/((n:ℝ)+2)^4 := by
    have he : -δ^2*V n/8 = -(4*Real.log ((n:ℝ)+2)) := by
      dsimp [V]
      calc
        _ = -(δ^2*c)*Real.log ((n:ℝ)+2)/4 := by ring
        _ = _ := by rw [hcδ]; ring
    rw [he,Real.exp_neg]
    rw [show (4:ℝ)=((4:ℕ):ℝ) by norm_num,Real.exp_nat_mul,
      Real.exp_log (by positivity : 0 < (n:ℝ)+2)]
    rfl
  have hfinite (L : ℕ) : ∃ A : Set ℕ, ∀ n, N ≤ n → n ≤ L →
      |(sumRep A n : ℝ)-c*Real.log n| ≤ 5*δ*c*Real.log n := by
    let S : Finset ℕ := Finset.Icc N L
    have hsmall : (∑ n∈S, 2*Real.exp (-δ^2*V n/8)) < 1 := by
      simp_rw [htail]
      exact hN₂ S (fun n hn ↦ by
        have hh := (Finset.mem_Icc.mp hn).1
        dsimp [N] at hh
        omega)
    obtain ⟨ω, hw, hω⟩ := exists_summed_bound (fun i : Fin (L+1) ↦ p i.val)
      (fun i ↦ hp i.val) S (fun n ω ↦ (sumRep (selected L ω) n : ℝ))
      (fun n ↦ repMean L n (fun i ↦ p i.val)) V δ hδ hδ1
      (fun n hn ↦ hmV L n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2)
      (fun n _ t ht ↦ rep_mgf L n (fun i ↦ p i.val) (fun i ↦ hp i.val) t ht)
      hsmall
    refine ⟨selected L ω, fun n hn hnL ↦ ?_⟩
    have hd := hω n (Finset.mem_Icc.mpr ⟨hn,hnL⟩)
    have hh := hmean L n hn hnL
    have hln := hlog n hn
    have he : repMean L n (fun i ↦ p i.val)/Real.log n-c =
        (repMean L n (fun i ↦ p i.val)-c*Real.log n)/Real.log n := by
      field_simp
    rw [he,abs_div,abs_of_pos hln] at hh
    have hbias := (div_lt_iff₀ hln).mp hh
    have hshift := log_shift_bound n (by dsimp [N] at hn; omega)
    have hdev : δ*V n ≤ 4*δ*c*Real.log n := by
      have hh := mul_le_mul_of_nonneg_left hshift (show 0 ≤ δ*(2*c) by positivity)
      dsimp [V]
      nlinarith
    have ha := abs_sub_le (sumRep (selected L ω) n : ℝ)
      (repMean L n (fun i ↦ p i.val)) (c*Real.log n)
    nlinarith
  obtain ⟨A,hA⟩ := exists_of_finite_envelopes (fun n ↦ c*Real.log n)
    (fun n ↦ 5*δ*c*Real.log n) N hfinite
  refine ⟨A, eventually_atTop.mpr ⟨N,fun n hn ↦ ?_⟩⟩
  have hln := hlog n hn
  change |(sumRep A n : ℝ)/Real.log n-c| ≤ 5*δ*c
  have he : (sumRep A n : ℝ)/Real.log n-c =
      ((sumRep A n : ℝ)-c*Real.log n)/Real.log n := by field_simp
  rw [he,abs_div,abs_of_pos hln]
  exact (div_le_iff₀ hln).mpr (hA n hn)

/-- Arbitrarily small fixed relative error is possible with a coefficient
that is allowed to depend on that error. -/
theorem exists_fixed_relative_log_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : Set ℕ) (c : ℝ), 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      |(sumRep A n : ℝ)/Real.log n-c| ≤ ε*c := by
  let δ : ℝ := min (ε/5) 1
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : 5*δ ≤ ε := by have := min_le_left (ε/5) 1; dsimp [δ]; linarith
  obtain ⟨A,hA⟩ := exists_with_coefficient δ hδ hδ1
  have hc : 0 < 16/δ^2 := by positivity
  refine ⟨A,16/δ^2,hc,?_⟩
  filter_upwards [hA] with n hn
  exact hn.trans (mul_le_mul_of_nonneg_right hδε hc.le)

end Erdos66InfiniteLogApproximation
