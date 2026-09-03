import Submission.UniformPrimeBlockHighMoments
import Submission.CountableBandDensity

/-!
Countably many signed moving-center prime-score bands with logarithmic index
loss. This strengthens the analytic source construction, but does not supply
an all-family cubic collision estimate.
-/
namespace Erdos1206.SignedLogarithmicPrimeBands
open Finset Filter PrimeBlockVariance MovingPrimeBlockVariance SharpPrimeBlockVariance
open UniformPrimeBlockHighMoments
open scoped Classical Topology

/-- The order schedule has summable geometric costs. -/
theorem source_of_moment_schedule (S : Set ℕ) (hpos : ∀ n∈S,0 < n)
    (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (k : ℕ → ℕ)
    {δ C₀ C : ℝ} (hC : 0 < C)
    (hpre : ∀ N : ℕ,δ*(N:ℝ) ≤ ((S∩Set.Iio N).ncard:ℝ)+C₀)
    (hk : ∀ j,0 < k j)
    (hm : ∀ j N : ℕ,
      (∑ n∈Icc 1 N,(primeSum (P j) (w j) n-movingMean (P j) (w j) n)^(2*k j)) ≤
        (N:ℝ)*(C*(k j:ℝ)*(mass (P j) (w j)+k j))^(k j))
    (hcs : Summable (fun j => (1/4:ℝ)^(k j)))
    (hcost : (∑' j,(1/4:ℝ)^(k j)) < δ) :
    ∃ A : Set ℕ,A ⊆ S ∧ 0 < A.lowerDensity ∧ ∀ n∈A,∀ j,
      (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^2 ≤
        4*C*(k j:ℝ)*(mass (P j) (w j)+k j) := by
  let R : ℕ → ℝ := fun j => Real.sqrt (4*C*(k j:ℝ)*(mass (P j) (w j)+k j))
  have hkp (j : ℕ) : (0:ℝ) < k j := by exact_mod_cast hk j
  have hm0 (j : ℕ) : 0 ≤ mass (P j) (w j) := mass_nonneg _ _
  have hRpos (j : ℕ) : 0 < R j := by
    have := hkp j
    have := hm0 j
    apply Real.sqrt_pos.mpr
    positivity
  have hR2 (j : ℕ) : (R j)^2=4*C*(k j:ℝ)*(mass (P j) (w j)+k j) :=
    Real.sq_sqrt (by have := hkp j; have := hm0 j; positivity)
  let f : ℕ → ℕ → ℝ := fun j n =>
    ((primeSum (P j) (w j) n-movingMean (P j) (w j) n)/R j)^(k j)
  have hmoment (j N : ℕ) : (∑ n∈Icc 1 N,(f j n)^2) ≤ (N:ℝ)*(1/4:ℝ)^(k j) := by
    have he (n : ℕ) : (f j n)^2=
        (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^(2*k j)/((R j)^2)^(k j) := by
      dsimp only [f]
      rw [←pow_mul,Nat.mul_comm (k j) 2,div_pow]
      simp only [pow_mul]
    simp_rw [he]
    rw [←sum_div]
    apply (div_le_iff₀ (pow_pos (sq_pos_of_pos (hRpos j)) (k j))).mpr
    have hscale : (1/4:ℝ)*(R j)^2=C*(k j:ℝ)*(mass (P j) (w j)+k j) := by
      rw [hR2]; ring
    rw [mul_assoc,←mul_pow,hscale]
    exact hm j N
  let A : Set ℕ := {n | n∈S ∧ ∀ j,|f j n| ≤ 1}
  have hden : 0 < A.lowerDensity := CountableBandDensity.lowerDensity_pos_of_prefix
    S f (fun j => (1/4:ℝ)^(k j)) hpos hpre (fun j => by positivity) hcs hmoment hcost
  refine ⟨A,fun _ hn => hn.1,hden,fun n hn j => ?_⟩
  have hh := hn.2 j
  change |((primeSum (P j) (w j) n-movingMean (P j) (w j) n)/R j)^(k j)| ≤ 1 at hh
  rw [abs_pow,pow_le_one_iff_of_nonneg (abs_nonneg _) (hk j).ne'] at hh
  rw [abs_div,abs_of_pos (hRpos j)] at hh
  have hab := (div_le_one (hRpos j)).mp hh
  have hs := (sq_le_sq₀ (abs_nonneg _) (hRpos j).le).mpr hab
  simpa only [sq_abs,hR2] using hs

lemma logarithmic_cost_summable :
    Summable (fun j : ℕ => (1/4:ℝ)^(Nat.log 2 (j+1)+1)) := by
  have hs : Summable (fun j : ℕ => (((j:ℝ)+1)^2)⁻¹) := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2:ℕ)))
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  apply hs.of_nonneg_of_le (fun j => by positivity)
  intro j
  have hn := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (j+1)
  have hp : (j+1)^2 ≤ (4:ℕ)^(Nat.log 2 (j+1)+1) := by
    calc
      _ ≤ (2^(Nat.log 2 (j+1)+1))^2 := Nat.pow_le_pow_left hn.le _
      _ = _ := by rw [←pow_mul,Nat.mul_comm _ 2,pow_mul]; norm_num
  have hpR : ((j:ℝ)+1)^2 ≤ (4:ℝ)^(Nat.log 2 (j+1)+1) := by exact_mod_cast hp
  have hh := one_div_le_one_div_of_le (by positivity : (0:ℝ) < ((j:ℝ)+1)^2) hpR
  simpa only [one_div_pow,one_div,inv_pow] using hh

/-- Any positive-density source of positive integers admits all countably
many signed moving-center bounds simultaneously, with logarithmic index
rather than geometric index loss. The same K works for all prime blocks. -/
theorem exists_signed_logarithmic_bands (S : Set ℕ) (hS : 0 < S.lowerDensity)
    (hpos : ∀ n∈S,0 < n) :
    ∃ K : ℝ,0 < K ∧ ∀ (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ j p,p∈P j → p.Prime) → (∀ j p,p∈P j → |w j p| ≤ 1) →
      ∃ A : Set ℕ,A ⊆ S ∧ 0 < A.lowerDensity ∧ ∀ n∈A,∀ j,
        (primeSum (P j) (w j) n-movingMean (P j) (w j) n)^2 ≤
          K*(Nat.log 2 (j+1)+1:ℕ)*(mass (P j) (w j)+(Nat.log 2 (j+1)+1:ℕ)) := by
  obtain ⟨C,hC,hmom⟩ := exists_moving_moment_constant
  obtain ⟨δ,hδ,C₀,hpre⟩ := prefix_bound_of_positive_lowerDensity hS
  let b : ℕ → ℝ := fun j => (1/4:ℝ)^(Nat.log 2 (j+1)+1)
  have hb : Summable b := logarithmic_cost_summable
  let B : ℝ := ∑' j,b j
  have ht : Tendsto (fun J : ℕ => (1/4:ℝ)^J*B) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ) < 1)).mul_const B
  obtain ⟨J,hJ⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  let k : ℕ → ℕ := fun j => J+(Nat.log 2 (j+1)+1)
  have hk (j : ℕ) : 0 < k j := by dsimp [k]; omega
  have hcs : Summable (fun j => (1/4:ℝ)^(k j)) := by
    simpa only [k,pow_add,b] using hb.mul_left ((1/4:ℝ)^J)
  have hcost : (∑' j,(1/4:ℝ)^(k j)) < δ := by
    simpa only [k,pow_add,tsum_mul_left,b,B] using hJ
  let K : ℝ := 4*C*((J:ℝ)+1)^2
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,fun P w hP hw => ?_⟩
  obtain ⟨A,hAS,hAd,hA⟩ := source_of_moment_schedule S hpos P w k hC hpre hk
    (fun j N => hmom (P j) (w j) (hP j) (hw j) (k j) (hk j) N) hcs hcost
  refine ⟨A,hAS,hAd,fun n hn j => ?_⟩
  have hsmall := hA n hn j
  let q : ℕ := Nat.log 2 (j+1)+1
  have hq : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by dsimp [q]; omega)
  have hM : 0 ≤ mass (P j) (w j) := mass_nonneg _ _
  have hkj : (k j:ℝ) ≤ ((J:ℝ)+1)*(q:ℝ) := by
    have he : (k j:ℝ)=(J:ℝ)+q := by simp only [k,q,Nat.cast_add]
    rw [he]
    nlinarith [show (0:ℝ) ≤ J from Nat.cast_nonneg J]
  have hmj : mass (P j) (w j)+(k j:ℝ) ≤
      ((J:ℝ)+1)*(mass (P j) (w j)+(q:ℝ)) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg J) hM]
  have hp := mul_le_mul hkj hmj (show 0 ≤ mass (P j) (w j)+(k j:ℝ) by positivity)
    (show 0 ≤ ((J:ℝ)+1)*(q:ℝ) by positivity)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*C by positivity)
  apply hsmall.trans
  convert hh using 1 <;> dsimp [K,q] <;> ring

#print axioms source_of_moment_schedule
#print axioms logarithmic_cost_summable
#print axioms exists_signed_logarithmic_bands
end Erdos1206.SignedLogarithmicPrimeBands
