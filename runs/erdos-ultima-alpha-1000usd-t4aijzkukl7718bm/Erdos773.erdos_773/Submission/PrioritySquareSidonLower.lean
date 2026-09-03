import Submission.CaroTuzaFourUniform
import Submission.ControlledSquareSampling
import Submission.APFreeExtraction

/-!
Applying the four-uniform priority bound to progression-free square carriers.
The resulting Sidon lower bound still has a logarithmic loss.
-/
namespace Erdos773.PrioritySquareSidonLower
open Finset Filter SquareCollisionCodegrees
set_option maxHeartbeats 1500000

lemma sidon_of_edge_avoidance {A B : Finset ℕ} (hBA : B ⊆ A)
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    (havoid : ∀ e ∈ edges A, ¬e ⊆ B) :
    IsSidon ((B.image (fun n : ℕ => n^2)) : Set ℕ) := by
  classical
  intro a ha b hb c hc d hd he
  obtain ⟨a,ha',rfl⟩ := mem_image.mp ha
  obtain ⟨b,hb',rfl⟩ := mem_image.mp hb
  obtain ⟨c,hc',rfl⟩ := mem_image.mp hc
  obtain ⟨d,hd',rfl⟩ := mem_image.mp hd
  by_contra hn
  have hmem (x : ℕ) (hx : x ∈ B) : x^2 ∈ A.image (fun n : ℕ => n^2) :=
    mem_image.mpr ⟨x,hBA hx,rfl⟩
  have hdist := APFreeExtraction.four_distinct_of_collision hAP
    (hmem a ha') (hmem c hc') (hmem b hb') (hmem d hd') he hn
  have hac : a ≠ c := fun h => hdist.1 (congrArg (fun n : ℕ => n^2) h)
  have hab : a ≠ b := fun h => hdist.2.1 (congrArg (fun n : ℕ => n^2) h)
  have had : a ≠ d := fun h => hdist.2.2.1 (congrArg (fun n : ℕ => n^2) h)
  have hcb : c ≠ b := fun h => hdist.2.2.2.1 (congrArg (fun n : ℕ => n^2) h)
  have hcd : c ≠ d := fun h => hdist.2.2.2.2.1 (congrArg (fun n : ℕ => n^2) h)
  have hbd : b ≠ d := fun h => hdist.2.2.2.2.2 (congrArg (fun n : ℕ => n^2) h)
  have hsub : ({a,c,b,d} : Finset ℕ) ⊆ B := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  apply havoid {a,c,b,d} _ hsub
  exact mem_filter.mpr ⟨mem_powerset.mpr (hsub.trans hBA),
    by simp [hac,hab,had,hcb,hcd,hbd],a,c,b,d,rfl,he⟩

/-- A finite bound for the actual Sidon maximum, using any progression-free
root carrier inside the given height. -/
theorem carrier_bound {N : ℕ} {A : Finset ℕ} (hAN : A ⊆ Icc 1 N)
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ)) :
    A.card^4 ≤ (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)))^3*
      (6*(edges A).card+A.card) := by
  classical
  obtain ⟨B,hBA,hB,hcard⟩ := CaroTuzaFourUniform.finite_selection A (edges A)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
  have hs := sidon_of_edge_avoidance hBA hAP hB
  have hsub : B.image (fun n : ℕ => n^2) ⊆ (Icc 1 N).image (fun n : ℕ => n^2) :=
    image_subset_image (hBA.trans hAN)
  have hmax : (B.image (fun n : ℕ => n^2)).card ≤
      maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr hsub,hs⟩)
  rw [card_image_of_injective B (Nat.pow_left_injective (by omega : (2:ℕ) ≠ 0))] at hmax
  exact hcard.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hmax 3))

lemma scale_algebra (X L m E M : ℝ) (hX : 0 < X) (hL : 0 < L)
    (hM : 0 ≤ M) (hscale : 1000*L^2 ≤ X)
    (hsize : (1999/2000:ℝ)*X/L ≤ m) (hupper : m ≤ X/L)
    (hE : E ≤ (33/400:ℝ)*X^2/L^3) (hmain : m^4 ≤ M^3*(6*E+m)) :
    (125/64:ℝ)*X^2 ≤ M^3*L := by
  have hsz := (div_le_iff₀ hL).mp hsize
  have hsz4 := pow_le_pow_left₀ (show (0:ℝ) ≤ (1999/2000:ℝ)*X by positivity) hsz 4
  have hmain' := mul_le_mul_of_nonneg_right hmain (pow_nonneg hL.le 4)
  have he := (le_div_iff₀ (pow_pos hL 3)).mp hE
  have hu := (le_div_iff₀ hL).mp hupper
  have hu' := mul_le_mul_of_nonneg_right hu (sq_nonneg L)
  have hscale' := mul_le_mul_of_nonneg_left hscale hX.le
  have hden : (6*E+m)*L^3 ≤ (62/125:ℝ)*X^2 := by
    nlinarith only [he,hu',hscale']
  have hden' := mul_le_mul_of_nonneg_left hden (mul_nonneg (pow_nonneg hM 3) hL.le)
  have hc : (62/125:ℝ)*(125/64) ≤ (1999/2000)^4 := by norm_num
  have hc' := mul_le_mul_of_nonneg_right hc (pow_nonneg hX.le 4)
  apply (mul_le_mul_iff_left₀ (show (0:ℝ) < (62/125)*X^2 by positivity)).mp
  nlinarith only [hsz4,hmain',hden',hc']

lemma real_power_lower (X L M : ℝ) (hX : 0 < X) (hL : 0 < L) (hM : 0 ≤ M)
    (hcube : (125/64:ℝ)*X^2 ≤ M^3*L) :
    (5/4:ℝ)*X/(X*L)^(1/3:ℝ) ≤ M := by
  let R : ℝ := (X*L)^(1/3:ℝ)
  have hR : 0 < R := Real.rpow_pos_of_pos (mul_pos hX hL) _
  have hR3 : R^3=X*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (mul_nonneg hX.le hL.le)]
    norm_num
  change (5/4:ℝ)*X/R ≤ M
  apply le_of_pow_le_pow_left₀ (by omega : (3:ℕ) ≠ 0) hM
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hR 3)).mpr
  rw [hR3]
  have hh := mul_le_mul_of_nonneg_right hcube hX.le
  nlinarith only [hh]

/-- A larger leading constant for the actual Sidon maximum. The factor
`(log N)^(-1/3)` is still present; no new exponent is claimed. -/
theorem eventual_log_lower : ∀ᶠ N : ℕ in atTop,
    (5/4:ℝ)*(N:ℝ)/((N:ℝ)*Real.log N)^(1/3:ℝ) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) : ℝ) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlo := ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
    (show (0:ℝ) < 1/1000 by norm_num)
  filter_upwards [ControlledSquareSampling.logarithmic_sampling (1/2000) (by norm_num),
    hlog.eventually_ge_atTop 1,eventually_ge_atTop 1,hlo] with N hsample hL hN hsmall
  obtain ⟨A,hAN,hAP,hsize,hupper,hE⟩ := hsample
  norm_num at hsize hE
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N:ℝ) := by linarith
  have hsmall' : (Real.log (N:ℝ))^2 ≤ (1/1000:ℝ)*(N:ℝ) := by
    simpa only [Function.comp_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log (N:ℝ))),
      abs_of_nonneg hN0.le] using hsmall
  have hmain : (A.card:ℝ)^4 ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) : ℝ)^3*
        (6*((edges A).card:ℝ)+(A.card:ℝ)) := by exact_mod_cast carrier_bound hAN hAP
  apply real_power_lower (N:ℝ) (Real.log N) _ hN0 hL0 (Nat.cast_nonneg _)
  exact scale_algebra (N:ℝ) (Real.log N) A.card (edges A).card _ hN0 hL0
    (Nat.cast_nonneg _) (by nlinarith only [hsmall']) hsize hupper hE hmain

#print axioms sidon_of_edge_avoidance
#print axioms carrier_bound
#print axioms scale_algebra
#print axioms real_power_lower
#print axioms eventual_log_lower
end Erdos773.PrioritySquareSidonLower
