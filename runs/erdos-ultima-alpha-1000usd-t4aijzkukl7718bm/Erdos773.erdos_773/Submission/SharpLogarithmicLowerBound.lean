import Submission.SquareSupportCounting
import Submission.LowerBound
import Submission.AverageAPBound

/-!
A better leading constant in the actual Sidon lower bound, using unordered
collision supports. The logarithmic loss remains, so this does not establish
the endpoint epsilon = 1/3 or settle Erdős 773.
-/
namespace Erdos773.SharpLogarithmicLowerBound
open Finset Filter SquareCollisionCodegrees
set_option maxHeartbeats 1000000

lemma four_obstructions_bound (N : ℕ) :
    ((sidonObstructions (squaresBelow N)).filter (fun e => e.card=4)).card ≤
      (edges (Icc 1 N)).card := by
  classical
  apply le_trans _ (card_image_le (f := fun R : Finset ℕ => R.image (fun n => n^2))
    (s := edges (Icc 1 N)))
  apply card_le_card_of_injOn (fun e : Finset (squaresBelow N) => e.image Subtype.val)
  · intro e he
    change e ∈ (sidonObstructions (squaresBelow N)).filter (fun e => e.card=4) at he
    obtain ⟨he0,h4⟩ := mem_filter.mp he
    obtain ⟨_,a,b,c,d,rfl,heq,_⟩ := mem_filter.mp he0
    obtain ⟨x,hx,hxa⟩ := mem_image.mp a.property
    obtain ⟨y,hy,hyb⟩ := mem_image.mp b.property
    obtain ⟨z,hz,hzc⟩ := mem_image.mp c.property
    obtain ⟨w,hw,hwd⟩ := mem_image.mp d.property
    let R : Finset ℕ := {x,y,z,w}
    have hvalue : R.image (fun n => n^2) =
        ({a,b,c,d} : Finset (squaresBelow N)).image Subtype.val := by
      simp only [R,image_insert,image_singleton,hxa,hyb,hzc,hwd]
    have hRc : R.card=4 := by
      have hsq : Function.Injective (fun n : ℕ => n^2) := Nat.pow_left_injective (by omega)
      rw [← card_image_of_injective R hsq,hvalue,
        card_image_of_injective _ Subtype.val_injective,h4]
    change ({a,b,c,d} : Finset (squaresBelow N)).image Subtype.val ∈
      (edges (Icc 1 N)).image (fun R : Finset ℕ => R.image (fun n => n^2))
    apply mem_image.mpr
    refine ⟨R,mem_filter.mpr ⟨mem_powerset.mpr ?_,hRc,x,z,y,w,?_,?_⟩,hvalue⟩
    · intro n hn
      simp only [R,mem_insert,mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> assumption
    · ext n
      simp only [R,mem_insert,mem_singleton]
      tauto
    · simpa only [hxa,hyb,hzc,hwd] using heq
  · exact (image_injective Subtype.val_injective).injOn

/-- Ordinary alteration, but with each four-root support counted only once. -/
theorem sharp_alteration (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p*N-p^3*(squareAPs N).card-p^4*(edges (Icc 1 N)).card ≤
      (maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  have hm := sidon_alteration_bound (squaresBelow N) p hp hp1
  rw [squaresBelow_card,obstruction_weight_sum] at hm
  have h3 : (((sidonObstructions (squaresBelow N)).filter (fun e => e.card=3)).card : ℝ) ≤
      (squareAPs N).card := by exact_mod_cast square_obstructions_three_bound N
  have h4 : (((sidonObstructions (squaresBelow N)).filter (fun e => e.card=4)).card : ℝ) ≤
      (edges (Icc 1 N)).card := by exact_mod_cast four_obstructions_bound N
  have h3' := mul_le_mul_of_nonneg_left h3 (pow_nonneg hp 3)
  have h4' := mul_le_mul_of_nonneg_left h4 (pow_nonneg hp 4)
  linarith

lemma finite_log_lower (N : ℕ) (hN : 8000000000 ≤ N) (hlog : 2 ≤ Real.log (N:ℝ))
    (hE : ((edges (Icc 1 N)).card : ℝ) ≤ (1/12:ℝ)*(N:ℝ)^2*Real.log N) :
    (N:ℝ)/((N:ℝ)*Real.log N)^(1/3:ℝ) ≤
      (maxSidonSubsetCard (squaresBelow N) : ℝ) := by
  have hNlarge : (8000000000:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  let L : ℝ := Real.log N
  have hL : 2 ≤ L := hlog
  have hLu : L ≤ N := by
    have hh := Real.log_le_sub_one_of_pos hN0
    dsimp [L]
    linarith
  let R : ℝ := ((N:ℝ)*L)^(1/3:ℝ)
  have hNL : (1:ℝ) ≤ N*L := by nlinarith
  have hR1 : 1 ≤ R := Real.one_le_rpow hNL (by norm_num)
  have hR : 0 < R := by linarith
  have hR3 : R^3=(N:ℝ)*L := by
    dsimp [R]
    rw [← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ N*L)]
    norm_num
  have hR2 : 2 ≤ R := by
    apply le_of_pow_le_pow_left₀ (by omega : (3:ℕ) ≠ 0) hR.le
    nlinarith only [hR3,hL,hNlarge]
  have hRu : R ≤ (N:ℝ)/2000 := by
    apply le_of_pow_le_pow_left₀ (by omega : (3:ℕ) ≠ 0) (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hLu hN0.le
    have h2 := mul_le_mul_of_nonneg_right hNlarge (sq_nonneg (N:ℝ))
    nlinarith only [hR3,h1,h2]
  have hAP : ((squareAPs N).card : ℝ) ≤ 24*R^3 := by
    have hb := AverageAP.squareAPs_log_bound N
    have hl4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    norm_num at hl4
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hN0.ne'] at hb
    have hh : 1+Real.log 4+Real.log N ≤ 3*L := by dsimp [L] at hL ⊢; linarith
    have hmul := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 8*N by positivity)
    rw [hR3]
    nlinarith only [hb,hmul]
  have hE' : ((edges (Icc 1 N)).card : ℝ) ≤ (1/12:ℝ)*N*R^3 := by
    rw [hR3]
    dsimp [L]
    nlinarith only [hE]
  let p : ℝ := 3/(2*R)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hpr : p*R=3/2 := by dsimp [p]; field_simp
  have hpN : 3000 ≤ p*N := by
    have hh := mul_le_mul_of_nonneg_left hRu hp
    nlinarith only [hh,hpr]
  have h3 : p^3*(squareAPs N).card ≤ 81 := by
    calc
      _ ≤ p^3*(24*R^3) := mul_le_mul_of_nonneg_left hAP (pow_nonneg hp _)
      _ = 24*(p*R)^3 := by ring
      _ = 81 := by rw [hpr]; norm_num
  have h4 : p^4*(edges (Icc 1 N)).card ≤ (9/32:ℝ)*p*N := by
    calc
      _ ≤ p^4*((1/12:ℝ)*N*R^3) := mul_le_mul_of_nonneg_left hE' (pow_nonneg hp _)
      _ = (1/12:ℝ)*p*N*(p*R)^3 := by ring
      _ = _ := by rw [hpr]; ring
  have hb := sharp_alteration N p hp hp1
  have ht : (N:ℝ)/R=(2/3)*p*N := by dsimp [p]; ring
  change (N:ℝ)/R ≤ _
  rw [ht]
  nlinarith only [hb,h3,h4,hpN]

/-- The leading factor 1/8 in the previous logarithmic lower bound is
removed. A factor `(log N)^(1/3)` is still lost, so the endpoint remains open. -/
theorem eventual_log_lower :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)/((N:ℝ)*Real.log N)^(1/3:ℝ) ≤
      (maxSidonSubsetCard
        ((Icc 1 N).image (fun n : ℕ => n^2)) : ℝ) := by
  have ht : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [SquareSupportCounting.edges_eventually_small_constant,
    eventually_ge_atTop 8000000000,ht.eventually_ge_atTop 2] with N hE hN hlog
  apply finite_log_lower N hN hlog
  have hlog0 : 0 ≤ Real.log (N:ℝ) := by linarith
  have hh := mul_nonneg (sq_nonneg (N:ℝ)) hlog0
  nlinarith only [hE,hh]

#print axioms four_obstructions_bound
#print axioms sharp_alteration
#print axioms finite_log_lower
#print axioms eventual_log_lower
end Erdos773.SharpLogarithmicLowerBound
