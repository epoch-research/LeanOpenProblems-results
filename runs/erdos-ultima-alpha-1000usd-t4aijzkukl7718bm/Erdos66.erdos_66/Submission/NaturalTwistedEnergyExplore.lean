import Submission.TwistedEnergyExplore

/-! An alternating-convolution energy bound on the natural half-line. -/
namespace Erdos66NaturalTwistedEnergy
open Erdos66TwistedEnergy Erdos66MixedEnergy Erdos66AutocorrelationStability
  Erdos66ResidueSeries Erdos66Generating Erdos66WeightedPushEnergy
  Erdos66WeightedSquareStability
open scoped Classical Topology
open Filter AdditiveCombinatorics
set_option maxHeartbeats 2200000

lemma weighted_alt (f : ℕ → ℝ) (r : ℝ) :
    alt (fun n ↦ f n*r^n)=(fun n ↦ alt f n*r^n) := by
  funext n
  simp only [alt,mul_assoc]

lemma push_weighted_conv (m : ℕ) [NeZero m] {f g : ℕ → ℝ} {r : ℝ}
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n)) (z : ZMod m) :
    conv (push m (fun n ↦ f n*r^n)) (push m (fun n ↦ g n*r^n)) z=
      push m (fun n ↦ sumConv f g n*r^n) z := by
  rw [push_convolution m hf hg]
  congr 1
  exact funext (weighted_convolution f g r)

lemma push_weighted_twist (m : ℕ) [NeZero m] (hm : Even m) {f : ℕ → ℝ} {r : ℝ}
    (hf : Summable (fun n ↦ f n*r^n)) (z : ZMod m) :
    conv (push m (fun n ↦ f n*r^n))
      (fun x ↦ parityChar m x*push m (fun n ↦ f n*r^n) x) z=
      push m (fun n ↦ twistConv f n*r^n) z := by
  have ha : Summable (fun n ↦ alt f n*r^n) := by
    rw [← weighted_alt]
    exact summable_alt hf
  have he : (fun x ↦ parityChar m x*push m (fun n ↦ f n*r^n) x)=
      push m (fun n ↦ alt f n*r^n) := by
    funext x
    rw [← weighted_alt,push_alt m hm]
  rw [he,push_weighted_conv m hf ha]
  rfl

lemma finite_natCast_sum_le (m H : ℕ) [NeZero m] (hm : H< m)
    (u : ZMod m → ℝ) (hu : ∀ z, 0 ≤ u z) :
    (∑ n∈Finset.range (H+1), u (n : ZMod m)) ≤ ∑ z : ZMod m, u z := by
  let S := (Finset.range (H+1)).image (fun n : ℕ ↦ (n : ZMod m))
  have hi : Set.InjOn (fun n : ℕ ↦ (n : ZMod m)) (Finset.range (H+1) : Set ℕ) := by
    intro a ha b hb he
    have ha' : a< m := by have := Finset.mem_range.mp ha; omega
    have hb' : b< m := by have := Finset.mem_range.mp hb; omega
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ha',Nat.mod_eq_of_lt hb']
      using congrArg ZMod.val he
  calc
    _ = ∑ z∈S, u z := (Finset.sum_image (fun a ha b hb he ↦ hi ha hb he)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun z _ _ ↦ hu z)

lemma cyclic_twisted_bound (m : ℕ) [NeZero m] (hm : Even m) {f g : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r<1)
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n))
    (hf2 : Summable (fun n ↦ sumConv f f n^2*r^n))
    (hg2 : Summable (fun n ↦ sumConv g g n^2*r^n))
    (hE : Summable (fun n ↦ (sumConv f f n-sumConv g g n)^2*r^n))
    (htg : Summable (fun n ↦ twistConv g n^2*r^n)) :
    (∑ z : ZMod m, (push m (fun n ↦ twistConv f n*r^n) z)^2) ≤
      (1-r^m)⁻¹*(∑' n, twistConv g n^2*r^n)+
      Real.sqrt (((1-r^m)⁻¹*(∑' n, (sumConv f f n-sumConv g g n)^2*r^n))*
        (2*((1-r^m)⁻¹*(∑' n, sumConv f f n^2*r^n))+
          2*((1-r^m)⁻¹*(∑' n, sumConv g g n^2*r^n)))) := by
  let F := push m (fun n ↦ f n*r^n)
  let G := push m (fun n ↦ g n*r^n)
  let χ := parityChar m
  have hfE : energy F F ≤ (1-r^m)⁻¹*(∑' n, sumConv f f n^2*r^n) := by
    simp only [energy,F,push_weighted_conv m hf hf]
    exact sum_push_sq_le m hr0 hr1 (summable_weighted_convolution hf hf) hf2
  have hgE : energy G G ≤ (1-r^m)⁻¹*(∑' n, sumConv g g n^2*r^n) := by
    simp only [energy,G,push_weighted_conv m hg hg]
    exact sum_push_sq_le m hr0 hr1 (summable_weighted_convolution hg hg) hg2
  have hD : (∑ z : ZMod m, (conv F F z-conv G G z)^2) ≤
      (1-r^m)⁻¹*(∑' n, (sumConv f f n-sumConv g g n)^2*r^n) := by
    simp only [F,G,push_conv_error m hf hg]
    apply sum_push_sq_le m hr0 hr1 _ hE
    simp only [sub_mul]
    exact (summable_weighted_convolution hf hf).sub (summable_weighted_convolution hg hg)
  have htgE : energy G (fun z ↦ χ z*G z) ≤ (1-r^m)⁻¹*(∑' n, twistConv g n^2*r^n) := by
    simp only [energy,G,χ,push_weighted_twist m hm hg]
    have ha : Summable (fun n ↦ alt g n*r^n) := by
      rw [← weighted_alt]
      exact summable_alt hg
    exact sum_push_sq_le m hr0 hr1 (summable_weighted_convolution hg ha) htg
  have hd := twisted_energy_difference_sq χ F G (parityChar_add m hm) (parityChar_sq m)
  have hb : 2*energy F F+2*energy G G ≤
      2*((1-r^m)⁻¹*(∑' n, sumConv f f n^2*r^n))+
      2*((1-r^m)⁻¹*(∑' n, sumConv g g n^2*r^n)) := by linarith
  have hcap : 0 ≤ (1-r^m)⁻¹*(∑' n, (sumConv f f n-sumConv g g n)^2*r^n) :=
    le_trans (Finset.sum_nonneg (fun z _ ↦ sq_nonneg _)) hD
  have hs := hd.trans (mul_le_mul hD hb
    (by linarith [energy_nonneg F F,energy_nonneg G G]) hcap)
  have hsqrt := Real.le_sqrt_of_sq_le hs
  have hout := add_le_add htgE hsqrt
  rw [← add_sub_assoc,add_sub_cancel_left] at hout
  simpa only [energy,F,χ,push_weighted_twist m hm hf] using hout

/-- The weighted sum of squared alternating convolution coefficients is
bounded by a comparison energy plus a self-convolution error term. -/
theorem natural_twisted_energy_bound {f g : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r<1)
    (hf : Summable (fun n ↦ f n*r^n)) (hg : Summable (fun n ↦ g n*r^n))
    (hf2 : Summable (fun n ↦ sumConv f f n^2*r^n))
    (hg2 : Summable (fun n ↦ sumConv g g n^2*r^n))
    (hE : Summable (fun n ↦ (sumConv f f n-sumConv g g n)^2*r^n))
    (htg : Summable (fun n ↦ twistConv g n^2*r^n)) :
    Summable (fun n ↦ (twistConv f n*r^n)^2) ∧
    (∑' n, (twistConv f n*r^n)^2) ≤
      (∑' n, twistConv g n^2*r^n)+
      Real.sqrt ((∑' n, (sumConv f f n-sumConv g g n)^2*r^n)*
        (2*(∑' n, sumConv f f n^2*r^n)+2*(∑' n, sumConv g g n^2*r^n))) := by
  let B := (∑' n, twistConv g n^2*r^n)+
      Real.sqrt ((∑' n, (sumConv f f n-sumConv g g n)^2*r^n)*
        (2*(∑' n, sumConv f f n^2*r^n)+2*(∑' n, sumConv g g n^2*r^n)))
  have ha : Summable (fun n ↦ alt f n*r^n) := by
    rw [← weighted_alt]
    exact summable_alt hf
  have ht : Summable (fun n ↦ twistConv f n*r^n) := summable_weighted_convolution hf ha
  have hp : Tendsto (fun k : ℕ ↦ (1-r^(2*(k+1)))⁻¹) atTop (𝓝 (1 : ℝ)) := by
    have hi : Tendsto (fun k : ℕ ↦ 2*(k+1)) atTop atTop :=
      tendsto_atTop_mono (fun k ↦ by dsimp; omega) tendsto_id
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp hi).const_sub 1
    simpa only [sub_zero,inv_one] using hh.inv₀ (by norm_num : (1-0 : ℝ)≠0)
  have hpart (H : ℕ) : (∑ n∈Finset.range (H+1), (twistConv f n*r^n)^2) ≤ B := by
    have hl := tendsto_finset_sum (Finset.range (H+1)) (fun n _ ↦ (push_even_tendsto ht n).pow 2)
    have hu := (hp.mul_const (∑' n, twistConv g n^2*r^n)).add
      (((hp.mul_const (∑' n, (sumConv f f n-sumConv g g n)^2*r^n)).mul
        (((hp.mul_const (∑' n, sumConv f f n^2*r^n)).const_mul 2).add
          ((hp.mul_const (∑' n, sumConv g g n^2*r^n)).const_mul 2))).sqrt)
    simp only [one_mul] at hu
    apply le_of_tendsto_of_tendsto hl hu
    filter_upwards [eventually_ge_atTop H] with k hk
    exact (finite_natCast_sum_le (2*(k+1)) H (by omega) _ (fun _ ↦ sq_nonneg _)).trans
      (cyclic_twisted_bound (2*(k+1)) (by exact even_two_mul (k+1)) hr0 hr1 hf hg hf2 hg2 hE htg)
  have hb (S : Finset ℕ) : (∑ n∈S, (twistConv f n*r^n)^2) ≤ B := by
    have hsub : S⊆Finset.range (S.sup id+1) := by
      intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ sq_nonneg _)).trans (hpart _)
  have hs : Summable (fun n ↦ (twistConv f n*r^n)^2) := summable_of_sum_le (fun _ ↦ sq_nonneg _) hb
  refine ⟨hs,?_⟩
  exact le_of_tendsto hs.hasSum (Eventually.of_forall hb)

end Erdos66NaturalTwistedEnergy
